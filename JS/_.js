/**
 * Usage:
 * 
 * Input:
 * 1 + 1 = 2
 * 2 = 2 = 4
 * Prove 1 + 1 + 1 + 1 = 4
 * 
 * Output:
 * 1 + 1 + 1 + 1 = 4, root
 * 2 + 1 + 1 = 4, via axiom 0 LHS reduce
 * 2 + 2 = 4, via axiom 0 LHS reduce
 * 2 + 2 = 2 + 2, via axiom 1 RHS expand
 * Q.E.D.
 * 
 */

// ANN axiom-address dispatch configuration.
// "off"                 -> original token-index path only.
// "ann_first"           -> ANN-selected axioms first, then deterministic fallback.
// "ann_ranked_fallback" -> deterministic fallback candidates, ranked by ANN preference.
// "ann_only"            -> ANN-selected axioms only; fastest, but may miss proofs.
const _annDispatchMode = "off"; // "off", "ann_first", "ann_ranked_fallback", "ann_only" //

// Other ANN default configs
const _annHiddenSize = 128;
const _annLearningRate = 0.03;
const _annSeed = 42;
const _bidirectionalFastForwardFlag = true;

// Predict both rewrite directions:
// 0 => expansion-preference context
// 1 => reduction-preference context
const _annPredictionDirections = [0, 1];

// Maximum contiguous expression window used for ANN axiom-address prediction.
const _annMaxWindowLength = 12;

// Prediction-cache cap. Prevents unbounded Map growth during large searches.
const _annPredictionCacheLimit = 4096;

// Add prover-side ANN helper functions (Place after your existing utility functions, or before BinaryHeap.)
function normalizeAxiomToken(token) {
    return token && token.startsWith('?') ? '?VAR' : token;
}

function stableHashString(s) {
    let h = 2166136261;

    for (let i = 0; i < s.length; i++) {
        h ^= s.charCodeAt(i);
        h = Math.imul(h, 16777619);
    }

    return (h >>> 0).toString(16);
}

function chooseAnnEpochs(sampleCount, axiomCount) {
    if (axiomCount > 50000) return 2;
    if (axiomCount > 10000) return 4;
    if (axiomCount > 1000) return 24;
    if (sampleCount > 5000) return 64;
    return 256;
}

// ANN feature-compiler. This pre-parses all axiom/proof tokens and computes the correct ANN.inputSize param.

class AxiomFeatureCompiler {
    constructor(axioms, proofStatement) {
        this.vocab = [];
        this.tokenToIndex = new Map();
        this.maxSubnetLength = 1;

        this._buildVocabulary(axioms, proofStatement);

        this.directionOffset = this.vocab.length;
        this.lengthOffset = this.directionOffset + 1;
        this.uniqueOffset = this.directionOffset + 2;
        this.patternOffset = this.directionOffset + 3;

        this.inputSize = this.vocab.length + 4;
    }

    _addToken(token) {
        const key = normalizeAxiomToken(token);

        if (!this.tokenToIndex.has(key)) {
            this.tokenToIndex.set(key, this.vocab.length);
            this.vocab.push(key);
        }
    }

    _scanSubnet(subnet) {
        if (!Array.isArray(subnet)) return;

        this.maxSubnetLength = Math.max(this.maxSubnetLength, subnet.length);

        for (const token of subnet) {
            this._addToken(token);
        }
    }

    _buildVocabulary(axioms, proofStatement) {
        for (const axiom of axioms) {
            for (const subnet of axiom.subnets) {
                this._scanSubnet(subnet);
            }
        }

        if (proofStatement) {
            for (const subnet of proofStatement.subnets) {
                this._scanSubnet(subnet);
            }
        }
    }

    encode(tokens, direction = 0) {
        const t = new Float32Array(this.inputSize);
        const unique = new Set();
        let hasPattern = 0;

        for (const rawToken of tokens) {
            const token = normalizeAxiomToken(rawToken);
            const idx = this.tokenToIndex.get(token);

            if (idx !== undefined) {
                t[idx] += 1;
                unique.add(idx);
            }

            if (token === '?VAR') {
                hasPattern = 1;
            }
        }

        t[this.directionOffset] = direction;
        t[this.lengthOffset] = tokens.length;
        t[this.uniqueOffset] = unique.size;
        t[this.patternOffset] = hasPattern;

        return t;
    }

    fingerprint() {
        return stableHashString(
            this.vocab.join('\u001f') +
            `|${this.inputSize}|${this.maxSubnetLength}`
        );
    }
}

// ANN Dispatcher

class NeuralAxiomDispatcher {
    constructor({ axioms, proofStatement, hiddenSize, learningRate, seed }) {
        this.axioms = axioms;
        this.compiler = new AxiomFeatureCompiler(axioms, proofStatement);

        this.hiddenSize = hiddenSize;
        this.learningRate = learningRate;
        this.seed = seed;

        this.ann = null;
        this.lastLoss = null;
        this.trainingMs = 0;
        this.predictionCache = new Map();

        this.stats = {
            annInputSize: this.compiler.inputSize,
            annAddressBits: requiredAddressBits(Math.max(1, axioms.length)),
            annDispatchHits: 0,
            annDispatchMisses: 0,
            annFallbackUsefulHits: 0,
            annReplaySamples: 0,
            annTrainingSamples: 0,
            annTrainingEpochs: 0,
            annTrainingMs: 0,
            annPredictions: 0,
            annValidPredictions: 0,
            annCacheHits: 0,
            annFallbackScans: 0,
            openQueueMode: _openQueueMode,
            branchRankMode: _branchRankMode,
            branchAnnPredictions: 0,
            branchAnnTrainingSamples: 0,
            annMode: _annDispatchMode
        };
    }

    addRuntimeSample(expr, axiomIndex, direction = 0) {
        if (!Number.isInteger(axiomIndex)) return;
        if (axiomIndex < 0 || axiomIndex >= this.axioms.length) return;

        this.runtimeSamples ??= [];
        this.runtimeSampleKeys ??= new Set();

        const key = `${expr.join(' ')}|${direction}|${axiomIndex}`;

        if (this.runtimeSampleKeys.has(key)) return;

        this.runtimeSampleKeys.add(key);

        this.runtimeSamples.push({
            t: this.compiler.encode(expr, direction),
            i: axiomIndex
        });

        this.stats.annReplaySamples = this.runtimeSamples.length;
    }

    build() {
        if (_annDispatchMode === "off" || this.axioms.length === 0) {
            return this;
        }

        for (let i = 0; i < this.axioms.length; i++) {
            this.axioms[i].nnIndex = i;
        }

        const samples = this._buildTrainingSamples();

        this.stats.annTrainingSamples = samples.length;
        this.stats.annTrainingEpochs = chooseAnnEpochs(
            samples.length,
            this.axioms.length
        );

        this.ann = this._loadCachedModel();

        if (this.ann) {
            return this;
        }

        const t0 = performance.now();

        this.ann = new AxiomAddressANN({
            inputSize: this.compiler.inputSize,
            hiddenSize: this.hiddenSize,
            axiomCount: this.axioms.length,
            learningRate: this.learningRate,
            seed: this.seed
        });

        this.lastLoss = this.ann.train(samples, {
            epochs: this.stats.annTrainingEpochs,
            shuffle: true
        });

        this.trainingMs = performance.now() - t0;
        this.stats.annTrainingMs = this.trainingMs;

        this._saveCachedModel();

        return this;
    }

    _buildTrainingSamples() {
        const samples = [];
        const sampleKeys = new Set();

        const addSample = (tokens, axiomIndex, direction) => {
            if (!Array.isArray(tokens) || tokens.length === 0) return;

            const key = `${axiomIndex}|${direction}|${tokens.join(' ')}`;

            if (sampleKeys.has(key)) return;

            sampleKeys.add(key);

            samples.push({
                t: this.compiler.encode(tokens, direction),
                i: axiomIndex
            });
        };

        const addWindowSamples = (tokens, axiomIndex, direction) => {
            if (!Array.isArray(tokens) || tokens.length === 0) return;

            const maxWindow = Math.min(
                _annMaxWindowLength,
                this.compiler.maxSubnetLength,
                tokens.length
            );

            for (let len = 1; len <= maxWindow; len++) {
                for (let start = 0; start <= tokens.length - len; start++) {
                    addSample(tokens.slice(start, start + len), axiomIndex, direction);
                }
            }
        };

        for (let i = 0; i < this.axioms.length; i++) {
            const axiom = this.axioms[i];
            const [a, b] = axiom.subnets;

            // Train both orientations because parseInput sorts subnet length,
            // while proof search may use either subnet as the active rewrite source.
            if (Array.isArray(a)) {
                addSample(a, i, 0);
                addSample(a, i, 1);
                addWindowSamples(a, i, 0);
                addWindowSamples(a, i, 1);
            }

            if (Array.isArray(b)) {
                addSample(b, i, 0);
                addSample(b, i, 1);
                addWindowSamples(b, i, 0);
                addWindowSamples(b, i, 1);
            }

            // Context sample: helps the ANN associate both sides with the same address.
            if (Array.isArray(a) && Array.isArray(b)) {
                const joined = [...a, ...b];

                addSample(joined, i, 0);
                addSample(joined, i, 1);
                addWindowSamples(joined, i, 0);
                addWindowSamples(joined, i, 1);
            }
        }

        return samples;
    }

    _cacheKey() {
        const axiomSignature = this.axioms
            .map(ax => ax.subnets.map(s => s.join(' ')).join('='))
            .join('\n');

        const h = stableHashString(
            axiomSignature +
            this.compiler.fingerprint()
        );

        return `ANN_AXIOM_SELECTOR_V3:${h}:${this.compiler.inputSize}:${this.hiddenSize}:${this.axioms.length}`;
    }

    _loadCachedModel() {
        try {
            if (typeof localStorage === 'undefined') return null;

            const raw = localStorage.getItem(this._cacheKey());
            if (!raw) return null;

            const data = JSON.parse(raw);

            if (
                data.inputSize !== this.compiler.inputSize ||
                data.hiddenSize !== this.hiddenSize ||
                data.axiomCount !== this.axioms.length
            ) {
                return null;
            }

            return AxiomAddressANN.fromJSON(data);
        } catch (_) {
            return null;
        }
    }

    _saveCachedModel() {
        try {
            if (typeof localStorage === 'undefined' || !this.ann) return;

            localStorage.setItem(
                this._cacheKey(),
                JSON.stringify(this.ann.toJSON())
            );
        } catch (_) {
            // localStorage quota can be exceeded for large vocabularies.
            // Keep the in-memory model and continue.
        }
    }

    getPredictedAxioms(expr) {
        if (!this.ann || this.axioms.length === 0) {
            return [];
        }

        const key = expr.join(' ');
        const cached = this.predictionCache.get(key);

        if (cached) {
            this.stats.annCacheHits++;
            return cached;
        }

        const selected = new Map();
        const seenWindows = new Set();

        const maxWindow = Math.min(
            _annMaxWindowLength,
            this.compiler.maxSubnetLength,
            expr.length
        );

        const recordPrediction = (prediction) => {
            this.stats.annPredictions++;

            if (!prediction.valid) return;

            this.stats.annValidPredictions++;

            const axiom = this.axioms[prediction.i];

            if (axiom && !selected.has(prediction.i)) {
                selected.set(prediction.i, axiom);
            }
        };

        const predictWindow = (tokens) => {
            for (const direction of _annPredictionDirections) {
                const windowKey = `${direction}|${tokens.join(' ')}`;

                if (seenWindows.has(windowKey)) continue;

                seenWindows.add(windowKey);

                recordPrediction(
                    this.ann.predictAddress(
                        this.compiler.encode(tokens, direction)
                    )
                );
            }
        };

        // Whole expression.
        predictWindow(expr);

        // Contiguous windows.
        for (let len = 1; len <= maxWindow; len++) {
            for (let start = 0; start <= expr.length - len; start++) {
                predictWindow(expr.slice(start, start + len));
            }
        }

        const result = Array.from(selected.values());

        if (this.predictionCache.size > _annPredictionCacheLimit) {
            this.predictionCache.clear();
        }

        this.predictionCache.set(key, result);

        return result;
    }

    mergePredictedWithFallback(expr, fallbackAxioms) {
        const predicted = this.getPredictedAxioms(expr);

        const fallbackSet = new Set(
            fallbackAxioms.map(ax => ax.nnIndex ?? ax.axiomID)
        );

        let hit = false;

        for (const axiom of predicted) {
            const key = axiom.nnIndex ?? axiom.axiomID;

            if (fallbackSet.has(key)) {
                hit = true;
                break;
            }
        }

        if (predicted.length > 0) {
            if (hit) {
                this.stats.annDispatchHits++;
            } else {
                this.stats.annDispatchMisses++;
            }
        }

        if (!hit && fallbackAxioms.length > 0) {
            this.stats.annFallbackUsefulHits++;
        }

        if (_annDispatchMode === "ann_only") {
            return predicted;
        }

        if (_annDispatchMode === "ann_ranked_fallback") {
            const rank = new Map();

            for (let i = 0; i < predicted.length; i++) {
                const key = predicted[i].nnIndex ?? predicted[i].axiomID;

                if (!rank.has(key)) {
                    rank.set(key, i);
                }
            }

            return fallbackAxioms
                .map((axiom, originalIndex) => ({
                    axiom,
                    originalIndex,
                    rank: rank.has(axiom.nnIndex ?? axiom.axiomID)
                        ? rank.get(axiom.nnIndex ?? axiom.axiomID)
                        : Number.POSITIVE_INFINITY
                }))
                .sort((a, b) => {
                    if (a.rank !== b.rank) return a.rank - b.rank;
                    return a.originalIndex - b.originalIndex;
                })
                .map(item => item.axiom);
        }

        const merged = [];
        const seen = new Set();

        for (const axiom of predicted) {
            const key = axiom.nnIndex ?? axiom.axiomID;

            if (!seen.has(key)) {
                seen.add(key);
                merged.push(axiom);
            }
        }

        for (const axiom of fallbackAxioms) {
            const key = axiom.nnIndex ?? axiom.axiomID;

            if (!seen.has(key)) {
                seen.add(key);
                merged.push(axiom);
            }
        }

        return merged;
    }

    trainReplaySamples() {
        if (!this.ann) return;
        if (!this.runtimeSamples || this.runtimeSamples.length === 0) return;

        const epochs = Math.min(
            64,
            Math.max(8, Math.ceil(512 / this.runtimeSamples.length))
        );

        this.ann.train(this.runtimeSamples, {
            epochs,
            shuffle: true
        });

        this._saveCachedModel();
    }

} // end class

// MAIN //

let _input = document.getElementById('input');
let _output = document.getElementById('output');
let _lineNumbers = document.getElementById('line-numbers');
let _stats = document.getElementById('stats');

const _searchStrategy = { 
    option : {
        _astar: { config: 'a*', description:'A* with heuristic.' },
        _greedy: { config: 'greedy', description:'BFS (Greedy) - only use heuristic (h), not depth (g).' },
        _adaptive: { config: 'adaptive', description:'Adaptive combination of BFS (Greedy) with A* for higher iterations.' },
    }
}

const _currentSearchStrategy = _searchStrategy.option._astar; // _astar,_greedy,_adaptive //
const _canonicalFormFlag = false; // Add ANN dispatch configuration. fast! Only finds approximate solutions.

// Rewrite candidate selection configuration.
// "deterministic" -> original legal rewrite order.
// "matrix_beam"  -> rank legal rewrites by tally-shaped matrix residual before enqueue.
const _rewriteCandidateMode = "matrix_beam"; // "deterministic", "matrix_beam" //
const _matrixBeamWidth = 16;
const _matrixAllowWorsening = 4;
const _matrixNorm = "l1"; // "l1", "l2" //
const _matrixIncludeAllOccurrencesCandidate = true;

// OPEN queue: A*-safe score inversion plus ANN tie-ranking.
const _openQueueMode = "bucket_astar"; // "bucket_astar", "ann_tie_astar"
const _priorityMaxF = 65535;

// Critical performance switch.
// "off"         -> no ANN prediction/training in the OPEN queue hot path.
// "predict_tie" -> ANN predicts tie-order only; no online training.
const _branchRankMode = "off";

const _branchTieBuckets = _branchRankMode === "off" ? 1 : 16;
const _branchRankHiddenSize = 8;
const _branchRankLearningRate = 0.02;

function seededRand(seed) {
    let s = seed >>> 0;

    return function() {
        s ^= s << 13;
        s ^= s >>> 17;
        s ^= s << 5;
        return (s >>> 0) / 4294967296;
    };
}

function sigmoid(x) {
    if (x < -40) return 0;
    if (x > 40) return 1;
    return 1 / (1 + Math.exp(-x));
}

// Tiny ANN used only as an A*-safe tie-ranker inside equal f buckets.
class BranchRankANN {
    constructor(inputSize = 8, hiddenSize = 8, learningRate = 0.02, seed = 777) {
        this.inputSize = inputSize;
        this.hiddenSize = hiddenSize;
        this.learningRate = learningRate;
        this.wIH = new Float32Array(inputSize * hiddenSize);
        this.bH = new Float32Array(hiddenSize);
        this.wHO = new Float32Array(hiddenSize);
        this.h = new Float32Array(hiddenSize);
        this.bO = 0;

        const rand = seededRand(seed);
        for (let i = 0; i < this.wIH.length; i++) this.wIH[i] = (rand() * 2 - 1) / Math.sqrt(inputSize);
        for (let i = 0; i < this.wHO.length; i++) this.wHO[i] = (rand() * 2 - 1) / Math.sqrt(hiddenSize);
    }

    predict01(x) {
        for (let j = 0; j < this.hiddenSize; j++) {
            let sum = this.bH[j], base = j * this.inputSize;
            for (let i = 0; i < this.inputSize; i++) sum += (x[i] || 0) * this.wIH[base + i];
            this.h[j] = Math.tanh(sum);
        }

        let out = this.bO;
        for (let j = 0; j < this.hiddenSize; j++) out += this.h[j] * this.wHO[j];
        return sigmoid(out);
    }

    bucket(x, bucketCount) {
        return Math.max(0, Math.min(bucketCount - 1, Math.floor(this.predict01(x) * bucketCount)));
    }

    train(x, target) {
        target = Math.max(0, Math.min(1, target));
        const y = this.predict01(x);
        const dO = (target - y) * y * (1 - y);

        for (let j = 0; j < this.hiddenSize; j++) {
            const old = this.wHO[j];
            this.wHO[j] += this.learningRate * dO * this.h[j];

            const dH = dO * old * (1 - this.h[j] * this.h[j]);
            const base = j * this.inputSize;

            for (let i = 0; i < this.inputSize; i++) {
                this.wIH[base + i] += this.learningRate * dH * (x[i] || 0);
            }

            this.bH[j] += this.learningRate * dH;
        }

        this.bO += this.learningRate * dO;
    }
}

// Direct-address priority stack. Higher integer priority pops first.
// A* compatibility: priority = (MAX_F - f) * tieBuckets + annTie.
class AnnPriorityStack {
    constructor(maxF = 65535, tieBuckets = 16, ann = null) {
        this.maxF = maxF;
        this.tieBuckets = tieBuckets;
        this.ann = ann;
        this.maxPriority = (maxF + 1) * tieBuckets - 1;

        this.top = new Int32Array(this.maxPriority + 1).fill(-1);
        this.count = new Int32Array(this.maxPriority + 1);

        this.id = [];
        this.element = [];
        this.priority = [];
        this.prev = [];
        this.next = [];
        this.free = [];
        this.byId = new Map();

        this.levels = [];
        this._buildLevels(this.maxPriority + 1);

        this.seq = 0;
        this.predictions = 0;
        this.trainingSamples = 0;
    }

    _buildLevels(n) {
        for (let words = Math.ceil(n / 32); ; words = Math.ceil(words / 32)) {
            this.levels.push(new Uint32Array(words));
            if (words <= 1) break;
        }
    }

    _set(p) {
        let idx = p >>> 5;
        this.levels[0][idx] |= 1 << (p & 31);

        for (let l = 1; l < this.levels.length; l++) {
            const parent = idx >>> 5;
            this.levels[l][parent] |= 1 << (idx & 31);
            idx = parent;
        }
    }

    _clear(p) {
        if (this.count[p] !== 0) return;

        let idx = p >>> 5;
        this.levels[0][idx] &= ~(1 << (p & 31));

        for (let l = 1; l < this.levels.length; l++) {
            if (this.levels[l - 1][idx] !== 0) break;

            const parent = idx >>> 5;
            this.levels[l][parent] &= ~(1 << (idx & 31));
            idx = parent;
        }
    }

    _highest() {
        let idx = 0;

        for (let l = this.levels.length - 1; l >= 0; l--) {
            const word = this.levels[l][idx];
            if (word === 0) return -1;
            idx = (idx << 5) + 31 - Math.clz32(word);
        }

        return idx <= this.maxPriority ? idx : -1;
    }

    _makePriority(f, features = null, target = undefined) {
        const fQ = Math.max(0, Math.min(this.maxF, Math.round(f)));
        let tie = 0;

        if (
            this.ann &&
            features &&
            (_branchRankMode === "predict_tie" || _branchRankMode === "online_train")
        ) {
            tie = this.ann.bucket(features, this.tieBuckets);
            this.predictions++;

            // Preserve target support, but keep training out of the hot path by default.
            if (_branchRankMode === "online_train" && target !== undefined) {
                this.ann.train(features, target);
                this.trainingSamples++;
            }
        }

        return (this.maxF - fQ) * this.tieBuckets + tie;
    }

    enqueue(element, f, features = null, target = undefined) {
        const id = element.queueId || `${element.side}:${element.canonicalStr}:${this.seq++}`;
        const p = this._makePriority(f, features, target);

        if (this.byId.has(id)) return this.update(id, element, f, features);

        const n = this.free.length ? this.free.pop() : this.element.length;
        const oldTop = this.top[p];

        this.id[n] = id;
        this.element[n] = element;
        this.priority[n] = p;
        this.prev[n] = -1;
        this.next[n] = oldTop;

        if (oldTop !== -1) this.prev[oldTop] = n;

        this.top[p] = n;
        this.count[p]++;
        this.byId.set(id, n);
        this._set(p);
    }

    update(id, element, f, features = null) {
        this.remove(id);
        element.queueId = id;
        this.enqueue(element, f, features);
    }

    remove(id) {
        const n = this.byId.get(id);
        if (n === undefined) return null;

        const p = this.priority[n];

        if (this.prev[n] !== -1) this.next[this.prev[n]] = this.next[n];
        else this.top[p] = this.next[n];

        if (this.next[n] !== -1) this.prev[this.next[n]] = this.prev[n];

        this.count[p]--;
        this._clear(p);
        this.byId.delete(id);

        const out = this.element[n];
        this.element[n] = null;
        this.free.push(n);

        return out;
    }

    dequeue() {
        const p = this._highest();
        if (p < 0) return undefined;
        return this.remove(this.id[this.top[p]]);
    }

    isEmpty() {
        return this._highest() < 0;
    }

    size() {
        return this.byId.size;
    }
}

function normRankValue(x, scale = 16) {
    return Math.tanh((x || 0) / scale);
}

function makeBranchRankFeatures(rewrite, stateDepth) {
    return new Float32Array([
        normRankValue(rewrite.matrixScore),
        normRankValue(rewrite.matrixImprovement),
        normRankValue(rewrite.matrixOldScore),
        Math.min(1, rewrite.length / 64),
        Math.min(1, stateDepth / 128),
        rewrite.direction === 'expand' ? 1 : 0,
        rewrite.method === 'all' ? 1 : 0,
        rewrite.side === 'rhs' ? 1 : 0
    ]);
}

function branchRankTarget(rewrite) {
    const base = Math.max(1, Math.abs(rewrite.matrixOldScore || 0));
    return Math.max(0, Math.min(1, 0.5 + (rewrite.matrixImprovement || 0) / (2 * base)));
}

// Token index for fast axiom matching
class AxiomIndex {
    constructor() {
        this.tokenToAxioms = new Map();
        this.patternAxioms = [];
    }
    
    addAxiom(axiom) {
        const hasPattern = axiom.subnets.some(subnet => 
            subnet.some(token => token.includes('?'))
        );
        
        if (hasPattern) {
            this.patternAxioms.push(axiom);
        } else {
            // Index by first token of each subnet
            for (const subnet of axiom.subnets) {
                if (subnet.length > 0) {
                    const token = subnet[0];
                    if (!this.tokenToAxioms.has(token)) {
                        this.tokenToAxioms.set(token, []);
                    }
                    this.tokenToAxioms.get(token).push(axiom);
                }
            }
        }
    }
    
    getRelevantAxioms(expr) {
        const relevantAxioms = new Set();
        
        // Get axioms matching any token in the expression
        for (const token of expr) {
            if (this.tokenToAxioms.has(token)) {
                for (const axiom of this.tokenToAxioms.get(token)) {
                    relevantAxioms.add(axiom);
                }
            }
        }
        
        // Always include pattern axioms
        for (const axiom of this.patternAxioms) {
            relevantAxioms.add(axiom);
        }
        
        return Array.from(relevantAxioms);
    }
}

// Heuristic cache
class HeuristicCache {
    constructor() {
        this.cache = new Map();
    }
    
    getKey(expr1, expr2) {
        return `${expr1.join(' ')}|||${expr2.join(' ')}`;
    }
    
    get(expr1, expr2) {
        return this.cache.get(this.getKey(expr1, expr2));
    }
    
    set(expr1, expr2, value) {
        this.cache.set(this.getKey(expr1, expr2), value);
    }
}

// Pattern matching with variables
function matchPattern(pattern, expr, bindings = {}) {
    if (pattern.length > expr.length) return null;
    
    const newBindings = {...bindings};
    
    for (let i = 0; i <= expr.length - pattern.length; i++) {
        let match = true;
        const tempBindings = {...newBindings};
        
        for (let j = 0; j < pattern.length; j++) {
            const patternToken = pattern[j];
            const exprToken = expr[i + j];
            
            if (patternToken.startsWith('?')) {
                // Pattern variable
                if (tempBindings[patternToken]) {
                    if (tempBindings[patternToken] !== exprToken) {
                        match = false;
                        break;
                    }
                } else {
                    tempBindings[patternToken] = exprToken;
                }
            } else if (patternToken !== exprToken) {
                match = false;
                break;
            }
        }
        
        if (match) {
            return {
                position: i,
                bindings: tempBindings
            };
        }
    }
    
    return null;
}

// Apply pattern substitution
function applySubstitution(pattern, bindings) {
    return pattern.map(token => {
        if (token.startsWith('?') && bindings[token]) {
            return bindings[token];
        }
        return token;
    });
}

// Canonicalization for commutative operations
function canonicalize(expr) {
    // Simple canonicalization: sort sequences of additions
    const result = [...expr];
    
    // Find + operators and sort their operands
    for (let i = 0; i < result.length; i++) {
        if (result[i] === '+' && i > 0 && i < result.length - 1) {
            // Collect all terms in this addition chain
            const terms = [];
            let start = i - 1;
            
            // Go backwards to find start
            while (start > 0 && result[start - 1] === '+') {
                start -= 2;
            }
            
            // Collect all terms
            for (let j = start; j < result.length; j += 2) {
                if (j >= result.length || (j > start && result[j - 1] !== '+')) break;
                terms.push(result[j]);
            }
            
            // Sort terms
            terms.sort();
            
            // Replace in result
            let k = 0;
            for (let j = start; j < result.length && k < terms.length; j += 2) {
                if (j >= result.length || (j > start && result[j - 1] !== '+')) break;
                result[j] = terms[k++];
            }
        }
    }
    
    return result;
}

// Sparse tally vector helpers. A tally is a plain object: { token: count }.
// A delta has the same structure, but values may be negative.
function makeTally(tokens) {
    const tally = Object.create(null);

    if (!Array.isArray(tokens)) return tally;

    for (const token of tokens) {
        const key = normalizeAxiomToken(token);
        tally[key] = (tally[key] || 0) + 1;
    }

    return tally;
}

function cloneTally(tally) {
    const out = Object.create(null);

    for (const key in tally) {
        out[key] = tally[key];
    }

    return out;
}

function addTallyValue(out, key, value) {
    const next = (out[key] || 0) + value;

    if (next === 0) {
        delete out[key];
    } else {
        out[key] = next;
    }
}

function subtractTallies(left, right) {
    const out = Object.create(null);

    for (const key in left) {
        addTallyValue(out, key, left[key]);
    }

    for (const key in right) {
        addTallyValue(out, key, -right[key]);
    }

    return out;
}

function deltaTally(from, to) {
    // Directed rewrite delta: tally(to) - tally(from).
    // The result deliberately preserves the same sparse object shape as makeTally().
    return subtractTallies(makeTally(to), makeTally(from));
}

function applyTallyDelta(tally, delta) {
    const out = cloneTally(tally);

    for (const key in delta) {
        addTallyValue(out, key, delta[key]);
    }

    return out;
}

function tallyNorm(tally, norm = _matrixNorm) {
    let score = 0;

    for (const key in tally) {
        const value = tally[key];
        score += norm === "l2" ? value * value : Math.abs(value);
    }

    return score;
}

function scoreMatrixCandidate(side, currentTally, targetTally, delta) {
    const oldResidual = side === "lhs"
        ? subtractTallies(currentTally, targetTally)
        : subtractTallies(targetTally, currentTally);

    const nextCurrentTally = applyTallyDelta(currentTally, delta);

    const newResidual = side === "lhs"
        ? subtractTallies(nextCurrentTally, targetTally)
        : subtractTallies(targetTally, nextCurrentTally);

    const oldScore = tallyNorm(oldResidual);
    const score = tallyNorm(newResidual);

    return {
        score,
        oldScore,
        improvement: oldScore - score,
        residual: newResidual,
        delta
    };
}

function arraysMatchAt(expr, pattern, position) {
    if (!Array.isArray(expr) || !Array.isArray(pattern)) return false;
    if (position < 0 || position + pattern.length > expr.length) return false;

    for (let i = 0; i < pattern.length; i++) {
        if (expr[position + i] !== pattern[i]) return false;
    }

    return true;
}

function replaceAt(expr, from, to, position) {
    return [
        ...expr.slice(0, position),
        ...to,
        ...expr.slice(position + from.length)
    ];
}

function replaceAllOccurrences(expr, from, to) {
    let result = [...expr];
    let changed = false;

    for (let i = result.length - from.length; i >= 0; i--) {
        if (arraysMatchAt(result, from, i)) {
            result.splice(i, from.length, ...to);
            changed = true;
        }
    }

    return changed ? result : false;
}

function findLiteralMatches(expr, from) {
    const positions = [];

    if (!Array.isArray(from) || from.length === 0 || from.length > expr.length) {
        return positions;
    }

    for (let i = 0; i <= expr.length - from.length; i++) {
        if (arraysMatchAt(expr, from, i)) {
            positions.push(i);
        }
    }

    return positions;
}

function findPatternMatches(pattern, expr, bindings = {}) {
    const matches = [];

    if (pattern.length > expr.length) return matches;

    for (let i = 0; i <= expr.length - pattern.length; i++) {
        let ok = true;
        const tempBindings = {...bindings};

        for (let j = 0; j < pattern.length; j++) {
            const patternToken = pattern[j];
            const exprToken = expr[i + j];

            if (patternToken.startsWith('?')) {
                if (tempBindings[patternToken]) {
                    if (tempBindings[patternToken] !== exprToken) {
                        ok = false;
                        break;
                    }
                } else {
                    tempBindings[patternToken] = exprToken;
                }
            } else if (patternToken !== exprToken) {
                ok = false;
                break;
            }
        }

        if (ok) {
            matches.push({
                position: i,
                bindings: tempBindings
            });
        }
    }

    return matches;
}

let heuristicCache;
let axiomIndex;
let annDispatcher; // forward declaration //
let proofHistory = [];

function solveProblem() {
    const { axioms, proofStatement } = parseInput(_input.value);
    const startTime = performance.now();

    // Reset global state.
    heuristicCache = new HeuristicCache();
    axiomIndex = new AxiomIndex();
    annDispatcher = null;
    proofHistory = [];

    // Build deterministic token-index fallback.
    for (let i = 0; i < axioms.length; i++) {
        axioms[i].nnIndex = i;
        axiomIndex.addAxiom(axioms[i]);
    }

    // Pre-parse all axiom/proof tokens to compute ANN inputSize,
    // then train/load the compact address predictor.
    annDispatcher = new NeuralAxiomDispatcher({
        axioms,
        proofStatement,
        hiddenSize: _annHiddenSize,
        learningRate: _annLearningRate,
        seed: _annSeed
    }).build();

    const result = generateProofOptimized(axioms, proofStatement);
    const endTime = performance.now();

    _output.value = result.proof;
    _output.value += `\n\nTotal runtime: ${(endTime - startTime).toFixed(4)} ms`;

    _stats.innerHTML = `
        <strong>Search Statistics:</strong><br>
        States explored: ${result.stats.statesExplored}<br>
        Unique states: ${result.stats.uniqueStates}<br>
        Queue operations: ${result.stats.queueOps}<br>
        OPEN queue: ${result.stats.openQueueMode}<br>
        Branch rank mode: ${result.stats.branchRankMode}<br>
        Branch ANN predictions: ${result.stats.branchAnnPredictions}<br>
        Branch ANN training samples: ${result.stats.branchAnnTrainingSamples}<br>
        Search depth: ${result.stats.maxDepth}<br>
        Strategy: ${result.stats.strategy}<br>
        ANN mode: ${result.stats.annMode}<br>
        ANN inputSize: ${result.stats.annInputSize}<br>
        ANN address bits: ${result.stats.annAddressBits}<br>
        ANN dispatch hits: ${result.stats.annDispatchHits}<br>
        ANN dispatch misses: ${result.stats.annDispatchMisses}<br>
        ANN fallback useful hits: ${result.stats.annFallbackUsefulHits}<br>
        ANN replay samples: ${result.stats.annReplaySamples}<br>
        ANN training samples: ${result.stats.annTrainingSamples}<br>
        ANN training epochs: ${result.stats.annTrainingEpochs}<br>
        ANN training time: ${result.stats.annTrainingMs.toFixed(4)} ms<br>
        ANN bitfield predictions: ${result.stats.annPredictions}<br>
        ANN valid bitfield predictions: ${result.stats.annValidPredictions}<br>
        ANN cache hits: ${result.stats.annCacheHits}<br>
        ANN fallback scans: ${result.stats.annFallbackScans}<br>
        Rewrite candidate mode: ${result.stats.rewriteCandidateMode}<br>
        Matrix candidate count: ${result.stats.matrixCandidateCount}<br>
        Matrix yielded count: ${result.stats.matrixYieldCount}<br>
        Matrix pruned count: ${result.stats.matrixPrunedCount}<br>
        Matrix beam width: ${result.stats.matrixBeamWidth}<br>
        Proof steps found: ${proofHistory.length}
    `;

    if (
        annDispatcher &&
        result.proof.includes("Proof Found!") &&
        annDispatcher.runtimeSamples?.length > 0
    ) {
        annDispatcher.trainReplaySamples();
    }

    if (!result.proof.includes("Proof Found!") && proofHistory.length > 0) {
        _output.value += "\n\n=== Partial Proof History ===\n";

        for (const step of proofHistory) {
            _output.value += `${step.from} => ${step.to} (via ${step.rule})\n`;
        }
    }
}

function parseInput(input) {
    let lines = input
        .split('\n')
        .filter(line => line.trim() && !line.startsWith('//'));
    let axiomsSet = new Set();

    lines.slice().forEach((line, k) => {
        // Handle pattern variables in axioms
        const parts = line
            .split(/[~<]?=+[>]?/g)
            .map(s => s.trim());
        parts.forEach((part, i) => {
            parts.slice(i + 1).forEach(otherPart => {
                axiomsSet.add({
                    subnets: `${part} = ${otherPart}`,
                    axiomID: `axiom_${k + 1}.0`,
                    guidZ: k
                });
            });
        });
    });

    const sortedAxioms = Array.from(axiomsSet).map(axiom => {
        axiom.subnets = axiom.subnets
            .split(' = ')
            .sort((a, b) => b.length - a.length) // (lhs/rhs) //
            .map(pair => pair.match(/\S+/g));
        return axiom;
    });

    const proofStatement = sortedAxioms[sortedAxioms.length - 1];
    return {
        axioms: sortedAxioms.slice(0, -1),
        proofStatement: proofStatement
    };
}

function generateProofOptimized(axioms, proofStatement) {
    const [lhs, rhs] = proofStatement.subnets;
    const lhsStr = lhs.join(' ');
    const rhsStr = rhs.join(' ');

    // Main search loop
    let iterations = 0;
    const maxIterations = 10000;
    
    // Statistics tracking
    const stats = {
        statesExplored: 0,
        uniqueStates: 0,
        queueOps: 0,
        maxDepth: 0,
        strategy: _currentSearchStrategy.description,

        annMode: annDispatcher?.stats.annMode ?? "off",
        annInputSize: annDispatcher?.stats.annInputSize ?? 0,
        annAddressBits: annDispatcher?.stats.annAddressBits ?? 0,
        annTrainingSamples: annDispatcher?.stats.annTrainingSamples ?? 0,
        annTrainingEpochs: annDispatcher?.stats.annTrainingEpochs ?? 0,
        annTrainingMs: annDispatcher?.stats.annTrainingMs ?? 0,

        annDispatchHits: annDispatcher?.stats.annDispatchHits ?? 0,
        annDispatchMisses: annDispatcher?.stats.annDispatchMisses ?? 0,
        annFallbackUsefulHits: annDispatcher?.stats.annFallbackUsefulHits ?? 0,
        annReplaySamples: annDispatcher?.stats.annReplaySamples ?? 0,

        annPredictions: annDispatcher?.stats.annPredictions ?? 0,
        annValidPredictions: annDispatcher?.stats.annValidPredictions ?? 0,
        annCacheHits: annDispatcher?.stats.annCacheHits ?? 0,
        annFallbackScans: annDispatcher?.stats.annFallbackScans ?? 0,

        meetChecks: 0,
        fastForwardHits: 0,

        rewriteCandidateMode: _rewriteCandidateMode,
        matrixCandidateCount: 0,
        matrixYieldCount: 0,
        matrixPrunedCount: 0,
        matrixBeamWidth: _matrixBeamWidth
    };

    function syncAnnStats() {
        const s = annDispatcher?.stats;
        if (!s) return stats;

        stats.annMode = s.annMode ?? stats.annMode;
        stats.annInputSize = s.annInputSize ?? stats.annInputSize;
        stats.annAddressBits = s.annAddressBits ?? stats.annAddressBits;
        stats.annTrainingSamples = s.annTrainingSamples ?? stats.annTrainingSamples;
        stats.annTrainingEpochs = s.annTrainingEpochs ?? stats.annTrainingEpochs;
        stats.annTrainingMs = s.annTrainingMs ?? stats.annTrainingMs;

        stats.annDispatchHits = s.annDispatchHits ?? 0;
        stats.annDispatchMisses = s.annDispatchMisses ?? 0;
        stats.annFallbackUsefulHits = s.annFallbackUsefulHits ?? 0;
        stats.annReplaySamples = s.annReplaySamples ?? 0;

        stats.annPredictions = s.annPredictions ?? 0;
        stats.annValidPredictions = s.annValidPredictions ?? 0;
        stats.annCacheHits = s.annCacheHits ?? 0;

        stats.annFallbackScans = Math.max(
            stats.annFallbackScans ?? 0,
            s.annFallbackScans ?? 0
        );

        return stats;
    }

    // If already equal, return immediately
    if (lhsStr === rhsStr) {
        return {
            proof: "Proof Found!\n\n" + lhsStr + " = " + rhsStr + ", trivial\n\nQ.E.D.",
            stats
        };
    }

    // Heuristic function with caching
    function heuristic(expr1, expr2) {
        // Check cache first
        let cached = heuristicCache.get(expr1, expr2);
        if (cached !== undefined) return cached;
        
        const arr1 = [...expr1];
        const arr2 = [...expr2];
        
        // Combine multiple heuristics
        let h = 0;
        
        // Length difference
        h += Math.abs(arr1.length - arr2.length) * 2;
        
        // Token difference
        const tokens1 = new Set(arr1);
        const tokens2 = new Set(arr2);
        const common = new Set([...tokens1].filter(x => tokens2.has(x)));
        h += (tokens1.size + tokens2.size - 2 * common.size);
        
        // Position-based difference
        const minLen = Math.min(arr1.length, arr2.length);
        for (let i = 0; i < minLen; i++) {
            if (arr1[i] !== arr2[i]) h += 1;
        }
        
        // Cache the result
        heuristicCache.set(expr1, expr2, h);
        return h;
    }

    // Unified search state
    class SearchState {
        constructor(expr, path, side, depth = 0, 
                searchStrategy = _currentSearchStrategy.config) {
            this.expr = expr;
            this.canonicalExpr = _canonicalFormFlag 
                ? canonicalize(expr) /* fast! Only finds approximate solutions. */ 
                : expr ;
            this.exprStr = expr.join(' ');
            this.canonicalStr = this.canonicalExpr.join(' ');
            this.path = path;
            this.side = side;
            this.depth = depth;
            this.searchStrategy = searchStrategy;
        }
        
        getPriority(targetExpr) {
            // BFS (Greedy) - only use heuristic, not depth, else
            // A* f(n) = g(n) + h(n)
            const g = this.depth; // Cost so far
            const h = heuristic(this.canonicalExpr, targetExpr); // Heuristic estimate
            return ((this.searchStrategy == 'a*') || ((this.searchStrategy == 'adaptive') && (iterations > (maxIterations * .1))) ? g : 0) + h;
        }
    }

    // Bidirectional BFS search
    const branchRankANN = _branchRankMode === "predict_tie"
        ? new BranchRankANN(
            8,
            _branchRankHiddenSize,
            _branchRankLearningRate,
            _annSeed ^ 0x9e3779b9
        )
        : null;

    const lhsQueue = new AnnPriorityStack(_priorityMaxF, _branchTieBuckets, branchRankANN);
    const rhsQueue = new AnnPriorityStack(_priorityMaxF, _branchTieBuckets, branchRankANN);

    function syncQueueStats() {
        stats.openQueueMode = _openQueueMode;
        stats.branchRankMode = _branchRankMode;
        stats.branchAnnPredictions = lhsQueue.predictions + rhsQueue.predictions;
        stats.branchAnnTrainingSamples = lhsQueue.trainingSamples + rhsQueue.trainingSamples;
        return stats;
    }

    const lhsVisited = new Map();
    const rhsVisited = new Map();
    
    // Initialize with starting states
    const lhsStart = new SearchState(lhs, [{expr: lhs, rule: 'start'}], 'lhs');
    const rhsStart = new SearchState(rhs, [{expr: rhs, rule: 'start'}], 'rhs');
    
    lhsQueue.enqueue(lhsStart, lhsStart.getPriority(rhs));
    rhsQueue.enqueue(rhsStart, rhsStart.getPriority(lhs));
    lhsVisited.set(lhsStart.canonicalStr, lhsStart);
    rhsVisited.set(rhsStart.canonicalStr, rhsStart);

    // Add the bidirectional meet helper
    function meetState(candidateState, ownVisited, oppositeVisited) {
        if (!_bidirectionalFastForwardFlag) return null;

        stats.meetChecks++;

        const oppositeState = oppositeVisited.get(candidateState.canonicalStr);

        if (oppositeState) {
            stats.fastForwardHits++;
            return constructProof(candidateState, oppositeState);
        }

        return null;
    }

    function makeRewriteCandidate(expr, side, axiom, from, to, resultExpr, position, method, targetExpr) {
        const delta = deltaTally(from, to);
        const currentTally = makeTally(expr);
        const targetTally = makeTally(targetExpr);
        const matrix = scoreMatrixCandidate(side, currentTally, targetTally, delta);

        return {
            expr: resultExpr,
            axiom: axiom.axiomID,
            axiomIndex: axiom.nnIndex,
            direction: to.length > from.length ? `expand` : `reduce`,
            side,
            from,
            to,
            position,
            method,
            delta: matrix.delta,
            matrixScore: matrix.score,
            matrixOldScore: matrix.oldScore,
            matrixImprovement: matrix.improvement,
            matrixResidual: matrix.residual,
            length: resultExpr.length
        };
    }

    function collectRewriteCandidates(expr, side, targetExpr, relevantAxioms) {
        const candidates = [];
        const seenResults = new Set();

        const pushCandidate = (candidate) => {
            const key = `${candidate.axiom}|${candidate.direction}|${candidate.method}|${candidate.position}|${candidate.expr.join(' ')}`;

            if (seenResults.has(key)) return;

            seenResults.add(key);
            candidates.push(candidate);
        };

        for (const axiom of relevantAxioms) {
            for (const [from, to] of [
                [axiom.subnets[0], axiom.subnets[1]],
                [axiom.subnets[1], axiom.subnets[0]]
            ]) {
                const hasPattern = from.some(token => token.includes('?'));

                if (!hasPattern) {
                    const positions = findLiteralMatches(expr, from);

                    for (const position of positions) {
                        pushCandidate(
                            makeRewriteCandidate(
                                expr,
                                side,
                                axiom,
                                from,
                                to,
                                replaceAt(expr, from, to, position),
                                position,
                                'single',
                                targetExpr
                            )
                        );
                    }

                    if (_matrixIncludeAllOccurrencesCandidate && positions.length > 1) {
                        const allResult = replaceAllOccurrences(expr, from, to);

                        if (allResult) {
                            // For simultaneous all-occurrence replacement, the delta is effectively multiplied.
                            // Keep the same tally-shaped object representation while scaling each signed count.
                            const candidate = makeRewriteCandidate(
                                expr,
                                side,
                                axiom,
                                from,
                                to,
                                allResult,
                                -1,
                                'all',
                                targetExpr
                            );

                            const scaledDelta = Object.create(null);

                            for (const key in candidate.delta) {
                                scaledDelta[key] = candidate.delta[key] * positions.length;
                            }

                            const matrix = scoreMatrixCandidate(
                                side,
                                makeTally(expr),
                                makeTally(targetExpr),
                                scaledDelta
                            );

                            candidate.delta = matrix.delta;
                            candidate.matrixScore = matrix.score;
                            candidate.matrixOldScore = matrix.oldScore;
                            candidate.matrixImprovement = matrix.improvement;
                            candidate.matrixResidual = matrix.residual;

                            pushCandidate(candidate);
                        }
                    }
                } else {
                    const matches = findPatternMatches(from, expr);

                    for (const match of matches) {
                        const substitutedTo = applySubstitution(to, match.bindings);
                        const resultExpr = [
                            ...expr.slice(0, match.position),
                            ...substitutedTo,
                            ...expr.slice(match.position + from.length)
                        ];

                        pushCandidate(
                            makeRewriteCandidate(
                                expr,
                                side,
                                axiom,
                                from,
                                substitutedTo,
                                resultExpr,
                                match.position,
                                'pattern',
                                targetExpr
                            )
                        );
                    }
                }
            }
        }

        return candidates;
    }

    function rankMatrixCandidates(candidates) {
        if (_rewriteCandidateMode !== "matrix_beam") {
            return candidates;
        }

        stats.matrixCandidateCount += candidates.length;

        if (candidates.length === 0) {
            return candidates;
        }

        const oldScore = candidates[0].matrixOldScore;
        const allowedScore = oldScore + _matrixAllowWorsening;

        const sorted = candidates
            .filter(candidate => candidate.matrixScore <= allowedScore)
            .sort((a, b) => {
                if (a.matrixScore !== b.matrixScore) return a.matrixScore - b.matrixScore;
                if (a.matrixImprovement !== b.matrixImprovement) return b.matrixImprovement - a.matrixImprovement;
                if (a.length !== b.length) return a.length - b.length;
                return String(a.axiom).localeCompare(String(b.axiom));
            });

        const beam = sorted.slice(0, _matrixBeamWidth);

        stats.matrixPrunedCount += Math.max(0, candidates.length - beam.length);
        stats.matrixYieldCount += beam.length;

        return beam;
    }

    // Generate all possible rewrites for an expression.
    // In matrix_beam mode, legal rewrites are ranked using tally-shaped deltas.
    function* generateRewrites(expr, side, targetExpr) {
        let fallbackAxioms = [];

        if (!annDispatcher || _annDispatchMode !== "ann_only") {
            fallbackAxioms = axiomIndex.getRelevantAxioms(expr);
            stats.annFallbackScans++;

            if (annDispatcher) {
                annDispatcher.stats.annFallbackScans++;
            }
        }

        const relevantAxioms = annDispatcher
            ? annDispatcher.mergePredictedWithFallback(expr, fallbackAxioms)
            : fallbackAxioms;

        syncAnnStats();

        stats.annPredictions = annDispatcher?.stats.annPredictions ?? 0;
        stats.annValidPredictions = annDispatcher?.stats.annValidPredictions ?? 0;
        stats.annCacheHits = annDispatcher?.stats.annCacheHits ?? 0;
        stats.annFallbackScans = Math.max(
            stats.annFallbackScans,
            annDispatcher?.stats.annFallbackScans ?? 0
        );

        const candidates = collectRewriteCandidates(expr, side, targetExpr, relevantAxioms);
        const rankedCandidates = rankMatrixCandidates(candidates);

        for (const candidate of rankedCandidates) {
            if (annDispatcher && Number.isInteger(candidate.axiomIndex)) {
                annDispatcher.addRuntimeSample(
                    expr,
                    candidate.axiomIndex,
                    candidate.direction === 'expand' ? 0 : 1
                );
            }

            yield candidate;
        }
    }
    
    while (!lhsQueue.isEmpty() || !rhsQueue.isEmpty()) {
        if (iterations++ > maxIterations) break;
        
        // Alternate between queues for balanced search
        for (const [queue, visited, otherVisited, side, targetExpr] of [
            [lhsQueue, lhsVisited, rhsVisited, 'lhs', rhs],
            [rhsQueue, rhsVisited, lhsVisited, 'rhs', lhs]
        ]) {
            if (queue.isEmpty()) continue;
            
            const current = queue.dequeue();
            if (!current) continue;
            
            stats.statesExplored++;
            stats.queueOps++;
            stats.maxDepth = Math.max(stats.maxDepth, current.depth);
            
            // Check if we've met in the middle (using canonical form)
            if (otherVisited.has(current.canonicalStr)) {
                const otherState = otherVisited.get(current.canonicalStr);
                return {
                    proof: constructProof(current, otherState),
                    stats: syncAnnStats()
                };
            }
            
            // Generate and explore neighbors
            for (const rewrite of generateRewrites(current.expr, side, targetExpr)) {
                const newState = new SearchState(
                    rewrite.expr,
                    [...current.path, {
                        expr: rewrite.expr,
                        rule: `${rewrite.axiom} (${rewrite.direction})`
                    }],
                    side,
                    current.depth + 1
                );
                
                // Record in proof history
                proofHistory.push({
                    from: current.exprStr,
                    to: newState.exprStr,
                    rule: `${rewrite.axiom} (${rewrite.direction})`
                });
                
                // Skip if already visited with shorter path.
                const previous = visited.get(newState.canonicalStr);

                if (previous && previous.depth <= newState.depth) {
                    continue;
                }

                // Fast-forward: if this new state already exists in the opposite frontier,
                // the proof is complete now. Do not wait for heap dequeue.
                const proof = meetState(newState, visited, otherVisited);

                if (proof) {
                    return {
                        proof,
                        stats: syncAnnStats()
                    };
                }

                visited.set(newState.canonicalStr, newState);

                const fScore = newState.getPriority(targetExpr);

                if (_branchRankMode === "predict_tie") {
                    queue.enqueue(
                        newState,
                        fScore,
                        makeBranchRankFeatures(rewrite, newState.depth)
                    );
                } else {
                    queue.enqueue(newState, fScore);
                }

                syncQueueStats();
                stats.queueOps++;

                stats.uniqueStates = visited.size + otherVisited.size;
            }
        }
    }
    
    // No proof found
    return {
        proof: "No proof found within search limits.",
        stats: syncAnnStats()
    };
}

// Construct the final proof from two meeting paths
function constructProof(lhsState_, rhsState_) { /* bug */
    let proof = "Proof Found!\n\n";

    const lhsState = lhsState_.side == "lhs" ? lhsState_ : rhsState_ ;
    const rhsState = lhsState_.side == "lhs" ? rhsState_ : lhsState_ ;
    
    // LHS transformations
    const rhsStart = rhsState.path[0].expr.join(' ');
    for (let i = 0; i < lhsState.path.length; i++) {
        const step = lhsState.path[i];
        proof += `${step.expr.join(' ')} = ${rhsStart}`;
        if (step.rule !== 'start') {
            proof += `, via ${step.rule} (lhs)`;
        } 
        proof += '\n';
    }
    
    // RHS transformations (in reverse)
    const lhsEnd = lhsState.path[lhsState.path.length - 1].expr.join(' ');
    for (let i = 1; i < rhsState.path.length; i++) {
        const step = rhsState.path[i];
        proof += `${lhsEnd} = ${step.expr.join(' ')}, via ${step.rule} (rhs)\n`;
    }
    
    proof += "\nQ.E.D.";
    return proof;
}

// Optimized replacement functions
function tryReplace(arr, from, to, method) {
    if (from.length > arr.length) return false;
    
    if (method === 'A') {
        // First occurrence replacement
        for (let i = 0; i <= arr.length - from.length; i++) {
            let match = true;
            for (let j = 0; j < from.length; j++) {
                if (arr[i + j] !== from[j]) {
                    match = false;
                    break;
                }
            }
            if (match) {
                return [...arr.slice(0, i), ...to, ...arr.slice(i + from.length)];
            }
        }
    } else if (method === 'B') {
        // All occurrences replacement
        let result = [...arr];
        let changed = false;
        
        for (let i = arr.length - from.length; i >= 0; i--) {
            let match = true;
            for (let j = 0; j < from.length; j++) {
                if (result[i + j] !== from[j]) {
                    match = false;
                    break;
                }
            }
            if (match) {
                result.splice(i, from.length, ...to);
                changed = true;
            }
        }
        
        return changed ? result : false;
    }
    
    return false;
}

// UI functions
function updateLineNumbers() {
    const lines = _input.value.split('\n');
    let i = 1;
    _lineNumbers.innerHTML = lines
        .map(u => /^[^\/\t\s\n]+/.test(u) ? i++ : '')
        .join('<br>');
}

_input.addEventListener('keyup', function() {updateLineNumbers();});
_input.addEventListener('scroll', function() {
    _lineNumbers.scrollTop = this.scrollTop;
});

// JavaScript: Persist textarea contents using localStorage
document.addEventListener('DOMContentLoaded', () => {
    const textarea = _input;

    // Load saved value from localStorage if it exists
    const savedText = JSON.parse(localStorage.getItem('lastProof'));
    if (savedText !== null) {
        textarea.value = savedText;
    }

    // Save value to localStorage on _input
    textarea.addEventListener('input', () => {
        localStorage.setItem('lastProof', JSON.stringify(textarea.value, ' ', 2));
    });

    updateLineNumbers();
});

// Initialize with example including pattern variables
_input.value = `// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Pattern variable example
nat { ?x } = nat_range { 1 }
nat_range { ?n } = nat_range { ?n + 1 }

// Prove
1 + 2 + 1 = 4`;

updateLineNumbers();

/** Example Usage */
/* 
const axiomCount = 100_000;

const ann = new AxiomAddressANN({
  inputSize: 4,
  hiddenSize: 64,
  axiomCount,
  learningRate: 0.03,
  seed: 42
});

const samples = [
    // t[+ 1 2 4 ] //
  { t: [1, 2, 0, 0], i: 0 },
  { t: [0, 0, 1, 0], i: 0 },
  { t: [1, 0, 2, 0], i: 1 },
  { t: [0, 0, 0, 1], i: 1 }
];

ann.train(samples, { epochs: 5000 });

// 1 + 1 + 1 + 1
const t = [3, 4, 0, 0];

// 1 + 1 + 1 + 1
//const t = [0, 0, 0, 1];

const result = ann.predictAddress( t );

console.log(result);
*/