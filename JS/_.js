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
// "off"                 -> original token-index/rule-index path only.
// "ann_first"           -> ANN-selected axioms first, then deterministic fallback.
// "ann_ranked_fallback" -> deterministic fallback candidates, ranked by ANN preference.
// "ann_only"            -> ANN-selected axioms only; fastest, but may miss proofs.
const _annDispatchMode = "off"; // "off", "ann_first", "ann_ranked_fallback", "ann_only" //

// Other ANN default configs.
const _annHiddenSize = 128;
const _annLearningRate = 0.03;
const _annSeed = 42;
const _bidirectionalFastForwardFlag = true;

// Hot-loop diagnostics. Keep false for benchmarking.
const _debugProofHistoryFlag = false;

// Predict both rewrite directions when ANN mode is enabled.
// 0 => expansion-preference context
// 1 => reduction-preference context
const _annPredictionDirections = [0, 1];

// Maximum contiguous expression window used for ANN axiom-address prediction.
const _annMaxWindowLength = 12;

// Prediction-cache cap. Prevents unbounded Map growth during large searches.
const _annPredictionCacheLimit = 4096;

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

let _tokenStore = null;

class TokenStore {
    constructor() {
        this.tokenToId = new Map();
        this.idToToken = [];
        this.patternIds = new Set();
    }

    intern(rawToken) {
        const token = String(rawToken);
        let id = this.tokenToId.get(token);

        if (id !== undefined) return id;

        id = this.idToToken.length;
        this.tokenToId.set(token, id);
        this.idToToken.push(token);

        if (token.startsWith('?')) {
            this.patternIds.add(id);
        }

        return id;
    }

    encodeTokens(text) {
        const tokens = String(text).match(/\S+/g) || [];
        return tokens.map(token => this.intern(token));
    }

    decode(id) {
        if (typeof id === 'number') {
            return this.idToToken[id] ?? String(id);
        }

        return String(id);
    }

    exprToString(expr) {
        return expr.map(token => this.decode(token)).join(' ');
    }

    isPatternId(token) {
        return typeof token === 'number'
            ? this.patternIds.has(token)
            : String(token).startsWith('?');
    }
}

function tokenText(token) {
    return _tokenStore ? _tokenStore.decode(token) : String(token);
}

function exprToString(expr) {
    return _tokenStore ? _tokenStore.exprToString(expr) : expr.join(' ');
}

function isPatternToken(token) {
    return _tokenStore
        ? _tokenStore.isPatternId(token)
        : String(token).startsWith('?');
}

function normalizeAxiomToken(token) {
    const text = tokenText(token);
    return text && text.startsWith('?') ? '?VAR' : text;
}

function stableHashString(s) {
    let h = 2166136261;

    for (let i = 0; i < s.length; i++) {
        h ^= s.charCodeAt(i);
        h = Math.imul(h, 16777619);
    }

    return (h >>> 0).toString(16);
}

function getRequiredAddressBits(n) {
    if (typeof requiredAddressBits === 'function') {
        return requiredAddressBits(n);
    }

    return Math.max(1, Math.ceil(Math.log2(Math.max(1, n))));
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
            annAddressBits: getRequiredAddressBits(Math.max(1, axioms.length)),
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
            annMode: _annDispatchMode
        };
    }

    addRuntimeSample(expr, axiomIndex, direction = 0) {
        if (!Number.isInteger(axiomIndex)) return;
        if (axiomIndex < 0 || axiomIndex >= this.axioms.length) return;
        if (!this.ann) return;

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

        if (typeof AxiomAddressANN !== 'function') {
            console.warn('AxiomAddressANN is not available; ANN dispatch disabled.');
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

        return `ANN_AXIOM_SELECTOR_V4:${h}:${this.compiler.inputSize}:${this.hiddenSize}:${this.axioms.length}`;
    }

    _loadCachedModel() {
        try {
            if (typeof localStorage === 'undefined') return null;
            if (typeof AxiomAddressANN !== 'function') return null;

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

        predictWindow(expr);

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

    rankRules(expr, fallbackRules) {
        const predicted = this.getPredictedAxioms(expr);

        if (!this.ann) {
            return fallbackRules;
        }

        const fallbackAxiomSet = new Set(
            fallbackRules.map(rule => rule.nnIndex)
        );

        let hit = false;

        for (const axiom of predicted) {
            const key = axiom.nnIndex ?? axiom.axiomID;

            if (fallbackAxiomSet.has(key)) {
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

        if (!hit && fallbackRules.length > 0) {
            this.stats.annFallbackUsefulHits++;
        }

        if (_annDispatchMode === "ann_only") {
            const predictedSet = new Set(predicted.map(axiom => axiom.nnIndex));
            return fallbackRules.filter(rule => predictedSet.has(rule.nnIndex));
        }

        if (_annDispatchMode === "ann_ranked_fallback") {
            const rank = new Map();

            for (let i = 0; i < predicted.length; i++) {
                const key = predicted[i].nnIndex ?? predicted[i].axiomID;

                if (!rank.has(key)) {
                    rank.set(key, i);
                }
            }

            return fallbackRules
                .map((rule, originalIndex) => ({
                    rule,
                    originalIndex,
                    rank: rank.has(rule.nnIndex)
                        ? rank.get(rule.nnIndex)
                        : Number.POSITIVE_INFINITY
                }))
                .sort((a, b) => {
                    if (a.rank !== b.rank) return a.rank - b.rank;
                    return a.originalIndex - b.originalIndex;
                })
                .map(item => item.rule);
        }

        if (_annDispatchMode === "ann_first") {
            const predictedSet = new Set(predicted.map(axiom => axiom.nnIndex));
            const first = [];
            const rest = [];

            for (const rule of fallbackRules) {
                if (predictedSet.has(rule.nnIndex)) {
                    first.push(rule);
                } else {
                    rest.push(rule);
                }
            }

            return [...first, ...rest];
        }

        return fallbackRules;
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
}

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
const _canonicalFormFlag = false;

// Binary Heap implementation for O(log n) operations.
class BinaryHeap {
    constructor(compareFn) {
        this.items = [];
        this.compare = compareFn || ((a, b) => a.priority - b.priority);
    }
    
    enqueue(element, priority) {
        this.items.push({element, priority});
        this._bubbleUp(this.items.length - 1);
    }
    
    dequeue() {
        if (this.isEmpty()) return undefined;
        
        const result = this.items[0];
        const end = this.items.pop();
        
        if (this.items.length > 0) {
            this.items[0] = end;
            this._bubbleDown(0);
        }
        
        return result?.element;
    }

    peekPriority() {
        return this.items[0]?.priority ?? Number.POSITIVE_INFINITY;
    }
    
    isEmpty() {
        return this.items.length === 0;
    }
    
    size() {
        return this.items.length;
    }
    
    _bubbleUp(idx) {
        const element = this.items[idx];
        
        while (idx > 0) {
            const parentIdx = Math.floor((idx - 1) / 2);
            const parent = this.items[parentIdx];
            
            if (this.compare(element, parent) >= 0) break;
            
            this.items[idx] = parent;
            idx = parentIdx;
        }
        
        this.items[idx] = element;
    }
    
    _bubbleDown(idx) {
        const element = this.items[idx];
        const length = this.items.length;
        
        while (true) {
            const leftChildIdx = 2 * idx + 1;
            const rightChildIdx = 2 * idx + 2;
            let swap = -1;
            
            if (leftChildIdx < length) {
                const leftChild = this.items[leftChildIdx];
                if (this.compare(leftChild, element) < 0) {
                    swap = leftChildIdx;
                }
            }
            
            if (rightChildIdx < length) {
                const rightChild = this.items[rightChildIdx];
                const leftForCompare = swap === -1 ? element : this.items[leftChildIdx];

                if (this.compare(rightChild, leftForCompare) < 0) {
                    swap = rightChildIdx;
                }
            }
            
            if (swap === -1) break;
            
            this.items[idx] = this.items[swap];
            idx = swap;
        }
        
        this.items[idx] = element;
    }
}

function canonicalize(expr) {
    // Simple canonicalization: sort sequences of additions.
    const result = [...expr];
    const plusToken = _tokenStore?.tokenToId.get('+');

    if (plusToken === undefined) return result;
    
    for (let i = 0; i < result.length; i++) {
        if (result[i] === plusToken && i > 0 && i < result.length - 1) {
            const terms = [];
            let start = i - 1;
            
            while (start > 0 && result[start - 1] === plusToken) {
                start -= 2;
            }
            
            for (let j = start; j < result.length; j += 2) {
                if (j >= result.length || (j > start && result[j - 1] !== plusToken)) break;
                terms.push(result[j]);
            }
            
            terms.sort((a, b) => a - b);
            
            let k = 0;
            for (let j = start; j < result.length && k < terms.length; j += 2) {
                if (j >= result.length || (j > start && result[j - 1] !== plusToken)) break;
                result[j] = terms[k++];
            }
        }
    }
    
    return result;
}

function exprKey(expr) {
    return expr.join(' ');
}

function findPatternAnchor(tokens) {
    for (let i = 0; i < tokens.length; i++) {
        if (!isPatternToken(tokens[i])) {
            return {
                token: tokens[i],
                offset: i
            };
        }
    }

    return null;
}

function compileRewriteRules(axioms) {
    const rules = [];
    let ruleOrdinal = 0;

    const addRule = (axiom, axiomIndex, from, to, orientation) => {
        const anchor = findPatternAnchor(from);

        rules.push({
            // Unique rule identity. Do not derive this only from axiomID.
            ruleID: `rule_${ruleOrdinal++}`,

            axiomID: axiom.axiomID,
            guidZ: axiom.guidZ,
            nnIndex: axiomIndex,

            from,
            to,
            fromLen: from.length,
            toLen: to.length,
            firstToken: from[0],
            hasPattern: from.some(isPatternToken),
            anchorToken: anchor?.token ?? null,
            anchorOffset: anchor?.offset ?? -1,
            direction: to.length > from.length ? 'expand' : 'reduce',

            // Optional trace metadata.
            orientation,
            sourceLine: axiom.sourceLine,
            sourcePair: axiom.sourcePair
        });
    };

    for (let i = 0; i < axioms.length; i++) {
        const axiom = axioms[i];
        axiom.nnIndex = i;

        const [a, b] = axiom.subnets;

        if (Array.isArray(a) && Array.isArray(b)) {
            addRule(axiom, i, a, b, 0);
            addRule(axiom, i, b, a, 1);
        }
    }

    return rules;
}

class RewriteRuleIndex {
    constructor(rules) {
        this.literalFirstTokenToRules = new Map();
        this.patternAnchorToRules = new Map();
        this.floatingPatternRules = [];

        for (const rule of rules) {
            this.addRule(rule);
        }
    }

    _addToMap(map, key, rule) {
        if (!map.has(key)) {
            map.set(key, []);
        }

        map.get(key).push(rule);
    }

    addRule(rule) {
        if (rule.hasPattern) {
            if (rule.anchorToken !== null) {
                this._addToMap(this.patternAnchorToRules, rule.anchorToken, rule);
            } else {
                this.floatingPatternRules.push(rule);
            }

            return;
        }

        this._addToMap(this.literalFirstTokenToRules, rule.firstToken, rule);
    }

    getRelevantRules(positionIndex) {
        const relevant = [];
        const seen = new Set();

        const addRules = (rules) => {
            if (!rules) return;

            for (const rule of rules) {
                if (seen.has(rule.ruleID)) continue;

                seen.add(rule.ruleID);
                relevant.push(rule);
            }
        };

        for (const token of positionIndex.keys()) {
            addRules(this.literalFirstTokenToRules.get(token));
            addRules(this.patternAnchorToRules.get(token));
        }

        addRules(this.floatingPatternRules);

        return relevant;
    }
}

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

function buildPositionIndex(expr) {
    const index = new Map();

    for (let i = 0; i < expr.length; i++) {
        const token = expr[i];
        let positions = index.get(token);

        if (!positions) {
            positions = [];
            index.set(token, positions);
        }

        positions.push(i);
    }

    return index;
}

function arraysMatchAt(expr, pattern, position) {
    if (!Array.isArray(expr) || !Array.isArray(pattern)) return false;
    if (position < 0 || position + pattern.length > expr.length) return false;

    for (let i = 0; i < pattern.length; i++) {
        if (expr[position + i] !== pattern[i]) return false;
    }

    return true;
}

function matchPatternAt(pattern, expr, position, bindings = null) {
    if (position < 0 || position + pattern.length > expr.length) return null;

    const out = bindings ? new Map(bindings) : new Map();

    for (let j = 0; j < pattern.length; j++) {
        const patternToken = pattern[j];
        const exprToken = expr[position + j];
        
        if (isPatternToken(patternToken)) {
            if (out.has(patternToken)) {
                if (out.get(patternToken) !== exprToken) {
                    return null;
                }
            } else {
                out.set(patternToken, exprToken);
            }
        } else if (patternToken !== exprToken) {
            return null;
        }
    }

    return {
        position,
        bindings: out
    };
}

function applySubstitution(pattern, bindings) {
    return pattern.map(token => {
        if (isPatternToken(token) && bindings.has(token)) {
            return bindings.get(token);
        }

        return token;
    });
}

function replaceAt(expr, from, to, position) {
    return [
        ...expr.slice(0, position),
        ...to,
        ...expr.slice(position + from.length)
    ];
}

function replaceAllAtPositions(expr, from, to, positions) {
    if (!positions || positions.length === 0) return false;

    const result = [...expr];
    let changed = false;

    for (let i = positions.length - 1; i >= 0; i--) {
        const position = positions[i];

        if (arraysMatchAt(result, from, position)) {
            result.splice(position, from.length, ...to);
            changed = true;
        }
    }

    return changed ? result : false;
}

function* matchRuleOccurrences(expr, rule, positionIndex) {
    // Preserve the original branching semantics:
    // - literal rules yield first occurrence replacement;
    // - literal rules also yield all-occurrences replacement when useful;
    // - pattern rules yield first legal match only.
    // The speedup comes from using token-position anchors instead of scanning the
    // whole expression for every directed rule.
    if (!rule.hasPattern) {
        const candidatePositions = positionIndex.get(rule.firstToken) || [];
        const matches = [];

        for (const position of candidatePositions) {
            if (arraysMatchAt(expr, rule.from, position)) {
                matches.push(position);
            }
        }

        if (matches.length > 0) {
            yield {
                position: matches[0],
                to: rule.to,
                method: 'first'
            };
        }

        if (matches.length > 1) {
            const resultExpr = replaceAllAtPositions(expr, rule.from, rule.to, matches);

            if (resultExpr) {
                yield {
                    position: -1,
                    to: rule.to,
                    method: 'all',
                    resultExpr
                };
            }
        }

        return;
    }

    if (rule.anchorToken !== null) {
        const anchorPositions = positionIndex.get(rule.anchorToken) || [];

        for (const anchorPosition of anchorPositions) {
            const start = anchorPosition - rule.anchorOffset;
            const match = matchPatternAt(rule.from, expr, start);

            if (!match) continue;

            yield {
                position: match.position,
                to: applySubstitution(rule.to, match.bindings),
                method: 'pattern'
            };

            return;
        }

        return;
    }

    for (let position = 0; position <= expr.length - rule.fromLen; position++) {
        const match = matchPatternAt(rule.from, expr, position);

        if (!match) continue;

        yield {
            position: match.position,
            to: applySubstitution(rule.to, match.bindings),
            method: 'pattern'
        };

        return;
    }
}

let heuristicCache;
let rewriteRuleIndex;
let annDispatcher;
let proofHistory = [];

function solveProblem() {
    const { axioms, proofStatement } = parseInput(_input.value);
    const startTime = performance.now();

    heuristicCache = new HeuristicCache();
    proofHistory = [];

    const rewriteRules = compileRewriteRules(axioms);
    rewriteRuleIndex = new RewriteRuleIndex(rewriteRules);

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
        Search depth: ${result.stats.maxDepth}<br>
        Strategy: ${result.stats.strategy}<br>
        Token count: ${result.stats.tokenCount}<br>
        Directed rewrite rules: ${result.stats.rewriteRuleCount}<br>
        Position-index builds: ${result.stats.positionIndexBuilds}<br>
        Rule match attempts: ${result.stats.ruleMatchAttempts}<br>
        Rewrite candidates yielded: ${result.stats.rewriteCandidatesYielded}<br>
        Debug proof history: ${_debugProofHistoryFlag ? 'on' : 'off'}<br>
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
        Final proof steps: ${result.stats.proofSteps}<br>
        Debug history records: ${proofHistory.length}
    `;

    if (
        annDispatcher &&
        result.proof.includes("Proof Found!") &&
        annDispatcher.runtimeSamples?.length > 0
    ) {
        annDispatcher.trainReplaySamples();
    }

    if (!result.proof.includes("Proof Found!") && _debugProofHistoryFlag && proofHistory.length > 0) {
        _output.value += "\n\n=== Partial Proof History ===\n";

        for (const step of proofHistory) {
            _output.value += `${step.from} => ${step.to} (via ${step.rule})\n`;
        }
    }
}

function parseInput(input) {
    _tokenStore = new TokenStore();

    const lines = input
        .split('\n')
        .filter(line => line.trim() && !line.trim().startsWith('//'));

    const axiomMap = new Map();
    let globalAxiomOrdinal = 0;

    lines.slice().forEach((line, k) => {
        const parts = line
            .split(/[~<]?=+[>]?/g)
            .map(s => s.trim())
            .filter(Boolean);

        let linePairOrdinal = 0;

        parts.forEach((part, i) => {
            parts.slice(i + 1).forEach(otherPart => {
                const left = _tokenStore.encodeTokens(part);
                const right = _tokenStore.encodeTokens(otherPart);
                const key = `${left.join(' ')}=${right.join(' ')}`;

                if (!axiomMap.has(key)) {
                    axiomMap.set(key, {
                        subnets: [left, right],

                        // Unique display/source ID per expanded pair.
                        axiomID: `axiom_${k + 1}.${linePairOrdinal}`,

                        // Unique internal ordinal. Use this for rule identity.
                        guidZ: globalAxiomOrdinal,

                        // Optional trace metadata.
                        sourceLine: k + 1,
                        sourcePair: linePairOrdinal
                    });

                    globalAxiomOrdinal++;
                }

                linePairOrdinal++;
            });
        });
    });

    const sortedAxioms = Array.from(axiomMap.values()).map(axiom => {
        axiom.subnets = axiom.subnets
            .sort((a, b) => b.length - a.length);
        return axiom;
    });

    const proofStatement = sortedAxioms[sortedAxioms.length - 1];

    return {
        axioms: sortedAxioms.slice(0, -1),
        proofStatement
    };
}

function generateProofOptimized(axioms, proofStatement) {
    const [lhs, rhs] = proofStatement.subnets;
    const lhsStr = exprToString(lhs);
    const rhsStr = exprToString(rhs);

    let iterations = 0;
    const maxIterations = 10000;
    
    const stats = {
        statesExplored: 0,
        uniqueStates: 0,
        queueOps: 0,
        maxDepth: 0,
        strategy: _currentSearchStrategy.description,

        tokenCount: _tokenStore?.idToToken.length ?? 0,
        rewriteRuleCount: axioms.length * 2,
        positionIndexBuilds: 0,
        ruleMatchAttempts: 0,
        rewriteCandidatesYielded: 0,
        proofSteps: 0,

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
        fastForwardHits: 0
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

    if (lhsStr === rhsStr) {
        stats.proofSteps = 1;

        return {
            proof: "Proof Found!\n\n" + lhsStr + " = " + rhsStr + ", trivial\n\nQ.E.D.",
            stats
        };
    }

    function heuristic(expr1, expr2) {
        const cached = heuristicCache.get(expr1, expr2);
        if (cached !== undefined) return cached;
        
        const arr1 = expr1;
        const arr2 = expr2;
        let h = 0;
        
        h += Math.abs(arr1.length - arr2.length) * 2;
        
        const tokens1 = new Set(arr1);
        const tokens2 = new Set(arr2);
        let commonCount = 0;

        for (const token of tokens1) {
            if (tokens2.has(token)) commonCount++;
        }

        h += (tokens1.size + tokens2.size - 2 * commonCount);
        
        const minLen = Math.min(arr1.length, arr2.length);
        for (let i = 0; i < minLen; i++) {
            if (arr1[i] !== arr2[i]) h += 1;
        }
        
        heuristicCache.set(expr1, expr2, h);
        return h;
    }

    class SearchState {
        constructor(expr, parent, rule, side, depth = 0, searchStrategy = _currentSearchStrategy.config) {
            this.expr = expr;
            this.parent = parent;
            this.rule = rule || 'start';
            this.side = side;
            this.depth = depth;
            this.searchStrategy = searchStrategy;

            this.canonicalExpr = _canonicalFormFlag ? canonicalize(expr) : expr;
            this.canonicalStr = exprKey(this.canonicalExpr);
            this.exprStr = exprToString(expr);
        }
        
        getPriority(targetExpr) {
            const g = this.depth;
            const h = heuristic(this.canonicalExpr, targetExpr);
            return ((this.searchStrategy == 'a*') || ((this.searchStrategy == 'adaptive') && (iterations > (maxIterations * .1))) ? g : 0) + h;
        }
    }

    function unwindPath(state) {
        const path = [];

        while (state) {
            path.push({
                expr: state.expr,
                rule: state.rule || 'start'
            });

            state = state.parent;
        }

        return path.reverse();
    }

    function constructProof(lhsState_, rhsState_) {
        let proof = "Proof Found!\n\n";

        const lhsState = lhsState_.side == "lhs" ? lhsState_ : rhsState_;
        const rhsState = lhsState_.side == "lhs" ? rhsState_ : lhsState_;
        const lhsPath = unwindPath(lhsState);
        const rhsPath = unwindPath(rhsState);
        
        const rhsStart = exprToString(rhsPath[0].expr);

        for (let i = 0; i < lhsPath.length; i++) {
            const step = lhsPath[i];
            proof += `${exprToString(step.expr)} = ${rhsStart}`;

            if (step.rule !== 'start') {
                proof += `, via ${step.rule} (lhs)`;
            }

            proof += '\n';
        }
        
        const lhsEnd = exprToString(lhsPath[lhsPath.length - 1].expr);

        for (let i = 1; i < rhsPath.length; i++) {
            const step = rhsPath[i];
            proof += `${lhsEnd} = ${exprToString(step.expr)}, via ${step.rule} (rhs)\n`;
        }
        
        proof += "\nQ.E.D.";
        stats.proofSteps = Math.max(0, lhsPath.length + rhsPath.length - 1);
        return proof;
    }

    const lhsQueue = new BinaryHeap();
    const rhsQueue = new BinaryHeap();
    const lhsVisited = new Map();
    const rhsVisited = new Map();
    
    const lhsStart = new SearchState(lhs, null, 'start', 'lhs');
    const rhsStart = new SearchState(rhs, null, 'start', 'rhs');
    
    lhsQueue.enqueue(lhsStart, lhsStart.getPriority(rhs));
    rhsQueue.enqueue(rhsStart, rhsStart.getPriority(lhs));
    lhsVisited.set(lhsStart.canonicalStr, lhsStart);
    rhsVisited.set(rhsStart.canonicalStr, rhsStart);

    function meetState(candidateState, oppositeVisited) {
        if (!_bidirectionalFastForwardFlag) return null;

        stats.meetChecks++;

        const oppositeState = oppositeVisited.get(candidateState.canonicalStr);

        if (oppositeState) {
            stats.fastForwardHits++;
            return constructProof(candidateState, oppositeState);
        }

        return null;
    }

    function* generateRewrites(expr, side) {
        const positionIndex = buildPositionIndex(expr);
        stats.positionIndexBuilds++;

        let relevantRules = rewriteRuleIndex.getRelevantRules(positionIndex);
        stats.annFallbackScans++;

        if (annDispatcher) {
            annDispatcher.stats.annFallbackScans++;
            relevantRules = annDispatcher.rankRules(expr, relevantRules);
        }

        syncAnnStats();

        for (const rule of relevantRules) {
            stats.ruleMatchAttempts++;

            for (const occurrence of matchRuleOccurrences(expr, rule, positionIndex)) {
                const resultExpr = occurrence.resultExpr || replaceAt(expr, rule.from, occurrence.to, occurrence.position);
                stats.rewriteCandidatesYielded++;

                if (annDispatcher && Number.isInteger(rule.nnIndex)) {
                    annDispatcher.addRuntimeSample(
                        expr,
                        rule.nnIndex,
                        rule.direction === 'expand' ? 0 : 1
                    );
                }

                yield {
                    expr: resultExpr,
                    axiom: rule.axiomID,
                    direction: rule.direction,
                    method: occurrence.method,
                    position: occurrence.position
                };
            }
        }
    }

    while (!lhsQueue.isEmpty() || !rhsQueue.isEmpty()) {
        if (iterations++ > maxIterations) break;
        
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
            
            if (otherVisited.has(current.canonicalStr)) {
                const otherState = otherVisited.get(current.canonicalStr);
                return {
                    proof: constructProof(current, otherState),
                    stats: syncAnnStats()
                };
            }
            
            for (const rewrite of generateRewrites(current.expr, side)) {
                const newState = new SearchState(
                    rewrite.expr,
                    current,
                    `${rewrite.axiom} (${rewrite.direction})`,
                    side,
                    current.depth + 1
                );
                
                if (_debugProofHistoryFlag) {
                    proofHistory.push({
                        from: current.exprStr,
                        to: newState.exprStr,
                        rule: `${rewrite.axiom} (${rewrite.direction})`
                    });
                }
                
                const previous = visited.get(newState.canonicalStr);

                if (previous && previous.depth <= newState.depth) {
                    continue;
                }

                const proof = meetState(newState, otherVisited);

                if (proof) {
                    return {
                        proof,
                        stats: syncAnnStats()
                    };
                }

                visited.set(newState.canonicalStr, newState);
                queue.enqueue(newState, newState.getPriority(targetExpr));
                stats.queueOps++;
                stats.uniqueStates = visited.size + otherVisited.size;
            }
        }
    }
    
    return {
        proof: "No proof found within search limits.",
        stats: syncAnnStats()
    };
}

// Legacy replacement functions retained for quick A/B testing and compatibility.
function tryReplace(arr, from, to, method) {
    if (from.length > arr.length) return false;
    
    if (method === 'A') {
        for (let i = 0; i <= arr.length - from.length; i++) {
            if (arraysMatchAt(arr, from, i)) {
                return replaceAt(arr, from, to, i);
            }
        }
    } else if (method === 'B') {
        let result = [...arr];
        let changed = false;
        
        for (let i = result.length - from.length; i >= 0; i--) {
            if (arraysMatchAt(result, from, i)) {
                result.splice(i, from.length, ...to);
                changed = true;
            }
        }
        
        return changed ? result : false;
    }
    
    return false;
}

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

// JavaScript: Persist textarea contents using localStorage.
document.addEventListener('DOMContentLoaded', () => {
    const textarea = _input;

    const savedText = JSON.parse(localStorage.getItem('lastProof'));
    if (savedText !== null) {
        textarea.value = savedText;
    }

    textarea.addEventListener('input', () => {
        localStorage.setItem('lastProof', JSON.stringify(textarea.value, ' ', 2));
    });

    updateLineNumbers();
});

// Initialize with example including pattern variables.
_input.value = `// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Pattern variable example
nat { ?x } = nat_range { 1 }
nat_range { ?n } = nat_range { ?n + 1 }

// Prove
1 + 2 + 1 = 4`;

updateLineNumbers();