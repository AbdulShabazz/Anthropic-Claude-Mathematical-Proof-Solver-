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
 */

// ANN axiom-address dispatch configuration.
// "off"       -> original token-index path only.
// "ann_first" -> ANN-selected axioms first, then deterministic fallback.
// "ann_only"  -> ANN-selected axioms only; fastest, but may miss proofs.
const _annDispatchMode = "ann_only"; // "off", "ann_first", "ann_only" //

// Other ANN default configs
const _annHiddenSize = 64;
const _annLearningRate = 0.03;
const _annSeed = 42;
const _bidirectionalFastForwardFlag = true;

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

        for (let i = 0; i < this.axioms.length; i++) {
            const axiom = this.axioms[i];
            const [a, b] = axiom.subnets;

            if (Array.isArray(a)) {
                samples.push({
                    t: this.compiler.encode(a, 0),
                    i
                });
            }

            if (Array.isArray(b)) {
                samples.push({
                    t: this.compiler.encode(b, 0),
                    i
                });
            }

            if (Array.isArray(a) && Array.isArray(b)) {
                samples.push({
                    t: this.compiler.encode([...a, ...b], 0),
                    i
                });
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

        return `ANN_AXIOM_SELECTOR_V2:${h}:${this.compiler.inputSize}:${this.hiddenSize}:${this.axioms.length}`;
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

        const predictWindow = (tokens) => {
            const windowKey = tokens.join(' ');
            if (seenWindows.has(windowKey)) return;

            seenWindows.add(windowKey);

            const prediction = this.ann.predictAddress(
                this.compiler.encode(tokens, 0)
            );

            this.stats.annPredictions++;

            if (prediction.valid) {
                this.stats.annValidPredictions++;

                const axiom = this.axioms[prediction.i];

                if (axiom) {
                    selected.set(prediction.i, axiom);
                }
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

        const merged = [];
        const seen = new Set();

        for (const axiom of predicted) {
            if (!seen.has(axiom.nnIndex)) {
                seen.add(axiom.nnIndex);
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

// Binary Heap implementation for O(log n) operations
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
                if (this.compare(rightChild, element) < 0 && 
                    this.compare(rightChild, this.items[leftChildIdx]) < 0) {
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
    const lhsQueue = new BinaryHeap();
    const rhsQueue = new BinaryHeap();
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

    // Generate all possible rewrites for an expression
    function* generateRewrites(expr, indir) {
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

        for (const axiom of relevantAxioms) {
            for (const [from, to] of [
                [axiom.subnets[0], axiom.subnets[1]],
                [axiom.subnets[1], axiom.subnets[0]]
            ]) {
                const hasPattern = from.some(token => token.includes('?'));

                if (!hasPattern) {
                    const results = [
                        tryReplace(expr, from, to, 'A'),
                        tryReplace(expr, from, to, 'B')
                    ];

                    for (const result of results) {
                        if (result) {
                            const axiomIndex = axiom.nnIndex;

                            if (annDispatcher && Number.isInteger(axiomIndex)) {
                                annDispatcher.addRuntimeSample(
                                    expr,
                                    axiomIndex,
                                    to.length > from.length ? 0 : 1
                                );
                            }

                            yield {
                                expr: result,
                                axiom: axiom.axiomID,
                                direction: to.length > from.length ? `expand` : `reduce`
                            };
                        }
                    }
                } else {
                    const match = matchPattern(from, expr);

                    if (match) {
                        const substitutedTo = applySubstitution(to, match.bindings);

                        const newExpr = [
                            ...expr.slice(0, match.position),
                            ...substitutedTo,
                            ...expr.slice(match.position + from.length)
                        ];

                        const axiomIndex = axiom.nnIndex;

                        if (annDispatcher && Number.isInteger(axiomIndex)) {
                            annDispatcher.addRuntimeSample(
                                expr,
                                axiomIndex,
                                to.length > from.length ? 0 : 1
                            );
                        }

                        yield {
                            expr: newExpr,
                            axiom: axiom.axiomID,
                            direction: to.length > from.length ? `expand` : `reduce`
                        };
                    }
                }
            }
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
            for (const rewrite of generateRewrites(current.expr, side)) {
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
                queue.enqueue(newState, newState.getPriority(targetExpr));
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