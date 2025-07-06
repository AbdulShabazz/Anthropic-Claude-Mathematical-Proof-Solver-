let _input = document.getElementById('input');
let _output = document.getElementById('output');
let _lineNumbers = document.getElementById('line-numbers');
let _stats = document.getElementById('stats');

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
let proofHistory = [];

function solveProblem() {
    const { axioms, proofStatement } = parseInput(_input.value);
    const startTime = performance.now();
    
    // Reset global state
    heuristicCache = new HeuristicCache();
    axiomIndex = new AxiomIndex();
    proofHistory = [];
    
    // Build axiom index
    for (const axiom of axioms) {
        axiomIndex.addAxiom(axiom);
    }
    
    const result = generateProofOptimized(axioms, proofStatement);
    const endTime = performance.now();
    
    _output.value = result.proof;
    _output.value += `\n\nTotal runtime: ${(endTime - startTime).toFixed(4)} ms`;
    
    // Display statistics
    _stats.innerHTML = `
        <strong>Search Statistics:</strong><br>
        States explored: ${result.stats.statesExplored}<br>
        Unique states: ${result.stats.uniqueStates}<br>
        Queue operations: ${result.stats.queueOps}<br>
        Search depth: ${result.stats.maxDepth}<br>
        Strategy: ${result.stats.strategy}<br>
        Proof steps found: ${proofHistory.length}
    `;
    
    // If no complete proof, show partial proof
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
            .sort((a, b) => a.length - b.length) // (lhs/rhs) //
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
        strategy: 'BFS (Greedy) with heuristic'
    };

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
                searchStrategy = 'greedy' /* 'greedy', 'a*', or 'adaptive' */) {
            this.expr = expr;
            this.canonicalExpr = canonicalize(expr);
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

    // Generate all possible rewrites for an expression
    function* generateRewrites(expr, indir) {
        const relevantAxioms = axiomIndex.getRelevantAxioms(expr);
        
        for (const axiom of relevantAxioms) {
            // Try both directions
            for (const [from, to] of [[axiom.subnets[0], axiom.subnets[1]], 
                                        [axiom.subnets[1], axiom.subnets[0]]]) {
                
                // Check for pattern variables
                const hasPattern = from.some(token => token.includes('?'));
                
                if (hasPattern) {
                    // Pattern matching
                    const match = matchPattern(from, expr);
                    if (match) {
                        const substitutedTo = applySubstitution(to, match.bindings);
                        const newExpr = [
                            ...expr.slice(0, match.position),
                            ...substitutedTo,
                            ...expr.slice(match.position + from.length)
                        ];
                        
                        yield {
                            expr: newExpr,
                            axiom: axiom.axiomID,
                            direction: from === axiom.subnets[0] ? `expand` : `reduce`
                        };
                    }
                } else {
                    // Regular replacement
                    const results = [
                        tryReplace(expr, from, to, 'A'),
                        tryReplace(expr, from, to, 'B')
                    ];
                    
                    for (const result of results) {
                        if (result) {
                            yield {
                                expr: result,
                                axiom: axiom.axiomID,
                                direction: from === axiom.subnets[0] ? `expand` : `reduce`
                            };
                        }
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
                    stats
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
                
                // Skip if already visited with shorter path
                if (visited.has(newState.canonicalStr) && 
                    visited.get(newState.canonicalStr).depth <= newState.depth) {
                    continue;
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
        stats
    };
}

// Construct the final proof from two meeting paths
function constructProof(lhsState, rhsState) {
    let proof = "Proof Found!\n\n";
    
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
        proof += `${lhsEnd} = ${step.expr.join(' ')}`;
        proof += `, via ${step.rule} (rhs)\n`;
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