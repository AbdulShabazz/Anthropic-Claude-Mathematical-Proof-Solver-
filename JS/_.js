
let _input = document.getElementById('input');
let _output = document.getElementById('output');
let _lineNumbers = document.getElementById('line-numbers');
let _stats = document.getElementById('stats');

// Priority queue implementation for A* search
class PriorityQueue {
    constructor() {
        this.items = [];
    }
    
    enqueue(element, priority) {
        this.items.push({element, priority});
        this.items.sort((a, b) => a.priority - b.priority);
    }
    
    dequeue() {
        return this.items.shift()?.element;
    }
    
    isEmpty() {
        return this.items.length === 0;
    }
    
    size() {
        return this.items.length;
    }
}

function solveProblem() {
    const { axioms, proofStatement } = parseInput(_input.value);
    const startTime = performance.now();
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
        Strategy: ${result.stats.strategy}
    `;
}

function parseInput(input) {
    let lines = input
        .split('\n')
        .filter(line => line.trim() && !line.startsWith('//'));
    let axiomsSet = new Set();

    lines.slice().forEach((line, k) => {
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
            .sort((a, b) => a.length - b.length)
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
    
    // Statistics tracking
    const stats = {
        statesExplored: 0,
        uniqueStates: 0,
        queueOps: 0,
        maxDepth: 0,
        strategy: 'A* with heuristic'
    };

    // If already equal, return immediately
    if (lhsStr === rhsStr) {
        return {
            proof: "Proof Found!\n\n" + lhsStr + " = " + rhsStr + ", trivial\n\nQ.E.D.",
            stats
        };
    }

    // Heuristic function: estimate distance between two expressions
    function heuristic(expr1, expr2) {
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
        
        return h;
    }

    // Unified search state
    class SearchState {
        constructor(expr, path, side, depth = 0) {
            this.expr = expr;
            this.exprStr = expr.join(' ');
            this.path = path;
            this.side = side; // 'lhs' or 'rhs'
            this.depth = depth;
        }
        
        getPriority(targetExpr) {
            // f(n) = g(n) + h(n)
            const g = this.depth; // Cost so far
            const h = heuristic(this.expr, targetExpr); // Heuristic estimate
            return g + h;
        }
    }

    // Bidirectional A* search
    const lhsQueue = new PriorityQueue();
    const rhsQueue = new PriorityQueue();
    const lhsVisited = new Map(); // expression -> state
    const rhsVisited = new Map();
    
    // Initialize with starting states
    const lhsStart = new SearchState(lhs, [{expr: lhs, rule: 'start'}], 'lhs');
    const rhsStart = new SearchState(rhs, [{expr: rhs, rule: 'start'}], 'rhs');
    
    lhsQueue.enqueue(lhsStart, lhsStart.getPriority(rhs));
    rhsQueue.enqueue(rhsStart, rhsStart.getPriority(lhs));
    lhsVisited.set(lhsStr, lhsStart);
    rhsVisited.set(rhsStr, rhsStart);

    // Generate all possible rewrites for an expression
    function* generateRewrites(expr, axiomList) {
        for (const axiom of axiomList) {
            // Try both directions
            for (const [from, to] of [[axiom.subnets[0], axiom.subnets[1]], 
                                        [axiom.subnets[1], axiom.subnets[0]]]) {
                // Try all positions
                const results = [
                    tryReplace(expr, from, to, 'A'),
                    tryReplace(expr, from, to, 'B')
                ];
                
                for (const result of results) {
                    if (result) {
                        yield {
                            expr: result,
                            axiom: axiom.axiomID,
                            direction: from === axiom.subnets[0] ? 'forward expand' : 'backward reduce'
                        };
                    }
                }
            }
        }
    }

    // Main search loop
    let iterations = 0;
    const maxIterations = 10000;
    
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
            
            // Check if we've met in the middle
            if (otherVisited.has(current.exprStr)) {
                const otherState = otherVisited.get(current.exprStr);
                return {
                    proof: constructProof(current, otherState),
                    stats
                };
            }
            
            // Generate and explore neighbors
            for (const rewrite of generateRewrites(current.expr, axioms)) {
                const newExprStr = rewrite.expr.join(' ');
                
                // Skip if already visited with shorter path
                if (visited.has(newExprStr) && 
                    visited.get(newExprStr).depth <= current.depth + 1) {
                    continue;
                }
                
                const newState = new SearchState(
                    rewrite.expr,
                    [...current.path, {
                        expr: rewrite.expr,
                        rule: `${rewrite.axiom} (${rewrite.direction})`
                    }],
                    side,
                    current.depth + 1
                );
                
                visited.set(newExprStr, newState);
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
function constructProof(rhsState, lhsState) { /* swapped! */
    let proof = "Proof Found!\n\n";
    
    // LHS transformations
    const rhsStart = rhsState.path[0].expr.join(' ')
    for (let i = 0; i < lhsState.path.length; i++) {
        const step = lhsState.path[i];
        proof += `${step.expr.join(' ')} = ${rhsStart}`;
        if (step.rule !== 'start') {
            proof += `, via ${step.rule}`;
        }
        proof += '\n';
    }
    
    // RHS transformations (in reverse)
    const lhsEnd = lhsState.path[lhsState.path.length - 1].expr.join(' ')
    for (let i = 1; i < rhsState.path.length; i++) {
        const step = rhsState.path[i];
        proof += `${lhsEnd} = ${step.expr.join(' ')}`;
        proof += `, via ${step.rule}\n`;
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

// Initialize with example
_input.value = `// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4`;

updateLineNumbers();