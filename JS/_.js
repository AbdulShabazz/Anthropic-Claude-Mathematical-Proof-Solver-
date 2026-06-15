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

const _bidirectionalFastForwardFlag = true;

// Hot-loop diagnostics. Keep false for benchmarking.
const _debugProofHistoryFlag = false;

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

function exprToString(expr) {
    return _tokenStore ? _tokenStore.exprToString(expr) : expr.join(' ');
}

function isPatternToken(token) {
    return _tokenStore
        ? _tokenStore.isPatternId(token)
        : String(token).startsWith('?');
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

// Optional exact-branch -> next directed rewrite-rule index cache.
// This is a rule-ordering hint, not a proof-pruning mechanism.
const _allRewriteRulesHintFlag = true;
let _AllRewriteRules = new Map();

// Unary/bucket priority queue for integer A* f-values.
// bucket index === f-value.
// minPriority is the scan offset / lower bound; buckets are not rebased.
class UnaryPriorityQueue {
    constructor(maxDirectPriority = 1 << 20) {
        this.buckets = [];
        this.occupiedWords = new Uint32Array(32);
        this.length = 0;
        this.minPriority = Number.POSITIVE_INFINITY;
        this.maxDirectPriority = maxDirectPriority;

        // Diagnostics.
        this.wordScans = 0;
        this.priorityAdvances = 0;
    }

    enqueue(element, priority) {
        priority = this._normalizePriority(priority);
        this._ensurePriority(priority);

        let bucket = this.buckets[priority];

        if (!bucket) {
            bucket = { items: [], head: 0 };
            this.buckets[priority] = bucket;
        }

        const wasEmpty = bucket.head >= bucket.items.length;
        bucket.items.push(element);

        if (wasEmpty) {
            this._setOccupied(priority);

            if (priority < this.minPriority) {
                this.minPriority = priority;
            }
        }

        this.length++;
    }

    dequeue() {
        if (this.length === 0) return undefined;

        const priority = this._nextOccupiedPriority(this.minPriority);
        if (priority === Number.POSITIVE_INFINITY) return undefined;

        this.minPriority = priority;

        const bucket = this.buckets[priority];
        const element = bucket.items[bucket.head++];

        this.length--;

        if (bucket.head >= bucket.items.length) {
            bucket.items.length = 0;
            bucket.head = 0;
            this._clearOccupied(priority);

            this.minPriority = this.length === 0
                ? Number.POSITIVE_INFINITY
                : this._nextOccupiedPriority(priority + 1);
        } else if (bucket.head > 64 && bucket.head * 2 > bucket.items.length) {
            // Avoid unbounded retained dead slots in long-lived equal-priority buckets.
            bucket.items = bucket.items.slice(bucket.head);
            bucket.head = 0;
        }

        return element;
    }

    peekPriority() {
        if (this.length === 0) return Number.POSITIVE_INFINITY;
        return this._nextOccupiedPriority(this.minPriority);
    }

    isEmpty() {
        return this.length === 0;
    }

    size() {
        return this.length;
    }

    _normalizePriority(priority) {
        if (!Number.isFinite(priority)) {
            throw new Error(`UnaryPriorityQueue priority must be finite. Received: ${priority}`);
        }

        priority = Math.trunc(priority);

        if (priority < 0) {
            throw new Error(`UnaryPriorityQueue priority must be >= 0. Received: ${priority}`);
        }

        if (priority > this.maxDirectPriority) {
            throw new Error(
                `UnaryPriorityQueue priority ${priority} exceeds maxDirectPriority ${this.maxDirectPriority}. ` +
                `Increase maxDirectPriority or use BinaryHeap for sparse/high f-values.`
            );
        }

        return priority;
    }

    _ensurePriority(priority) {
        const requiredWords = (priority >> 5) + 1;

        if (requiredWords <= this.occupiedWords.length) return;

        let nextWords = this.occupiedWords.length || 1;

        while (nextWords < requiredWords) {
            nextWords <<= 1;
        }

        const grown = new Uint32Array(nextWords);
        grown.set(this.occupiedWords);
        this.occupiedWords = grown;
    }

    _setOccupied(priority) {
        this.occupiedWords[priority >> 5] |= (1 << (priority & 31));
    }

    _clearOccupied(priority) {
        this.occupiedWords[priority >> 5] &= ~(1 << (priority & 31));
    }

    _nextOccupiedPriority(fromPriority) {
        let wordIndex = fromPriority >> 5;
        const bitOffset = fromPriority & 31;

        if (wordIndex >= this.occupiedWords.length) {
            return Number.POSITIVE_INFINITY;
        }

        let word = this.occupiedWords[wordIndex] & (-1 << bitOffset);

        while (wordIndex < this.occupiedWords.length) {
            this.wordScans++;

            if (word !== 0) {
                const lowestBit = word & -word;
                const bitIndex = 31 - Math.clz32(lowestBit);
                const priority = (wordIndex << 5) + bitIndex;

                if (priority > fromPriority) {
                    this.priorityAdvances += priority - fromPriority;
                }

                return priority;
            }

            wordIndex++;
            word = wordIndex < this.occupiedWords.length
                ? this.occupiedWords[wordIndex]
                : 0;
        }

        return Number.POSITIVE_INFINITY;
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

function allRewriteRuleBranchKey(side, expr) {
    return `${side}|${exprKey(expr)}`;
}

function rememberAllRewriteRuleHint(expr, side, ruleIndex) {
    if (!_allRewriteRulesHintFlag) {
        return { key: null, ruleIndex: -1 };
    }

    if (!Number.isInteger(ruleIndex) || ruleIndex < 0 || !Array.isArray(expr) || expr.length === 0) {
        return { key: null, ruleIndex: -1 };
    }

    const key = allRewriteRuleBranchKey(side, expr);
    _AllRewriteRules.set(key, ruleIndex);

    return { key, ruleIndex };
}

function ruleHasOccurrence(expr, rule, positionIndex) {
    for (const _occurrence of matchRuleOccurrences(expr, rule, positionIndex)) {
        return true;
    }

    return false;
}

function rememberNextRewriteRuleHint(expr, side, stats = null) {
    if (!_allRewriteRulesHintFlag || !Array.isArray(expr) || expr.length === 0) {
        return { key: null, ruleIndex: -1 };
    }

    const indexed = buildPositionIndexAndTally(expr);
    const positionIndex = indexed.positionIndex;
    const exprTally = indexed.tally;

    if (stats) {
        stats.allRewriteRulePreviewBuilds++;
    }

    const relevantRules = rewriteRuleIndex.getRelevantRules(positionIndex);

    if (stats) {
        stats.allRewriteRulePreviewScans++;
    }

    // Preserve the current rule-index order. No sort.
    for (const rule of relevantRules) {
        if (!tallyContainsRule(exprTally, expr.length, rule)) {
            continue;
        }

        if (!ruleHasOccurrence(expr, rule, positionIndex)) {
            continue;
        }

        return rememberAllRewriteRuleHint(expr, side, rule.ruleIndex);
    }

    return { key: null, ruleIndex: -1 };
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
        const ruleIndex = ruleOrdinal++;

        rules.push({
            // Unique rule identity. Do not derive this only from axiomID.
            ruleIndex,
            ruleID: `rule_${ruleIndex}`,

            axiomID: axiom.axiomID,
            guidZ: axiom.guidZ,

            from,
            to,
            fromLen: from.length,
            toLen: to.length,
            firstToken: from[0],
            hasPattern: from.some(isPatternToken),
            anchorToken: anchor?.token ?? null,
            anchorOffset: anchor?.offset ?? -1,
            direction: to.length > from.length ? 'expand' : 'reduce',

            requiredFromTally: makeRuleRequiredTally(from),

            // Optional trace metadata.
            orientation,
            sourceLine: axiom.sourceLine,
            sourcePair: axiom.sourcePair
        });
    };

    for (let i = 0; i < axioms.length; i++) {
        const axiom = axioms[i];
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
        this.rules = rules;
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

    getRuleByIndex(ruleIndex) {
        return Number.isInteger(ruleIndex) ? this.rules[ruleIndex] : null;
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

function buildPositionIndexAndTally(expr) {
    const positionIndex = new Map();
    const tally = new Int16Array(_tokenStore.idToToken.length);

    for (let i = 0; i < expr.length; i++) {
        const token = expr[i];

        tally[token]++;

        let positions = positionIndex.get(token);

        if (!positions) {
            positions = [];
            positionIndex.set(token, positions);
        }

        positions.push(i);
    }

    return {
        positionIndex,
        tally
    };
}

function makeRuleRequiredTally(tokens) {
    const counts = new Map();

    for (const token of tokens) {
        if (isPatternToken(token)) continue;

        counts.set(token, (counts.get(token) || 0) + 1);
    }

    const required = [];

    for (const [token, count] of counts) {
        required.push({ token, count });
    }

    return required;
}

function tallyContainsRule(exprTally, exprLength, rule) {
    if (rule.fromLen > exprLength) {
        return false;
    }

    for (const req of rule.requiredFromTally) {
        if ((exprTally[req.token] || 0) < req.count) {
            return false;
        }
    }

    return true;
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
let proofHistory = [];

function solveProblem() {
    const { axioms, proofStatement } = parseInput(_input.value);
    const startTime = performance.now();

    heuristicCache = new HeuristicCache();
    proofHistory = [];
    _AllRewriteRules = new Map();

    const rewriteRules = compileRewriteRules(axioms);
    rewriteRuleIndex = new RewriteRuleIndex(rewriteRules);

    const result = generateProofOptimized(axioms, proofStatement);
    const endTime = performance.now();

    _output.value = result.proof;
    _output.value += `\n\nTotal runtime: ${(endTime - startTime).toFixed(4)} ms`;

    _stats.innerHTML = `
        <strong>Search Statistics:</strong><br>
        States explored: ${result.stats.statesExplored}<br>
        Unique states: ${result.stats.uniqueStates}<br>
        Queue operations: ${result.stats.queueOps}<br>
        Unary queue word scans: ${result.stats.unaryQueueWordScans}<br>
        Unary queue priority advances: ${result.stats.unaryQueuePriorityAdvances}<br>
        _AllRewriteRules size: ${_AllRewriteRules.size}<br>
        _AllRewriteRules lookups: ${result.stats.allRewriteRuleLookups}<br>
        _AllRewriteRules hits: ${result.stats.allRewriteRuleHits}<br>
        _AllRewriteRules misses: ${result.stats.allRewriteRuleMisses}<br>
        _AllRewriteRules yielded candidates: ${result.stats.allRewriteRuleCandidatesYielded}<br>
        _AllRewriteRules preview builds: ${result.stats.allRewriteRulePreviewBuilds}<br>
        _AllRewriteRules preview scans: ${result.stats.allRewriteRulePreviewScans}<br>
        Search depth: ${result.stats.maxDepth}<br>
        Strategy: ${result.stats.strategy}<br>
        Token count: ${result.stats.tokenCount}<br>
        Directed rewrite rules: ${result.stats.rewriteRuleCount}<br>
        Position-index builds: ${result.stats.positionIndexBuilds}<br>
        Rule match attempts: ${result.stats.ruleMatchAttempts}<br>
        Rewrite candidates yielded: ${result.stats.rewriteCandidatesYielded}<br>
        Rule-index scans: ${result.stats.ruleIndexScans}<br>
        Debug proof history: ${_debugProofHistoryFlag ? 'on' : 'off'}<br>
        Tally rule rejects: ${result.stats.tallyRuleRejects}<br>
        Tally rule passes: ${result.stats.tallyRulePasses}<br>
        Final proof steps: ${result.stats.proofSteps}<br>
        Debug history records: ${proofHistory.length}
    `;

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

        ruleIndexScans: 0,

        tallyRuleRejects: 0,
        tallyRulePasses: 0,

        unaryQueueWordScans: 0,
        unaryQueuePriorityAdvances: 0,

        allRewriteRuleLookups: 0,
        allRewriteRuleHits: 0,
        allRewriteRuleMisses: 0,
        allRewriteRuleCandidatesYielded: 0,
        allRewriteRulePreviewBuilds: 0,
        allRewriteRulePreviewScans: 0,

        meetChecks: 0,
        fastForwardHits: 0
    };

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
        constructor(expr, parent, rule, side, depth = 0, searchStrategy = _currentSearchStrategy.config, rewriteRuleKey = null, rewriteRuleIndex = -1) {
            this.expr = expr;
            this.parent = parent;
            this.rule = rule || 'start';
            this.side = side;
            this.depth = depth;
            this.searchStrategy = searchStrategy;
            this.rewriteRuleKey = rewriteRuleKey;
            this.rewriteRuleIndex = Number.isInteger(rewriteRuleIndex) ? rewriteRuleIndex : -1;

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
        
        updateQueueStats();

        proof += "\nQ.E.D.";
        stats.proofSteps = Math.max(0, lhsPath.length + rhsPath.length - 1);
        return proof;
    }

    const lhsQueue = new UnaryPriorityQueue();
    const rhsQueue = new UnaryPriorityQueue();
    const lhsVisited = new Map();
    const rhsVisited = new Map();
    
    const lhsStart = new SearchState(lhs, null, 'start', 'lhs');
    const rhsStart = new SearchState(rhs, null, 'start', 'rhs');
    
    lhsQueue.enqueue(lhsStart, lhsStart.getPriority(rhs));
    rhsQueue.enqueue(rhsStart, rhsStart.getPriority(lhs));
    lhsVisited.set(lhsStart.canonicalStr, lhsStart);
    rhsVisited.set(rhsStart.canonicalStr, rhsStart);

    function updateQueueStats() {
        stats.unaryQueueWordScans = lhsQueue.wordScans + rhsQueue.wordScans;
        stats.unaryQueuePriorityAdvances = lhsQueue.priorityAdvances + rhsQueue.priorityAdvances;
    }

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

    function* generateRewrites(expr, side, preferredRuleIndex = -1) {
        const indexed = buildPositionIndexAndTally(expr);
        const positionIndex = indexed.positionIndex;
        const exprTally = indexed.tally;
        const emittedRuleIDs = new Set();

        stats.positionIndexBuilds++;

        function* emitRuleMatches(rule, fromAllRewriteRules) {
            if (!rule || emittedRuleIDs.has(rule.ruleID)) {
                return;
            }

            emittedRuleIDs.add(rule.ruleID);

            if (!tallyContainsRule(exprTally, expr.length, rule)) {
                stats.tallyRuleRejects++;
                return;
            }

            stats.tallyRulePasses++;
            stats.ruleMatchAttempts++;

            for (const occurrence of matchRuleOccurrences(expr, rule, positionIndex)) {
                const resultExpr = occurrence.resultExpr || replaceAt(expr, rule.from, occurrence.to, occurrence.position);

                stats.rewriteCandidatesYielded++;

                if (fromAllRewriteRules) {
                    stats.allRewriteRuleCandidatesYielded++;
                }

                yield {
                    expr: resultExpr,
                    axiom: rule.axiomID,
                    direction: rule.direction,
                    method: occurrence.method,
                    position: occurrence.position,
                    ruleIndex: rule.ruleIndex
                };
            }
        }

        if (_allRewriteRulesHintFlag && preferredRuleIndex >= 0) {
            const preferredRule = rewriteRuleIndex.getRuleByIndex(preferredRuleIndex);
            yield* emitRuleMatches(preferredRule, true);
        }

        const relevantRules = rewriteRuleIndex.getRelevantRules(positionIndex);
        stats.ruleIndexScans++;

        for (const rule of relevantRules) {
            yield* emitRuleMatches(rule, false);
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
                    stats
                };
            }

            const currentRuleIndex = _allRewriteRulesHintFlag ? current.rewriteRuleIndex : -1;

            if (_allRewriteRulesHintFlag) {
                stats.allRewriteRuleLookups++;

                if (currentRuleIndex >= 0) {
                    stats.allRewriteRuleHits++;
                } else {
                    stats.allRewriteRuleMisses++;
                }
            }
            
            for (const rewrite of generateRewrites(current.expr, side, currentRuleIndex)) {
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
                        stats
                    };
                }

                if (_allRewriteRulesHintFlag) {
                    const hint = rememberNextRewriteRuleHint(newState.expr, side, stats);
                    newState.rewriteRuleKey = hint.key;
                    newState.rewriteRuleIndex = hint.ruleIndex;
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
        stats
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