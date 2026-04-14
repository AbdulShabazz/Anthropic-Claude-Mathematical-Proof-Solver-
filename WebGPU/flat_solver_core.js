'use strict';

class MinHeap {
  constructor(compare) {
    this.items = [];
    this.compare = compare || ((a, b) => a.priority - b.priority);
  }
  push(item) {
    this.items.push(item);
    this._up(this.items.length - 1);
  }
  pop() {
    if (this.items.length === 0) return undefined;
    const top = this.items[0];
    const end = this.items.pop();
    if (this.items.length) {
      this.items[0] = end;
      this._down(0);
    }
    return top;
  }
  size() { return this.items.length; }
  isEmpty() { return this.items.length === 0; }
  _up(i) {
    const item = this.items[i];
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (this.compare(item, this.items[p]) >= 0) break;
      this.items[i] = this.items[p];
      i = p;
    }
    this.items[i] = item;
  }
  _down(i) {
    const len = this.items.length;
    const item = this.items[i];
    for (;;) {
      let s = i;
      const l = i * 2 + 1;
      const r = l + 1;
      if (l < len && this.compare(this.items[l], this.items[s]) < 0) s = l;
      if (r < len && this.compare(this.items[r], this.items[s]) < 0) s = r;
      if (s === i) break;
      this.items[i] = this.items[s];
      i = s;
    }
    this.items[i] = item;
  }
}

class TokenStore {
  constructor() {
    this.idByToken = new Map();
    this.tokenById = [];
    this.tokenArena = [];
    this.exprMeta = [];
    this.hashByExprId = [];
  }

  internToken(token) {
    let id = this.idByToken.get(token);
    if (id !== undefined) return id;
    id = this.tokenById.length;
    this.idByToken.set(token, id);
    this.tokenById.push(token);
    return id;
  }

  encodeTokens(tokens) {
    return Uint32Array.from(tokens.map((t) => this.internToken(t)));
  }

  appendExprFromTokenIds(tokenIds) {
    const offset = this.tokenArena.length;
    for (let i = 0; i < tokenIds.length; i++) this.tokenArena.push(tokenIds[i] >>> 0);
    const length = tokenIds.length >>> 0;
    const exprId = this.exprMeta.length;
    const hash = hashTokenIds(tokenIds);
    this.exprMeta.push({ offset, length });
    this.hashByExprId.push(hash);
    return exprId;
  }

  appendExprFromTokens(tokens) {
    return this.appendExprFromTokenIds(this.encodeTokens(tokens));
  }

  getExprTokenIds(exprId) {
    const meta = this.exprMeta[exprId];
    return this.tokenArena.slice(meta.offset, meta.offset + meta.length);
  }

  decodeExpr(exprId) {
    return this.getExprTokenIds(exprId).map((id) => this.tokenById[id]);
  }

  exprToString(exprId) {
    return this.decodeExpr(exprId).join(' ');
  }
}

function hashTokenIds(tokenIds) {
  let h1 = 0x811c9dc5 >>> 0;
  let h2 = 0x9e3779b9 >>> 0;
  for (let i = 0; i < tokenIds.length; i++) {
    const x = tokenIds[i] >>> 0;
    h1 ^= x + 0x9e3779b9 + ((h1 << 6) >>> 0) + (h1 >>> 2);
    h1 = Math.imul(h1, 16777619) >>> 0;
    h2 ^= (x << ((i & 7) + 1)) >>> 0;
    h2 = Math.imul(h2 ^ 0x85ebca6b, 2246822519) >>> 0;
  }
  return [h1 >>> 0, h2 >>> 0, tokenIds.length >>> 0];
}

function eqHash(a, b) {
  return a[0] === b[0] && a[1] === b[1] && a[2] === b[2];
}

function sameExpr(store, exprIdA, exprIdB) {
  if (!eqHash(store.hashByExprId[exprIdA], store.hashByExprId[exprIdB])) return false;
  const a = store.getExprTokenIds(exprIdA);
  const b = store.getExprTokenIds(exprIdB);
  if (a.length !== b.length) return false;
  for (let i = 0; i < a.length; i++) if (a[i] !== b[i]) return false;
  return true;
}

function signatureKey(store, exprId) {
  const h = store.hashByExprId[exprId];
  const ids = store.getExprTokenIds(exprId);
  return `${h[0]}:${h[1]}:${h[2]}:${ids.join(',')}`;
}

function heuristic(store, exprIdA, exprIdB) {
  const a = store.getExprTokenIds(exprIdA);
  const b = store.getExprTokenIds(exprIdB);
  let score = Math.abs(a.length - b.length) * 2;
  const sa = new Set(a);
  const sb = new Set(b);
  let common = 0;
  for (const x of sa) if (sb.has(x)) common++;
  score += (sa.size + sb.size - 2 * common);
  const minLen = Math.min(a.length, b.length);
  for (let i = 0; i < minLen; i++) if (a[i] !== b[i]) score++;
  return score;
}

function tokenizeExpr(s) {
  return s.trim().split(/\s+/).filter(Boolean);
}

function parseInput(text) {
  const lines = text.split(/\r?\n/).map((s) => s.trim()).filter((s) => s && !s.startsWith('//'));
  if (lines.length < 1) throw new Error('Expected at least one equation.');
  const equations = lines.map((line) => {
    const parts = line.split(/[~<]?=+[>]?/g).map((s) => s.trim());
    if (parts.length !== 2) throw new Error(`Expected binary equation: ${line}`);
    return { lhs: tokenizeExpr(parts[0]), rhs: tokenizeExpr(parts[1]), raw: line };
  });
  return {
    axioms: equations.slice(0, -1),
    goal: equations[equations.length - 1],
  };
}

function compileProblem(inputText) {
  const parsed = typeof inputText === 'string' ? parseInput(inputText) : inputText;
  const store = new TokenStore();
  const rules = parsed.axioms.map((ax, i) => ({
    id: i,
    lhsExprId: store.appendExprFromTokens(ax.lhs),
    rhsExprId: store.appendExprFromTokens(ax.rhs),
    label: `axiom_${i + 1}.0`,
  }));
  const lhsGoalExprId = store.appendExprFromTokens(parsed.goal.lhs);
  const rhsGoalExprId = store.appendExprFromTokens(parsed.goal.rhs);
  return {
    store,
    rules,
    goal: {
      lhsExprId: lhsGoalExprId,
      rhsExprId: rhsGoalExprId,
      raw: parsed.goal.raw,
    },
  };
}

function findMatches(haystack, needle) {
  const matches = [];
  if (needle.length === 0 || needle.length > haystack.length) return matches;
  outer: for (let i = 0; i <= haystack.length - needle.length; i++) {
    for (let j = 0; j < needle.length; j++) {
      if (haystack[i + j] !== needle[j]) continue outer;
    }
    matches.push(i);
  }
  return matches;
}

function rewriteAt(haystack, pos, fromLen, replacement) {
  const out = new Uint32Array(haystack.length - fromLen + replacement.length);
  out.set(haystack.subarray(0, pos), 0);
  out.set(replacement, pos);
  out.set(haystack.subarray(pos + fromLen), pos + replacement.length);
  return out;
}

function generateLiteralBatch(store, frontierExprIds, rules, side) {
  const out = [];
  for (const exprId of frontierExprIds) {
    const exprIds = Uint32Array.from(store.getExprTokenIds(exprId));
    for (const rule of rules) {
      const fromExprId = side === 'lhs' ? rule.lhsExprId : rule.rhsExprId;
      const toExprId = side === 'lhs' ? rule.rhsExprId : rule.lhsExprId;
      const fromIds = Uint32Array.from(store.getExprTokenIds(fromExprId));
      const toIds = Uint32Array.from(store.getExprTokenIds(toExprId));
      const positions = findMatches(exprIds, fromIds);
      for (const pos of positions) {
        const rewritten = rewriteAt(exprIds, pos, fromIds.length, toIds);
        const newExprId = store.appendExprFromTokenIds(rewritten);
        out.push({ sourceExprId: exprId, newExprId, ruleId: rule.id, ruleLabel: rule.label, pos });
      }
    }
  }
  return out;
}

function reconstructProof(store, meetKey, visitedL, visitedR) {
  const leftPath = [];
  let cur = visitedL.get(meetKey);
  while (cur) {
    leftPath.push(cur);
    cur = cur.parentKey ? visitedL.get(cur.parentKey) : null;
  }
  leftPath.reverse();

  const rightPath = [];
  cur = visitedR.get(meetKey);
  while (cur) {
    rightPath.push(cur);
    cur = cur.parentKey ? visitedR.get(cur.parentKey) : null;
  }

  const lines = ['Proof Found!', ''];
  for (let i = 0; i < leftPath.length; i++) {
    const s = leftPath[i];
    const expr = store.exprToString(s.exprId);
    lines.push(i === 0 ? `${expr}` : `${expr}    via ${s.ruleLabel} (${s.side})`);
  }
  for (let i = 1; i < rightPath.length; i++) {
    const s = rightPath[i];
    const expr = store.exprToString(s.exprId);
    lines.push(`${expr}    via ${s.ruleLabel} (${s.side})`);
  }
  lines.push('', 'Q.E.D.');
  return lines.join('\n');
}

const MAX_ITERATIONS_Z = 1e6;

function solveFlat(inputText, options = {}) {
  const compiled = compileProblem(inputText);
  const { store, rules, goal } = compiled;
  const maxIterations = options.maxIterations || MAX_ITERATIONS_Z;
  const batchSize = options.batchSize || 64;
  const stats = { iterations: 0, expanded: 0, generated: 0, unique: 0, maxDepth: 1e6 };

  if (sameExpr(store, goal.lhsExprId, goal.rhsExprId)) {
    return { ok: true, proof: `Proof Found!\n\n${store.exprToString(goal.lhsExprId)} = ${store.exprToString(goal.rhsExprId)}\n\nQ.E.D.`, stats, compiled };
  }

  const makeState = (exprId, side, depth, parentKey, ruleLabel) => ({ exprId, side, depth, parentKey, ruleLabel });
  const keyL0 = signatureKey(store, goal.lhsExprId);
  const keyR0 = signatureKey(store, goal.rhsExprId);
  const visitedL = new Map([[keyL0, makeState(goal.lhsExprId, 'lhs', 0, null, 'start')]]);
  const visitedR = new Map([[keyR0, makeState(goal.rhsExprId, 'rhs', 0, null, 'start')]]);
  const heapL = new MinHeap((a, b) => a.priority - b.priority);
  const heapR = new MinHeap((a, b) => a.priority - b.priority);
  heapL.push({ exprId: goal.lhsExprId, depth: 0, priority: heuristic(store, goal.lhsExprId, goal.rhsExprId), key: keyL0 });
  heapR.push({ exprId: goal.rhsExprId, depth: 0, priority: heuristic(store, goal.rhsExprId, goal.lhsExprId), key: keyR0 });

  function expandOneSide(heap, ownVisited, otherVisited, side, targetExprId) {
    if (heap.isEmpty()) return null;
    const frontier = [];
    while (!heap.isEmpty() && frontier.length < batchSize) frontier.push(heap.pop());
    stats.expanded += frontier.length;
    const candidates = generateLiteralBatch(store, frontier.map((x) => x.exprId), rules, side);
    stats.generated += candidates.length;

    const parentByExprId = new Map(frontier.map((x) => [x.exprId, x]));
    for (const c of candidates) {
      const k = signatureKey(store, c.newExprId);
      if (ownVisited.has(k)) continue;
      const parent = parentByExprId.get(c.sourceExprId);
      const depth = (parent?.depth || 0) + 1;
      stats.maxDepth = Math.max(stats.maxDepth, depth);
      ownVisited.set(k, makeState(c.newExprId, side, depth, parent?.key || signatureKey(store, c.sourceExprId), c.ruleLabel));
      const priority = depth + heuristic(store, c.newExprId, targetExprId);
      heap.push({ exprId: c.newExprId, depth, priority, key: k });
      if (otherVisited.has(k)) return k;
    }
    return null;
  }

  for (let i = 0; i < maxIterations; i++) {
    stats.iterations = i + 1;
    const m1 = expandOneSide(heapL, visitedL, visitedR, 'lhs', goal.rhsExprId);
    if (m1) {
      stats.unique = visitedL.size + visitedR.size;
      return { ok: true, proof: reconstructProof(store, m1, visitedL, visitedR), stats, compiled };
    }
    const m2 = expandOneSide(heapR, visitedR, visitedL, 'rhs', goal.lhsExprId);
    if (m2) {
      stats.unique = visitedL.size + visitedR.size;
      return { ok: true, proof: reconstructProof(store, m2, visitedL, visitedR), stats, compiled };
    }
    if (heapL.isEmpty() && heapR.isEmpty()) break;
  }

  stats.unique = visitedL.size + visitedR.size;
  return { ok: false, proof: 'No proof found within search limits.', stats, compiled };
}

const WGSL_MATCH_LITERAL = `
struct RuleMeta {
  fromOffset : u32,
  fromLength : u32,
  toOffset : u32,
  toLength : u32,
};

@group(0) @binding(0) var<storage, read> tokenArena : array<u32>;
@group(0) @binding(1) var<storage, read> exprMeta : array<vec2<u32>>;
@group(0) @binding(2) var<storage, read> frontierExprIds : array<u32>;
@group(0) @binding(3) var<storage, read> ruleMeta : array<RuleMeta>;
@group(0) @binding(4) var<storage, read_write> outMatches : array<vec4<u32>>;

fn tokensEqual(exprOffset : u32, pos : u32, ruleOffset : u32, len : u32) -> bool {
  for (var i : u32 = 0u; i < len; i = i + 1u) {
    if (tokenArena[exprOffset + pos + i] != tokenArena[ruleOffset + i]) {
      return false;
    }
  }
  return true;
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid : vec3<u32>) {
  let frontierIdx = gid.x;
  let exprId = frontierExprIds[frontierIdx];
  let meta = exprMeta[exprId];
  let exprOffset = meta.x;
  let exprLen = meta.y;

  for (var ruleIdx : u32 = 0u; ruleIdx < arrayLength(&ruleMeta); ruleIdx = ruleIdx + 1u) {
    let rule = ruleMeta[ruleIdx];
    if (rule.fromLength > exprLen) { continue; }
    for (var pos : u32 = 0u; pos + rule.fromLength <= exprLen; pos = pos + 1u) {
      if (tokensEqual(exprOffset, pos, rule.fromOffset, rule.fromLength)) {
        let outIdx = frontierIdx * 64u + pos;
        outMatches[outIdx] = vec4<u32>(exprId, ruleIdx, pos, 1u);
      }
    }
  }
}
`;
`
module.exports = {
  TokenStore,
  parseInput,
  compileProblem,
  solveFlat,
  generateLiteralBatch,
  heuristic,
  hashTokenIds,
  signatureKey,
  WGSL_MATCH_LITERAL,
};`
