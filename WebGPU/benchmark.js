'use strict';
const { performance } = require('perf_hooks');
const { solveFlat } = require('./flat_solver_core.js');

const cases = [
  {
    name: 'simple',
    input: `// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4`,
    iterations: 200,
  },
  {
    name: 'chain-12',
    input: `a = b
b = c
c = d
d = e
e = f
f = g
g = h
h = i
i = j
j = k
k = l

// Prove
a = l`,
    iterations: 200,
  },
  {
    name: 'swap',
    input: `x y = y x
y z = z y

// Prove
x y z = z y x`,
    iterations: 50,
  },
];

function stats(values) {
  const sorted = [...values].sort((a, b) => a - b);
  const sum = values.reduce((a, b) => a + b, 0);
  const pick = (p) => sorted[Math.min(sorted.length - 1, Math.floor(sorted.length * p))];
  return {
    avgMs: sum / values.length,
    p50Ms: pick(0.50),
    p95Ms: pick(0.95),
    minMs: sorted[0],
    maxMs: sorted[sorted.length - 1],
  };
}

for (const c of cases) {
  const times = [];
  let last = null;
  for (let i = 0; i < c.iterations; i++) {
    const t0 = performance.now();
    last = solveFlat(c.input, { maxIterations: 2000, batchSize: 64 });
    const t1 = performance.now();
    times.push(t1 - t0);
  }
  const s = stats(times);
  console.log(`CASE ${c.name}`);
  console.log(JSON.stringify({ ok: last.ok, stats: last.stats, timing: s }, null, 2));
}
