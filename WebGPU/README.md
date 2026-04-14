# Flat GPU Solver Prototype

This project is a first-pass GPU-targeted rewrite solver prototype.

## Included files

- `flat_solver_core.js` — CommonJS core solver.
- `flat_solver_core_es.js` — ES module bridge for browser import.
- `benchmark.js` — Node benchmark harness.
- `webgpu_demo.html` — Browser demo with WebGPU probe.

## Design

The project merges two directions:

- flat numeric symbolic storage from the older solver variant
- bidirectional frontier search from the newer solver variant

Current scope:

- flat token arena
- typed-array friendly expression storage
- bidirectional CPU search
- literal token-span rewrites
- WGSL compute shader scaffold for batch literal matching

Not yet included:

- pattern-variable rewrite support on GPU
- full canonicalization kernel
- end-to-end GPU dispatch path
- full semantic parity with the working object-heavy solver

## Run

Node benchmark:

```bash
node benchmark.js
```

Browser demo:

1. Open `webgpu_demo.html` in a browser.
2. Click `Run CPU solver`.
3. Click `Probe WebGPU` to test availability and shader module creation.

## Example input

```text
// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4
```

## Notes

The current solver is intentionally literal. The immediate next step is to offload batch frontier expansion and scoring to WebGPU while keeping frontier ownership, visited sets, and proof reconstruction on the CPU.
