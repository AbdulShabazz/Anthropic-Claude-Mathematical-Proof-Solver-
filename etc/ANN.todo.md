# TODO: ANN-Only Prover Stabilization

## Objective

Stabilize `ann_only` mode so the prover can complete regression proofs without deterministic fallback scans.

Current stable mode:

```js
const _annDispatchMode = "ann_first";
```

Target mode:

```js
const _annDispatchMode = "ann_only";
```

Success condition:

```txt
ann_only proves every regression case
fallback scans == 0
```

---

## 1. Add ANN beam configuration

Add near the ANN config block:

```js
const _annBeamWidth = 8;
const _annMaxUncertainBits = 4;
const _annTrainOnPartialProofFlag = true;
```

Purpose:

```txt
Replace brittle single-address decoding with a small constant-width candidate beam.
```

---

## 2. Add bitfield beam decoder helpers

Add these helpers near the existing ANN utility functions.

* [ ] `decodeBitfieldIndexFromBits(bits)`
* [ ] `makeBaseBits(bitProbabilities)`
* [ ] `cloneFlipBits(baseBits, flipIndexes)`
* [ ] `addressBeamFromBitProbabilities(...)`

Purpose:

```txt
ANN bit probabilities -> base address + nearby bit-flip candidates
```

Implementation target:

```txt
Do not score or sort all axioms.
Only generate K candidate addresses from the compressed bitfield.
```

---

## 3. Replace `getPredictedAxioms(expr)`

Replace the current single-address version with a beam-based version.

Required behavior:

* [ ] Predict on the whole expression.
* [ ] Predict on contiguous windows.
* [ ] Predict with `direction = 0`.
* [ ] Predict with `direction = 1`.
* [ ] Decode a beam of axiom addresses from each prediction.
* [ ] Deduplicate predicted axioms by `nnIndex`.
* [ ] Cache predictions by expression plus beam settings.

Purpose:

```txt
window -> ANN bit probabilities -> K candidate axiom indexes
```

Expected improvement:

```txt
ann_only gets enough candidate coverage to complete proofs without fallback.
```

---

## 4. Fix `ann_only` hit/miss accounting

Patch `mergePredictedWithFallback(expr, fallbackAxioms)`.

In `ann_only` mode:

```txt
hit  = ANN returned at least one candidate
miss = ANN returned zero candidates
```

Do not compare ANN predictions against fallback candidates in `ann_only`, because fallback is intentionally empty.

Purpose:

```txt
Make ann_only statistics structurally meaningful.
```

---

## 5. Train on partial proofs

Current replay training only runs after complete proof success.

Change replay training condition so failed `ann_only` runs can still train from partial proof samples.

Replace proof-only condition with:

```js
if (
    annDispatcher &&
    annDispatcher.runtimeSamples?.length > 0 &&
    (_annTrainOnPartialProofFlag || result.proof.includes("Proof Found!"))
) {
    annDispatcher.trainReplaySamples();
}
```

Purpose:

```txt
Partial-proof rewrites become training data.
```

---

## 6. Expand synthetic training to both rewrite directions

Modify `_buildTrainingSamples()`.

For each axiom, train on:

* [ ] LHS subnet with `d = 0`
* [ ] RHS subnet with `d = 0`
* [ ] Combined subnet with `d = 0`
* [ ] LHS subnet with `d = 1`
* [ ] RHS subnet with `d = 1`
* [ ] Combined subnet with `d = 1`

Expected effect:

```txt
training samples roughly double
```

Purpose:

```txt
Teach the ANN that the same token pattern can participate in expand and reduce contexts.
```

---

## 7. Invalidate cached ANN models

After changing features or training format, clear the old model cache.

Run once in the browser console:

```js
Object.keys(localStorage)
    .filter(k => k.startsWith("ANN_AXIOM_SELECTOR_V2:"))
    .forEach(k => localStorage.removeItem(k));
```

Purpose:

```txt
Force retraining with the updated feature compiler and training data.
```

---

## 8. Add stronger ANN usefulness metrics

Add these counters:

```js
annApplicableHits: 0,
annApplicableMisses: 0
```

Definition:

```txt
annApplicableHits:
  At least one ANN-predicted axiom actually produced a rewrite.

annApplicableMisses:
  ANN returned candidates, but none rewrote the expression.
```

Purpose:

```txt
Measure rewrite applicability, not merely valid decoded addresses.
```

Do not rely only on:

```txt
ANN valid predictions
```

because that only means:

```txt
decoded address is inside [0, axiomCount)
```

---

## 9. Regression-test in stages

### Stage A: Robust baseline

Set:

```js
const _annDispatchMode = "ann_first";
```

Run all test cases.

Pass criteria:

* [ ] Every theorem proves.
* [ ] `ANN dispatch misses` stays low.
* [ ] `ANN fallback useful hits` trends toward `0`.
* [ ] Runtime replay samples are captured.

---

### Stage B: Pure ANN dispatch

Set:

```js
const _annDispatchMode = "ann_only";
```

Run the same test cases.

Pass criteria:

* [ ] Every theorem proves.
* [ ] `ANN fallback scans == 0`.
* [ ] `ANN applicable hits > 0`.
* [ ] `ANN applicable misses` trends down after replay training.

---

## 10. Tune beam parameters

Initial values:

```js
const _annBeamWidth = 8;
const _annMaxUncertainBits = 4;
```

Test matrix:

| Beam Width | Max Uncertain Bits | Goal                 |
| ---------: | -----------------: | -------------------- |
|          4 |                  3 | Faster, narrower     |
|          8 |                  4 | Balanced default     |
|         16 |                  5 | Wider, more reliable |
|         32 |                  5 | Diagnostic only      |

Record for each run:

* [ ] Runtime
* [ ] States explored
* [ ] Unique states
* [ ] Queue operations
* [ ] Search depth
* [ ] ANN predictions
* [ ] ANN applicable hits
* [ ] ANN applicable misses
* [ ] Replay samples
* [ ] Proof found / partial only

---

## 11. Final target

The desired final architecture:

```txt
expr
  -> feature compiler
  -> ANN compressed bitfield prediction
  -> constant-width address beam
  -> deterministic rewrite attempt
  -> bidirectional meet cache
  -> proof
```

Avoid:

```txt
score all axioms
sort all axioms
scan all axioms
```

Target operating mode:

```js
const _annDispatchMode = "ann_only";
```

Target result:

```txt
complete proofs
zero fallback scans
bounded ANN candidate generation
```
