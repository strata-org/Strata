# W6: Dead-Lemma Deletion in `CoreCFGToGotoTransformWF.lean`

**Status:** stub (in-progress)
**Worker:** W6
**Base commit:** `60b647dd5` (W4-final)
**Target file:** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` (7,102 LoC)
**Predecessor audit:** [`W5_unused_lemmas_audit.md`](./W5_unused_lemmas_audit.md)

## Plan

W5 identified 14 dead lemmas (~408 LoC) plus a `PartialWellFormedTranslation`
structure (~80 LoC) that becomes deletable once its sole constructor goes.
W6 applies the deletions in 5 passes, building between each:

| Pass | Group | Candidates | Est. LoC |
|------|-------|------------|---------:|
| A | emit-shape orphans | `patchGotoTargets_preserves_T`, `instrAt_of_push_lt`, `emitUncondGoto_preserves_size_eq`, `endFunction_emit_preserves_size_eq` | 54 |
| B | innerCmdLoop fold survivors | `innerCmdLoop_preserves_size_eq`, `innerCmdLoop_preserves_locationNum_eq_index`, `innerCmdLoop_nextLoc_advance` | 182 |
| C | labelMap/hashMap helpers | `labelMapInsert_preserves_inj`, `labelMapInsert_preserves_lt`, `hashMapToLabelMap_insert` | 80 |
| D | PartialWellFormedTranslation block | `partialWellFormedTranslation_initial` + structure | ~115 |
| E | patches predicates + subset | `PendingPatchesIndicesDistinct`, `PendingPatchesIndicesBounded`, `patchesFoldlM_no_contracts_resolvedPatches_indices_subset` | 58 |

Target: ~408–488 LoC removed. Tier-1 threshold: ≥350 LoC.

## Pre-flight verification (W4 line-shift check)

W4 changed 3 LoC. Re-grepped each W5 candidate; all 14 still have **0
external uses** and **1 in-file occurrence** (the declaration site itself).
Slight line shifts vs W5's audit (none breaking):

- `labelMapInsert_preserves_lt`: 2319 → 2318 (−1, W4 dropped `h_fresh_dom`)
- `hashMapToLabelMap_insert`: 2364 → 2363 (−1)
- `PendingPatchesIndicesDistinct`: 5785 → 5782 (−3)
- `PendingPatchesIndicesBounded`: 5789 → 5786 (−3)
- `patchesFoldlM_no_contracts_resolvedPatches_indices_subset`: 6272 → 6269 (−3)

`PartialWellFormedTranslation` references confined to its own block
(L980/L996/L1003/L1029/L1040/L1055), confirming external-zero from W5.

Baseline `lake build` green; `_v6`/`_v7` axioms = `[propext, Classical.choice, Quot.sound]`.

## Per-pass results

To be filled in as each pass lands.
