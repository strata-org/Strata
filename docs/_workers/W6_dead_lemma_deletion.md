# W6: Dead-Lemma Deletion in `CoreCFGToGotoTransformWF.lean`

**Status:** final
**Worker:** W6
**Base commit:** `60b647dd5` (W4-final)
**Target file:** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`
**Predecessor audit:** [`W5_unused_lemmas_audit.md`](./W5_unused_lemmas_audit.md)

## TL;DR

- **Tier 1.** 437 LoC saved (7,102 → 6,665, a 6.2% reduction).
- All 14 of W5's `safe-to-delete` candidates were genuinely dead and
  deleted without any build breakage.
- The `PartialWellFormedTranslation` structure (W5's bonus target) was
  also dead — both the structure and its sole constructor
  `partialWellFormedTranslation_initial` are gone.
- `lake build` green at every commit. Public API of
  `coreCFGToGotoTransform_wellFormed_strengthened`,
  `coreCFGToGotoTransform_decompose`,
  `wellFormedTranslation_of_shadow`, and `CoreCFGToGotoTransformShadow`
  unchanged (verified via `#check`).
- `_v6` / `_v7` axioms still `[propext, Classical.choice, Quot.sound]`.

## Pre-flight verification (W4 line-shift check)

W4 changed 3 LoC across 3 commits. I re-grepped each W5 candidate
before touching the file:

| Candidate | External uses | In-file uses | Status |
|-----------|--------------:|-------------:|:------:|
| `patchGotoTargets_preserves_T` | 0 | 1 | dead |
| `instrAt_of_push_lt` | 0 | 1 | dead |
| `partialWellFormedTranslation_initial` | 0 | 1 | dead |
| `emitUncondGoto_preserves_size_eq` | 0 | 1 | dead |
| `endFunction_emit_preserves_size_eq` | 0 | 1 | dead |
| `innerCmdLoop_preserves_size_eq` | 0 | 1 | dead |
| `innerCmdLoop_preserves_locationNum_eq_index` | 0 | 1 | dead |
| `innerCmdLoop_nextLoc_advance` | 0 | 1 | dead |
| `labelMapInsert_preserves_inj` | 0 | 1 | dead |
| `labelMapInsert_preserves_lt` | 0 | 1 | dead |
| `hashMapToLabelMap_insert` | 0 | 1 | dead |
| `PendingPatchesIndicesDistinct` | 0 | 1 | dead |
| `PendingPatchesIndicesBounded` | 0 | 1 | dead |
| `patchesFoldlM_no_contracts_resolvedPatches_indices_subset` | 0 | 1 | dead |
| `PartialWellFormedTranslation` (struct) | 0 | confined to its own block | dead |

All confirmed dead. Slight line shifts vs W5's audit (none breaking):

- `labelMapInsert_preserves_lt`: 2319 → 2318 (W4 dropped `h_fresh_dom`)
- `hashMapToLabelMap_insert`: 2364 → 2363
- `PendingPatchesIndicesDistinct`: 5785 → 5782
- `PendingPatchesIndicesBounded`: 5789 → 5786
- `patchesFoldlM_no_contracts_resolvedPatches_indices_subset`: 6272 → 6269

Baseline `lake build` green; baseline `_v6`/`_v7` axioms recorded as
`[propext, Classical.choice, Quot.sound]`.

## Per-pass results

### Pass A — emit-shape orphans (4 lemmas, 42 LoC)

| Candidate | Result |
|---|---|
| `patchGotoTargets_preserves_T` | deleted |
| `instrAt_of_push_lt` | deleted |
| `emitUncondGoto_preserves_size_eq` | deleted |
| `endFunction_emit_preserves_size_eq` | deleted |

`lake build` green. Commit `eab3ad260`. File: 7,102 → 7,060 LoC.

### Pass B — innerCmdLoop fold survivors (3 lemmas, 180 LoC)

| Candidate | Result |
|---|---|
| `innerCmdLoop_preserves_size_eq` | deleted |
| `innerCmdLoop_preserves_locationNum_eq_index` | deleted |
| `innerCmdLoop_nextLoc_advance` | deleted (107 LoC, the largest dead lemma in the file) |

`lake build` green. Commit `8f420e82e`. File: 7,060 → 6,880 LoC.

### Pass C — labelMap/hashMap helpers (3 lemmas, 66 LoC)

| Candidate | Result |
|---|---|
| `labelMapInsert_preserves_inj` | deleted |
| `labelMapInsert_preserves_lt` | deleted |
| `hashMapToLabelMap_insert` | deleted |

The `@[simp]` siblings `labelMapInsert_self`, `labelMapInsert_other`,
and `hashMapToLabelMap_empty` were preserved (W5's `keep` list).

`lake build` green. Commit `febb06954`. File: 6,880 → 6,814 LoC.

### Pass D — PartialWellFormedTranslation block (88 LoC)

| Candidate | Result |
|---|---|
| `partialWellFormedTranslation_initial` (constructor) | deleted |
| `structure PartialWellFormedTranslation` | deleted |
| Surrounding doc-comment blocks (`/-! ## Loop invariant ...`, `/-! ## Initial-state ...`) | deleted |

`emptyLabelMap` was **kept** — it is referenced at L1991/L1993 by the
`@[simp] hashMapToLabelMap_empty` lemma (which is on W5's `keep` list).

`lake build` green. Commit `1ef34747f`. File: 6,814 → 6,726 LoC.

### Pass E — pending-patches predicates + subset lemma (61 LoC)

| Candidate | Result |
|---|---|
| `PendingPatchesIndicesDistinct` | deleted |
| `PendingPatchesIndicesBounded` | deleted |
| `patchesFoldlM_no_contracts_resolvedPatches_indices_subset` | deleted (also removed its 6-line doc-section header `/-! ### resolvedPatches index distinctness`, which had only this one lemma underneath) |

`lake build` green. Commit `fe3d080ef`. File: 6,726 → 6,665 LoC.

## Verification

- `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF` — green at every commit.
- `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` — green (227 jobs).
- `lake build` (full) — green (585 jobs).
- `#print axioms` of `_v6` and `_v7` after Pass E:
  ```
  'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6' depends on axioms:
   [propext, Classical.choice, Quot.sound]
  'CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7' depends on axioms:
   [propext, Classical.choice, Quot.sound]
  ```
  Identical to baseline.
- `#check` of `coreCFGToGotoTransform_wellFormed_strengthened` and
  `coreCFGToGotoTransform_decompose` — public signatures byte-identical
  to baseline.
- No new `axiom`, `sorry`, or `admit`.

## Totals

| Pass | Candidates | LoC removed | Cum. file LoC |
|------|-----------:|------------:|-----:|
| baseline | — | — | 7,102 |
| A | 4 | 42 | 7,060 |
| B | 3 | 180 | 6,880 |
| C | 3 | 66 | 6,814 |
| D | 2 (struct + ctor) | 88 | 6,726 |
| E | 3 | 61 | 6,665 |
| **total** | **15 named decls (14 lemmas + 1 struct)** | **437** | **−6.2%** |

W5 projected ~408–488 LoC (lemmas + bonus struct removal). Actual:
**437 LoC**, near the middle of that range. The slight offset from
the lemma-only sum (408) comes from also removing the structure
(~80 LoC budgeted by W5) and from incidental doc-comment stripping
where a deletion left a one-liner section header with no surviving
content beneath it.

## Tier verdict

**Tier 1.** 437 LoC ≥ 350 LoC threshold. The audit was thorough; every
W5 candidate was genuinely dead, no surprises, and the projected
ceiling was met within ~10% of the prediction.

## Commits

```
cafd5706c docs(W6): stub plan
eab3ad260 cleanup(W6): Pass A — emit-shape orphans (4 lemmas, 42 LoC)
8f420e82e cleanup(W6): Pass B — innerCmdLoop fold survivors (3 lemmas, 180 LoC)
febb06954 cleanup(W6): Pass C — labelMap/hashMap helpers (3 lemmas, 66 LoC)
1ef34747f cleanup(W6): Pass D — PartialWellFormedTranslation block (struct + ctor, 88 LoC)
fe3d080ef cleanup(W6): Pass E — pending-patches predicates + subset lemma (61 LoC)
                                                                       total = 437 LoC
```
