# A1 — Split & Cleanup of `CoreCFGToGotoTransformWF.lean`

**Status:** final
**Worker:** A1
**Base commit:** `a012a1c01` (W6-final)
**Target file:** `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean` (originally 6,665 LoC)
**Predecessors:** W4 (params), W5 (audit), W6 (deletion = 437 LoC), L3 (combinator).

## TL;DR

- **Tier 2.** Every Lean file in `Strata/Backends/CBMC/GOTO/` is now ≤ 1.5k LoC.
- 6 split files created under `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF/`.
- Main `CoreCFGToGotoTransformWF.lean` shrunk from **6,665 → 142** LoC
  (the strengthened theorem only).
- Public API of `coreCFGToGotoTransform_wellFormed_strengthened`,
  `_decompose`, `_wellFormed_nonempty`, `coreCFGToGotoInitState`,
  `wellFormedTranslation_of_shadow`, `CoreCFGToGotoTransformShadow`
  preserved.
- `lake build` green at every commit (235 jobs, 585 in full repo).
- `_v6` / `_v7` still depend on `[propext, Classical.choice, Quot.sound]`.
- One `private` annotation dropped (`foldl_gotoInstrCount_extract_acc`)
  to allow cross-file reference.

## Pre-state

| File | LoC |
|---|---:|
| `CoreCFGToGotoTransformWF.lean` | 6,665 |
| `ExprTranslationPreservesEvalBoolInt.lean` | 1,527 (out of scope) |
| `PcInversion.lean` | 1,400 |
| `CoreCFGToGOTOConcrete.lean` | 1,376 |
| Total in `Strata/Backends/CBMC/GOTO/` | 22,633 |

`ExprTranslationPreservesEvalBoolInt.lean` (1,527) is not the target
of this task — the brief restricts work to `CoreCFGToGotoTransformWF.lean`
and any new split files created under it.

## Approach

Given:
- W6 already harvested 437 LoC of dead lemmas.
- L3 declined the `size_eq` chain combinator (Class C, structural mismatch).
- W4 confirmed remaining hypotheses are largely load-bearing.

The viable lever was **splits**, not cleanup. Goal: chop the 6,665 LoC
WF file into ≤ 1.5k chunks while preserving public API.

## Splits

Created 6 new files under `Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF/`,
arranged in a strict dependency chain (each importing the previous):

```
Shape.lean
  └─ Preservation.lean
       └─ StepPreservation.lean
            └─ FoldAndDecompose.lean
                 └─ BlockBodyClosures.lean
                      └─ CondGotoClosures.lean
                           └─ CoreCFGToGotoTransformWF.lean  (main, top-level theorem)
```

### Pass 1 — `Shape.lean` (941 LoC)

Per-Cmd shape lemmas (`Cmd_toGotoInstructions_*_ok`), emit-helper shape
lemmas (`emitLabel_shape`, `emitCondGoto_shape`, `emitUncondGoto_shape`),
`patchGotoTargets` invariants (`_preserves_size`, `_preserves_nextLoc`),
instruction-array lookup helpers (`instrAt_of_push`, `instrAt_of_append_two`),
per-Cmd `CmdEmittedAt` builders (`cmdEmittedAt_*`), and the dispatcher
(`cmdEmittedAt_of_toGotoInstructions`). 28 declarations.

* Commit `16645332d`.
* Main: 6,665 → 5,757 LoC.

### Pass 2 — `Preservation.lean` (1,023 LoC)

Per-emit/Cmd/patcher size_eq + locationNum_eq_index preservation,
the `innerCmdLoop` shadow, `toGotoInstructions` monotonicity
(`_size_le`, `_instructions_prefix?`), `innerCmdLoop_size_le`,
`innerCmdLoop_instructions_prefix?`, `toGotoInstructions_nextLoc_advance`,
`innerCmdLoop_layout_block_body`. 18 declarations.

* Commit `322e462ac`.
* Required dropping `private` from `foldl_gotoInstrCount_extract_acc`
  (used by `cmdsFoldlM_nextLoc_advance` in `StepPreservation`).
* Main: 5,757 → 4,765 LoC.

### Pass 3 — `StepPreservation.lean` (1,290 LoC)

LabelMap operations (`emptyLabelMap`, `labelMapInsert`,
`hashMapToLabelMap`), per-cmd / per-block step preservation
(`coreCFGToGotoCmdStep_*`, `cmdsFoldlM_*`, `coreCFGToGotoBlockStep_*`),
per-block step instruction-array prefix (`_size_le`, `_instructions_prefix?`),
and per-block step layout post-conditions
(`_location_at_pc`, `_location_at_pc_with_labels`, `_finish_at_pc`,
`_condGoto_at_pc`). 25 declarations.

* Commit `8cb7fefe0`.
* Main: 4,765 → 3,506 LoC.

### Pass 4 — `FoldAndDecompose.lean` (1,192 LoC)

Outer-loop fold layout-fact preservation (`blocksFoldlM_size_le`,
`blocksFoldlM_instructions_prefix?`), `BlockLabelsDistinct` and
related lemmas, layout-fact propagation through `blocksFoldlM`
(`_layout_location`, `_layout_location_with_labels`, `_layout_finish`),
`blocksFoldlM_preserves_size_eq` and `_preserves_locationNum_eq_index`,
patch-step preservation under empty loopContracts
(`coreCFGToGotoPatchStep_*`, `patchesFoldlM_*`), structural
soundness (`coreCFGToGotoTransform_size_eq_and_loc`), translator
decomposition (`coreCFGToGotoInitState`,
`coreCFGToGotoTransform_decompose`,
`coreCFGToGotoTransform_size_eq_and_loc_direct`), the
`CoreCFGToGotoTransformShadow` structure +
`wellFormedTranslation_of_shadow`, and the top-level
`coreCFGToGotoTransform_wellFormed_nonempty` theorem. 24 declarations.

* Commit `9ab2906aa`.
* Main: 3,506 → 2,347 LoC.

### Pass 5 — `BlockBodyClosures.lean` (862 LoC)

Closure helpers for hypothesis-parameter fields of
`_wellFormed_nonempty`: `entry_in_map_of_translator`,
`labelMapBoundedAndInj` + supporting lemmas,
`labelMap_inj_of_translator`, `cmdsFoldlM_eq_innerCmdLoop_on_admitted`,
`coreCFGToGotoBlockStep_layout_block_body`,
`blocksFoldlM_layout_block_body`, the patcher's "preserves full
instruction except target" lemmas, and
`layout_block_body_of_translator`. 12 declarations.

* Commit `026a7ea1c`.
* Main: 2,347 → 1,521 LoC (just barely over 1.5k; final pass clears it).

### Pass 6 — `CondGotoClosures.lean` (1,412 LoC)

`layout_cond_goto_of_translator` and
`layout_cond_goto_guards_of_translator` along with their full
support stack: patcher post-conditions
(`patch_one_target_eq`, `patch_foldl_target_*`,
`patchGotoTargets_target_at_patched_idx`), pendingPatches tracking
across the block fold, patches-fold correctness lemmas
(`patchesFoldlM_no_contracts_resolvedPatches_*`), pendingPatches
index distinctness lemmas, lookup-success on patchStep, lifted
`blocksFoldlM_layout_cond_goto_pre_patch`, top-level closures
(`coreCFGToGotoInitState_pendingPatches_distinct/_bounded`),
patcher guard preservation, and the guards-of-translator closure.
28 declarations.

* Commit `ef35b753a`.
* Main: 1,521 → 142 LoC.

## Post-state

| File | LoC | Δ vs baseline |
|---|---:|---|
| `CoreCFGToGotoTransformWF.lean` | **142** | -6,523 (was 6,665) |
| `WF/Shape.lean` | **941** | new |
| `WF/Preservation.lean` | **1,023** | new |
| `WF/StepPreservation.lean` | **1,290** | new |
| `WF/FoldAndDecompose.lean` | **1,192** | new |
| `WF/BlockBodyClosures.lean` | **862** | new |
| `WF/CondGotoClosures.lean` | **1,412** | new |
| **WF total** | **6,862** | +197 (preamble overhead) |

Every WF file is ≤ 1.5k LoC. The largest, `CondGotoClosures.lean`
at 1,412 LoC, has 88 LoC of headroom against the 1.5k target.

(Outside of scope: `ExprTranslationPreservesEvalBoolInt.lean` remains
at 1,527 LoC, slightly over 1.5k; the brief restricted work to the
WF file and its splits.)

## Cleanup

Limited net cleanup — primarily one private-annotation drop to
enable cross-file reference (necessary for the split). No dead
code removal beyond what W6 already harvested. The 197-LoC overhead
across new files is from per-file `module` preamble +
`namespace`/`section`/`end` boilerplate (~30 LoC × 6 files +
header copy).

## Verification

* `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF` — green.
* `lake build Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete` — green (233 jobs).
* `lake build` (full) — green (585 jobs).
* `#print axioms` of `_v6` and `_v7`:
  ```
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6 depends on axioms:
    [propext, Classical.choice, Quot.sound]
  CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v7 depends on axioms:
    [propext, Classical.choice, Quot.sound]
  ```
  Identical to baseline.
* No new `axiom`, `sorry`, or `admit`.
* Public theorem signatures (`_strengthened`, `_decompose`,
  `_wellFormed_nonempty`, `coreCFGToGotoInitState`,
  `wellFormedTranslation_of_shadow`, `CoreCFGToGotoTransformShadow`)
  unchanged.
* No consumer files outside the WF module touched. Existing imports
  of `Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF`
  (in `BlocksFoldClosed`, `CoreCFGToGOTOConcrete`,
  `GotoTargetProvenance`, `PcInversion`, `NoDead`, `WfLabelMapAgree`)
  still resolve correctly thanks to the public re-import chain in
  the main WF file.

## Tier verdict

**Tier 2.** Every file ≤ 1.5k LoC, achieved primarily via splits.
Cleanup contribution: minimal (a single `private` removed). The
splits required no proof changes — every theorem was moved
verbatim with its surrounding documentation.

## Commits

```
ffe2faca0 docs(A1): stub plan
16645332d split(A1): WF Pass 1 - Shape.lean (941 LoC)
322e462ac split(A1): WF Pass 2 - Preservation.lean (1023 LoC)
8cb7fefe0 split(A1): WF Pass 3 - StepPreservation.lean (1290 LoC)
9ab2906aa split(A1): WF Pass 4 - FoldAndDecompose.lean (1192 LoC)
026a7ea1c split(A1): WF Pass 5 - BlockBodyClosures.lean (862 LoC)
ef35b753a split(A1): WF Pass 6 - CondGotoClosures.lean (1412 LoC)
```

## Notes for follow-up workers

The chosen split boundaries align with natural section breaks in the
original file. A future cleanup pass could target:

* The single-caller lemmas in `Shape.lean` (e.g., the per-shape
  driver pairs `*_of_toGotoInstructions` are each used only by
  the dispatcher `cmdEmittedAt_of_toGotoInstructions`; inlining
  could save ~80 LoC but at significant readability cost).
* The patch-fold lemma family in `CondGotoClosures.lean` —
  `patch_foldl_target_*` is a chain of 4 private helpers that
  could be folded into the single public `patchGotoTargets_target_at_patched_idx`
  with `induction` on the proof, saving ~40-60 LoC.
* `CondGotoClosures.lean` at 1,412 LoC is the closest to the limit.
  A further split could move the `coreCFGToGotoBlockStep_pendingPatches_*`
  family (lines ~250-700 in CondGotoClosures) to its own file
  if more headroom is needed.
