# PSA1 — Proof Structure Audit (stub, in-progress)

**Worker:** PSA1 (read-only).
**Branch base:** `htd/unstructured-to-goto` (HEAD `01ac635cc`).
**Scope:** read-only audit of per-theorem LoC distribution, recurring
patterns not yet abstracted, and structural restructuring opportunities
inside `Strata/Backends/CBMC/GOTO/` (root + `CoreCFGToGotoTransformWF/`
subdirectory).

This is a stub — final findings to follow.

## Sections (planned)

1. Per-theorem LoC distribution
2. Recurring patterns not yet abstracted
3. Restructuring opportunities (file layout, predicate shape, theorem
   shape, layering)
4. Verdict (Tier 1 / 2 / 3) and honest assessment

## Files I will inspect in detail

Top of the per-theorem-LoC ranking (already computed, top-50):

* `CoreCFGToGOTOConcrete.lean` — `_v6` (328 LoC) and `_v7` (194 LoC)
  account for **97% of the file**.
* `CoreCFGToGOTOCorrect.lean` — `block_body_cmds_simulation` (264
  LoC), `cfgStepStar_to_gotoStar` (126), `single_cmd_simulation`
  (118), `block_body_simulation` (75), `block_simulation` (61).
* `CoreCFGToGotoTransformWF/FoldAndDecompose.lean` —
  `coreCFGToGotoTransform_wellFormed_nonempty` (226 LoC),
  `coreCFGToGotoTransform_size_eq_and_loc_direct` (127),
  `wellFormedTranslation_of_shadow` (90), `..._decompose` (88).
* `CoreCFGToGotoTransformWF/CondGotoClosures.lean` —
  `layout_cond_goto_of_translator` (184 LoC) and three other 100+ LoC
  theorems.
* `CoreCFGToGotoTransformWF/BlockBodyClosures.lean` —
  `layout_block_body_of_translator` (178),
  `coreCFGToGotoBlockStep_layout_block_body` (169),
  `blocksFoldlM_layout_block_body` (109).
* `CoreCFGToGotoTransformWF/StepPreservation.lean` —
  `coreCFGToGotoBlockStep_condGoto_at_pc` (131),
  `coreCFGToGotoBlockStep_preserves_locationNum_eq_index` (119),
  `coreCFGToGotoBlockStep_instructions_prefix?` (107),
  `coreCFGToGotoBlockStep_location_at_pc_with_labels` (99),
  `coreCFGToGotoBlockStep_finish_at_pc` (70).
* `PcInversion.lean` — five preservation lemmas, each 69-130 LoC.
* `ExprTranslationPreservesEvalBoolInt.lean` — `isBoolIntFragment`
  (236 LoC, `def`), `toGotoExprCtx_preservesEval_boolInt` (235),
  `CoreLExpr` (204 LoC `abbrev`).
* `CoreCFGToGOTOInvariants.lean` — `cmdsPrefixInstrCount` (166 LoC)
  and `LabelMap` (108 LoC) make up **83% of the file**, the rest is
  the `WellFormedTranslation` structure.

Patterns I will hunt for:

* The `coreCFGToGotoBlockStep_*` intro skeleton recurring across ~10
  theorems in `StepPreservation.lean` and ~5 in `FoldAndDecompose.lean`.
* The `_at_pc` vs `_at_pc_with_labels` vs `_finish_at_pc` vs
  `_condGoto_at_pc` family — what survives WF1 pruning?
* The `<chain>_preserves_body_pc_covered` repetition in PcInversion
  (Class E predicate).
* `CmdEmittedAt` constructor wrappers and Cmd-shape dispatch.
* `single_cmd_simulation` 7-arm dispatch — one-shot or repeated?

## Stub commit

This stub will be committed; final findings to follow in the same
file. (Per task spec: stub first, then commit, then final findings.)
