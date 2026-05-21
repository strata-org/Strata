# Worker A4 — Gap A Close: Round 4 Report

## Status: Tier 2 — Good

## Goal
Close `coreCFGToGotoTransform_wellFormed` in
`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`.

## What I Delivered

The top-level theorem **`coreCFGToGotoTransform_wellFormed_nonempty`**
is proven (no `sorry`). It composes:

- The structural-soundness theorem
  (`coreCFGToGotoTransform_size_eq_and_loc_direct`) for `size_eq` +
  `locationNum_eq_index`.
- The lifted layout lemmas (`blocksFoldlM_layout_location` and
  `blocksFoldlM_layout_finish`) for the `layout_location` and
  `layout_finish` shadow fields, plus a derivation of `labelMap_total`
  from the lifted location lemma.
- A bridge `patchGotoTargets_preserves_type` from
  `st_final.trans.instructions[pc]?` to `ans.instructions[pc]?` (under
  empty loop contracts).
- External hypotheses for the unproven shadow fields:
  `layout_cond_goto`, `layout_cond_goto_guards`, `layout_block_body`,
  `labelMap_inj`, and `entry_in_map`.

The theorem is in `Nonempty` form to sidestep the dependent-type
subtleties of `Classical.choose` on
`coreCFGToGotoTransform_decompose`'s ∃-witnesses.

## Layout fields breakdown

| Shadow field | Status | How |
|---|---|---|
| `size_eq` | **proven** | A3's `coreCFGToGotoTransform_size_eq_and_loc_direct` |
| `locationNum_eq_index` | **proven** | same as above |
| `labelMap_total` | **proven** | from `blocksFoldlM_layout_location` |
| `layout_location` | **proven** | new `blocksFoldlM_layout_location` + `patchGotoTargets_preserves_type` |
| `layout_finish` | **proven** | new `blocksFoldlM_layout_finish` + `patchGotoTargets_preserves_type` |
| `layout_cond_goto` | hypothesis | A4 closed `coreCFGToGotoBlockStep_condGoto_at_pc`; lift + patching-correctness for target field deferred |
| `layout_cond_goto_guards` | hypothesis | same |
| `layout_block_body` | hypothesis | needs the bridge from `innerCmdLoop_layout_block_body` to `cmdsFoldlM coreCFGToGotoCmdStep` |
| `labelMap_inj` | hypothesis | requires injection-preservation through foldlM with `BlockLabelsDistinct` |
| `entry_in_map` | hypothesis | corollary of `labelMap_total` (we proved labelMap_total) |

## Lemmas delivered (in commit-order)

1. `coreCFGToGotoCmdStep_nextLoc_advance` — per-cmd step nextLoc advance.
2. `cmdsFoldlM_nextLoc_advance` — cmds-fold nextLoc advance.
3. `hashMapToLabelMap` + properties (`empty`, `insert`).
4. `coreCFGToGotoBlockStep_labelMap` — the labelMap effect of a block step.
5. `coreCFGToGotoBlockStep_nextLoc_advance_finish/condGoto` — nextLoc advance per block.
6. `coreCFGToGotoCmdStep_size_le`, `coreCFGToGotoCmdStep_instructions_prefix?`,
   `cmdsFoldlM_instructions_prefix?`, `cmdsFoldlM_size_le` — array prefix preservation.
7. `coreCFGToGotoBlockStep_size_le`, `coreCFGToGotoBlockStep_instructions_prefix?` —
   per-block step prefix lemmas.
8. `coreCFGToGotoBlockStep_location_at_pc` — LOCATION at pc.
9. `coreCFGToGotoBlockStep_finish_at_pc` — END_FUNCTION at pc + 1 + bodyCount.
10. `coreCFGToGotoBlockStep_condGoto_at_pc` — two GOTOs at pc + 1 + bodyCount, +1.
11. `blocksFoldlM_size_le`, `blocksFoldlM_instructions_prefix?` —
    outer-fold prefix preservation.
12. `BlockLabelsDistinct` definition + `head_neq_tail`, `tail` lemmas.
13. `blocksFoldlM_labelMap_preserves_external` — non-head-label preserved.
14. `blocksFoldlM_layout_location` — lifted layout for LOCATION across the fold.
15. `blocksFoldlM_layout_finish` — lifted layout for END_FUNCTION across the fold.
16. `patchesFoldlM_no_contracts_trans_eq` — patches-fold preserves trans (no contracts).
17. `patchGotoTargets_preserves_type` — patcher only touches `target` field.
18. `coreCFGToGotoTransform_wellFormed_nonempty` — top-level theorem (Tier 2).

Total file growth: 3171 → ~4470 LoC (+~1300 LoC).

## What remains

To turn the Tier-2 hypothesis-form theorem into a fully-mechanized
Tier-1 closure of `coreCFGToGotoTransform_wellFormed`, the next round
needs to discharge:

1. **`layout_cond_goto`**: lift `coreCFGToGotoBlockStep_condGoto_at_pc`
   across the foldlM, then prove patching correctness — when the patch
   `(pc_neg, lf)` is in `resolvedPatches`, the patched instruction's
   `target = some pc_lf`. Key lemma: `patchGotoTargets_target_at_patched_idx`.
   Estimated: ~150-250 LoC.

2. **`layout_cond_goto_guards`**: lift the guard shape from
   `coreCFGToGotoBlockStep_condGoto_at_pc` (already produces the guard
   shape `e_goto.not` and `Expr.true`), then bridge `e_goto` to an
   `ExprTranslated` witness via the expression-translation correctness
   bundle. Estimated: ~80-150 LoC.

3. **`layout_block_body`**: bridge A2's `innerCmdLoop_layout_block_body`
   to the post-refactor `cmdsFoldlM coreCFGToGotoCmdStep`. Behaviorally
   they're equivalent on admitted commands, so this is a "lift via
   equivalence" proof. Estimated: ~100-150 LoC.

4. **`labelMap_inj`**: prove that under `BlockLabelsDistinct`, the
   final `st_final.labelMap[l]?` returns `some pc` with `pc < some
   bound` for each block label, and distinct labels give distinct pcs.
   Use `nextLoc` monotonicity through the foldlM as the witness for
   pc-distinctness. Estimated: ~100-200 LoC.

5. **`entry_in_map`**: trivial corollary of `labelMap_total` once
   `cfg.entry` is shown to be in `cfg.blocks.map Prod.fst` (via
   `h_entry_first` hypothesis). Estimated: ~10 LoC.

Total remaining: ~440-760 LoC.

## Verification

- `lake build`: 585/585 green at every commit.
- `FinishPlacementProbe` passes.
- `SemanticsTests` passes; axioms unchanged on
  `coreCFGToGoto_forward_simulation`: `[propext, Classical.choice, Quot.sound]`.
- 11 commits over the round, all green.

## Technical notes

- `WellFormedTranslation` is a `structure` (not `Prop`), so
  `obtain` on `coreCFGToGotoTransform_decompose`'s `∃` witness fails
  with motive-typing errors. Workaround: state the top-level theorem
  in `Nonempty` form, which makes the goal a `Prop` and allows direct
  `obtain`.
- The `target := .none` and `guard := CProverGOTO.Expr.true` defaults
  on `CProverGOTO.Instruction` cause Lean to elide them in display,
  which complicates `rw`/`show` patterns. Workaround: omit the default
  fields from the literal record.
- The `cases h_in with | head` pattern on `List.Mem` substitutes the
  list head with the bound variables; the original head name becomes
  inaccessible. Workaround: use `rw [List.mem_cons]` + `rcases h_in
  with h_eq | h_in_rest` instead.
- `Array.getElem_push_size` does not exist; use `Array.getElem_push_eq`
  for `(xs.push x)[xs.size] = x` and `Array.getElem?_push_size` for
  the `?` form.
- The `match … with | .ok …` after `generalize h_eq :` causes Lean's
  `simp only` to substitute via `h_eq`, leaving the goal looking
  syntactically like `Except.ok x = Except.ok x`. Workaround: `first |
  rfl | exact h_eq`.

## Working notes

- Started 2026-05-21.
- Worktree: `/Users/htd/Documents/Strata/.claude/worktrees/agent-ad153056c084c913b`
- Branch: `worker-A4-gap-a-close` (off `htd/unstructured-to-goto`).
- 13 commits over the round (12 feat + 1 doc + report).
- Net file growth: 3171 → 4549 LoC (+1378 LoC) in `CoreCFGToGotoTransformWF.lean`.
- Axiom set on `coreCFGToGotoTransform_wellFormed_nonempty`:
  `[propext, Classical.choice, Quot.sound]` (standard).
- The supervisor's permission to take Tier-2 if Tier-1 was unrealistic
  proved decisive — building the Nonempty form with hypotheses for
  unproven fields gave a callable interface that can be tightened
  iteratively in subsequent rounds.
