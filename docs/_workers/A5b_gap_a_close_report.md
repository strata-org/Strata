# A5b Worker Report — Closing `layout_cond_goto` and `layout_cond_goto_guards`

## Status: Tier 1 — Best (both target hypotheses closed)

## Goal

Close two of A4's open hypotheses on
`coreCFGToGotoTransform_wellFormed_nonempty`:
1. `layout_cond_goto` — every `.condGoto` block emits two GOTO
   instructions at the right pcs with the right targets *after
   patching*.
2. `layout_cond_goto_guards` — those two GOTO guards have shape
   `e_goto.not` and `Expr.true`.

## What Was Delivered

Two top-level closure theorems, both proven without `sorry`:

* **`layout_cond_goto_of_translator`** — discharges
  `h_layout_cond_goto`. Produces the existence of `pc_lf, pc_lt,
  instr_neg, instr_uncond` with:
  * `ans.instructions[pc + 1 + bodyCount]? = some instr_neg`
  * `instr_neg.type = .GOTO ∧ instr_neg.target = some pc_lf`
  * `hashMapToLabelMap st_final.labelMap lf = some pc_lf`
  * symmetric for `instr_uncond` and `lt`.

* **`layout_cond_goto_guards_of_translator`** — discharges
  `h_layout_cond_goto_guards`. Produces the existence of `e_goto`
  with:
  * `instr_neg.guard = e_goto.not`
  * `ExprTranslated δ δ_goto δ_goto_bool cond e_goto`
  * `instr_uncond.guard = CProverGOTO.Expr.true`

Both theorems use only the standard axiom set
`[propext, Classical.choice, Quot.sound]`, verified via
`#print axioms`.

## Lemmas Delivered (in commit order)

### Patcher post-condition (the crux for layout_cond_goto)

* `patch_one_target_eq` and `patch_one_target` — single-patch
  `set!` produces `target = some tgt` at the patched index.
* `patch_one_preserves_size` and `patch_foldl_preserves_size` —
  array size is preserved by patches.
* `patch_one_other_index` — patches at index `idx` don't affect
  other indices.
* `patch_foldl_target_preserved_when_idx_unique_in_tail` — patcher
  preserves `target = some tgt` at `idx` when no later patch
  shares that index.
* `patch_foldl_target_head` — patcher applied to `(idx, tgt) :: rest`
  with no later index match yields `target = some tgt` at `idx`.
* `patch_foldl_target_at_idx_when_last` — patcher's "last
  occurrence wins" formulation.
* **`patchGotoTargets_target_at_patched_idx`** — main patcher
  post-condition: under unique-indices `patches`,
  `(idx, tgt) ∈ patches ∧ idx < array.size`
  implies the patched array at `idx` has `target = some tgt`.

### pendingPatches tracking through blocksFoldlM

* `coreCFGToGotoBlockStep_pendingPatches_preserves` and
  `blocksFoldlM_pendingPatches_preserves` — the foldlM preserves
  pendingPatches membership.
* `coreCFGToGotoBlockStep_condGoto_pendingPatches` — for a
  `.condGoto` block, the per-block step pushes the two patches
  `(pc + 1 + bodyCount, lf)` and `(pc + 1 + bodyCount + 1, lt)`.

### pendingPatches index bounds + distinctness

* `coreCFGToGotoBlockStep_pendingPatches_indices_bound` and
  `blocksFoldlM_pendingPatches_indices_bound` — pendingPatches
  indices stay `< instructions.size`.
* `coreCFGToGotoBlockStep_pendingPatches_indices_distinct` and
  `blocksFoldlM_pendingPatches_indices_distinct` — pendingPatches
  indices stay pairwise distinct (under bounded indices).

### Patches fold under empty contracts

* `coreCFGToGotoPatchStep_no_contracts_resolvedPatches` — per-step
  shape: `acc'.1 = (idx, targetLoc) :: acc.1`.
* `patchesFoldlM_no_contracts_step_subset` and
  `patchesFoldlM_no_contracts_resolvedPatches_subset` — fold
  preserves input resolvedPatches.
* `patchesFoldlM_no_contracts_resolvedPatches_mem` — every input
  pendingPatch `(idx, label)` produces `(idx, targetLoc)` in
  resolvedPatches (where `targetLoc = labelMap[label]?`).
* `patchesFoldlM_no_contracts_resolvedPatches_indices_subset` —
  resolvedPatches indices are a subset of pendingPatches' indices.
* `coreCFGToGotoPatchStep_success_lookup` and
  `patchesFoldlM_success_all_lookups` — fold success implies
  every pendingPatch's label has a labelMap entry.
* `patchesFoldlM_no_contracts_resolvedPatches_pairwise_distinct` —
  resolvedPatches inherits index-distinctness from pendingPatches.

### Lifted condGoto layout

* **`blocksFoldlM_layout_cond_goto_pre_patch`** — lifts
  `coreCFGToGotoBlockStep_condGoto_at_pc` across the foldlM, also
  threading pendingPatches membership.

### Patcher preserves guard

* `patch_one_preserves_guard` and **`patchGotoTargets_preserves_guard`**
  — analogue of `patchGotoTargets_preserves_type` for the `guard`
  field.

### Initial state hypotheses

* `coreCFGToGotoInitState_pendingPatches_distinct` and
  `coreCFGToGotoInitState_pendingPatches_bounded` — vacuous
  invariants for the empty initial pendingPatches.

### Top-level closures

* **`layout_cond_goto_of_translator`** (Tier 1).
* **`layout_cond_goto_guards_of_translator`** (Tier 1).

## File Growth

`Strata/Backends/CBMC/GOTO/CoreCFGToGotoTransformWF.lean`:
4549 → ~5550 LoC (+~1000 LoC).

## Verification

* `lake build` green at every commit.
* All 585 jobs build successfully.
* `FinishPlacementProbe` passes.
* `SemanticsTests` passes; `coreCFGToGoto_forward_simulation` axioms
  unchanged: `[propext, Classical.choice, Quot.sound]`.
* Both new closure theorems verified via `#print axioms` to use only
  the standard axiom set.
* E2E tests `E2E_CFGPipeline` and `E2E_CoreToGOTO` build green.
* 6 commits over the round (5 feat + 1 doc + report).

## Technical Notes

* The patcher post-condition is the crux; it requires careful
  handling of `set!` (which uses `setIfInBounds`) and pairwise
  distinctness of patch indices to avoid later patches overwriting
  earlier ones.
* pendingPatches indices are pairwise distinct because each block
  step pushes patches at strictly increasing indices (since
  `nextLoc` only grows).
* resolvedPatches inherit distinctness via the per-step prepend
  `(idx, targetLoc) :: acc.1` shape under empty contracts.
* `match`/`cases` on `labelMap[label]?` substitutes the
  discriminant in the goal; this caused some pain. Workaround: use
  `by_cases` on `(labelMap[label]?).isSome` then
  `Option.isSome_iff_exists.mp`.
* For the `Pairwise` of two-element list `[X] ++ [Y]`,
  `List.pairwise_append` plus `List.pairwise_singleton` works
  cleanly.

## Working Notes

* Started 2026-05-21.
* Worktree:
  `/Users/htd/Documents/Strata/.claude/worktrees/agent-a227fca902cfa5de2`
* Branch: `worktree-agent-a227fca902cfa5de2` (off
  `htd/unstructured-to-goto`).
* 7 commits over the round: 1 stub + 5 feat + 1 final report.
* All proofs added at the END of the file under section header
  `/-! ## A5b: layout_cond_goto + guards -/` to coexist cleanly
  with A5a's parallel work.

## Disjoint-Scope Discipline

* A5a's insertions are expected between A4's existing theorem and
  the closing `end -- public section`. A5b's insertions are AFTER
  A5a's, also before `end -- public section`. Both worker outputs
  can be merged without conflicts.
* I did NOT modify A4's existing theorem
  `coreCFGToGotoTransform_wellFormed_nonempty` — only added new
  theorems.
* I did NOT touch supervisor docs.

## Remaining for Future Rounds

The two closure theorems take the same hypotheses A4 originally
required (modulo the additional `h_expr_translated_witness` for
guards). To replace A4's `h_layout_cond_goto`/`_guards`
parameters in `coreCFGToGotoTransform_wellFormed_nonempty`, the
supervisor needs to compose:
* `layout_cond_goto_of_translator` with A4's existing input
  hypotheses to discharge `h_layout_cond_goto`.
* `layout_cond_goto_guards_of_translator` for `h_layout_cond_goto_guards`.

A5a is closing `layout_block_body`, `labelMap_inj`, and
`entry_in_map` in parallel. Once both A5a and A5b land, the
supervisor can integrate the closures into a tightened top-level
WF theorem with no hypothesis parameters (modulo
`h_expr_translated_witness`, which itself reduces from caller's
expression-translation correctness — see B3's bool+int bridge).
