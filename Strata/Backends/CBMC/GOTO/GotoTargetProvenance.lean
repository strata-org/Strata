/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.GotoTargetInRange
public import Strata.Backends.CBMC.GOTO.BlocksFoldClosed
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # Discharging `EveryGotoTargetIsLabelMapEntry` by translator induction

Round-8a deliverable. Closes R7a's auxiliary hypothesis
`EveryGotoTargetIsLabelMapEntry cfg pgm wf.labelMap` by a structural
induction over `coreCFGToGotoTransform`'s pieces.

## Strategy

`coreCFGToGotoTransform` decomposes as:

1. **Blocks-fold** (`cfg.blocks.foldlM coreCFGToGotoBlockStep`) emits
   instructions including LOCATIONs, DECL/ASSIGN/ASSERT/etc., and GOTO
   instructions for `.condGoto` transfers. **All emitted GOTOs have
   `target = none`** at this stage.
2. **Patches-fold** (`pendingPatches.foldlM coreCFGToGotoPatchStep`)
   resolves each `(idx, label)` pending patch into `(idx, targetLoc)`,
   where `targetLoc = labelMap[label]?`. (Under empty `loopContracts`,
   this leaves `trans` untouched.)
3. **`patchGotoTargets resolved`** writes each `(idx, targetLoc) ∈
   resolved` into `instructions[idx].target := some targetLoc`.

So every emitted GOTO `i` has `target = some t` only if `(i, t) ∈
resolved`, in which case `t = labelMap[label]?` for the original
patch label `label`. Combined with the fact that `pendingPatches` only
contains labels referenced by `.condGoto` transfers (which the patcher
must look up successfully — meaning `label ∈ labelMap.keys`), we get
that `t` is a labelMap value of some block label.

The bridge to `wf.labelMap` is via the assumption that `wf` was
constructed via the strengthened theorem: the WF's labelMap is
`hashMapToLabelMap st_final.labelMap`. This theorem produces the
property keyed by `hashMapToLabelMap st_final.labelMap`; a corollary
in `CoreCFGToGOTOConcrete.lean` performs the bridge for the v4
caller.

## File layout

* **Predicates.** A "no GOTO has `target = some _`" predicate
  preserved through the blocks-fold; a "every GOTO target value is in
  the resolved patches" predicate after the patcher.
* **Patcher reverse-target lemma.** `patchGotoTargets_target_some_in_resolved`:
  if a GOTO at index `pc` has `target = some t` after the patcher and
  the pre-patcher GOTO had `target = none`, then `(pc, t) ∈ resolved`.
* **Blocks-fold preservation.** Through the blocks-fold, every GOTO
  has `target = none`.
* **Top-level theorem.** `everyGotoTargetIsLabelMapEntry_of_translator_translatorMap`
  produces the property keyed by `hashMapToLabelMap st_final.labelMap`.
-/

namespace CProverGOTO.GotoTargetProvenance

open Imperative
open CProverGOTO

/-! ## "No GOTO has target set" predicate

Two equivalent shapes are useful: an array-level predicate
`NoGotoHasTarget'` (which the BlocksFoldClosed combinator consumes) and
the transform-level `NoGotoHasTarget` (legacy public name). They are
linked by definitional unfolding. -/

/-- Array-level: every `GOTO` in `a` has `target = none`. -/
def NoGotoHasTarget' (a : Array CProverGOTO.Instruction) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    a[pc]? = some instr → instr.type = .GOTO → instr.target = none

/-- Transform-level (legacy public name): every `GOTO` in
`trans.instructions` has `target = none`. Held throughout the
blocks-fold (the translator only emits GOTOs with no target; the
patcher fills targets in later). -/
abbrev NoGotoHasTarget (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  NoGotoHasTarget' trans.instructions

/-! ## Push/append safety primitives

Pushing or appending instructions whose targets are `none` (or that
aren't GOTO at all) preserves `NoGotoHasTarget'`. These are the
ingredients to the `BlocksFoldClosed.ofPushSafe` helper. -/

/-- Per-instruction safety predicate: an instruction is safe for
`NoGotoHasTarget'` if it isn't a GOTO with a non-`none` target. The
translator only emits GOTOs with `target = none`, so every leaf-emit
produces a safe instruction. -/
private def IsSafeForNoGotoTarget (instr : CProverGOTO.Instruction) : Prop :=
  instr.type = .GOTO → instr.target = none

private theorem noGotoHasTarget'_push
    (a : Array CProverGOTO.Instruction) (new_instr : Instruction)
    (h : NoGotoHasTarget' a) (h_safe : IsSafeForNoGotoTarget new_instr) :
    NoGotoHasTarget' (a.push new_instr) := by
  intro pc instr h_at h_ty
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_push_lt h_lt] at h_at
    have h' : a[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h_at
    exact h h' h_ty
  · have h_ge : a.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = a.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h_at
      injection h_at with h_at
      subst h_at
      exact h_safe h_ty
    · have h_lt' : a.size < pc := by omega
      have h_oor : (a.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h_at
      exact absurd h_at (by simp)

private theorem noGotoHasTarget'_append_two
    (a : Array CProverGOTO.Instruction) (i₀ i₁ : Instruction)
    (h : NoGotoHasTarget' a)
    (h_safe0 : IsSafeForNoGotoTarget i₀)
    (h_safe1 : IsSafeForNoGotoTarget i₁) :
    NoGotoHasTarget' (a ++ #[i₀, i₁]) := by
  intro pc instr h_at h_ty
  by_cases h_lt : pc < a.size
  · rw [Array.getElem?_append_left h_lt] at h_at
    exact h h_at h_ty
  · have h_ge : a.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : pc = a.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h_at
      simp at h_at
      subst h_at
      exact h_safe0 h_ty
    · by_cases h_eq1 : pc = a.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h_at
        simp at h_at
        subst h_at
        exact h_safe1 h_ty
      · have h_oor : (a ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h_at
        exact absurd h_at (by simp)

/-! ## `BlocksFoldClosed` instance for `NoGotoHasTarget'`

Every leaf emit pushes either:
* a non-GOTO instruction (DECL, ASSIGN, ASSERT, ASSUME, FUNCTION_CALL,
  LOCATION, END_FUNCTION) — vacuously safe; or
* a GOTO with `target = none` (`emitCondGoto`, `emitUncondGoto`).

But the per-type vocabulary facts in `ofPushSafe` only see the type,
not the GOTO's target. The trick: for non-GOTO types, `IsSafeForNoGotoTarget`
is vacuously true; for GOTO, we'd need the target-is-none fact, which
isn't visible to type-only vocabulary. So we don't use `ofPushSafe`
directly — instead we provide the GOTO closures by hand, since they
naturally know `target = none`. The non-GOTO leaves can still be
discharged via push/append using the type-non-GOTO vocabulary. -/

instance instBlocksFoldClosed_NoGotoHasTarget' :
    BlocksFoldClosed NoGotoHasTarget' where
  toGotoInstructions T fname c trans ans h_run h := by
    show NoGotoHasTarget' ans.instructions
    cases c with
    | init v ty initVal md =>
      cases initVal with
      | det e =>
        obtain ⟨_gty, _e_goto, i_decl, i_assn,
                _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
          Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
        rw [h_inst]
        have h_eq : trans.instructions.append #[i_decl, i_assn]
                  = trans.instructions ++ #[i_decl, i_assn] := rfl
        rw [h_eq]
        have h_safe0 : IsSafeForNoGotoTarget i_decl := fun h' => by
          rw [h_decl_ty] at h'; exact (InstructionType.noConfusion h')
        have h_safe1 : IsSafeForNoGotoTarget i_assn := fun h' => by
          rw [h_assn_ty] at h'; exact (InstructionType.noConfusion h')
        intro pc instr h_at h_ty
        exact noGotoHasTarget'_append_two trans.instructions i_decl i_assn h
          h_safe0 h_safe1 h_at h_ty
      | nondet =>
        obtain ⟨_gty, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
          Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
        rw [h_inst]
        exact noGotoHasTarget'_push trans.instructions i_decl h
          (fun h' => by rw [h_decl_ty] at h'; exact (InstructionType.noConfusion h'))
    | set v src md =>
      cases src with
      | det e =>
        obtain ⟨_gty, _e_goto, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
          Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
        rw [h_inst]
        exact noGotoHasTarget'_push trans.instructions i_assn h
          (fun h' => by rw [h_assn_ty] at h'; exact (InstructionType.noConfusion h'))
      | nondet =>
        obtain ⟨_gty, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
          Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
        rw [h_inst]
        exact noGotoHasTarget'_push trans.instructions i_assn h
          (fun h' => by rw [h_assn_ty] at h'; exact (InstructionType.noConfusion h'))
    | assert label e md =>
      obtain ⟨_e_goto, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
      rw [h_inst]
      exact noGotoHasTarget'_push trans.instructions i h
        (fun h' => by rw [h_assert_ty] at h'; exact (InstructionType.noConfusion h'))
    | assume label e md =>
      obtain ⟨_e_goto, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
      rw [h_inst]
      exact noGotoHasTarget'_push trans.instructions i h
        (fun h' => by rw [h_assume_ty] at h'; exact (InstructionType.noConfusion h'))
    | cover label e md =>
      unfold Imperative.Cmd.toGotoInstructions at h_run
      simp only at h_run
      match h_expr :
          Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
      | .ok e_goto =>
        simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
        injection h_run with h_run
        subst h_run
        let assert_inst : CProverGOTO.Instruction :=
          { type := .ASSERT, locationNum := trans.nextLoc,
            sourceLoc := metadataToSourceLoc md fname trans.sourceText
              (comment := md.getPropertySummary.getD s!"cover {label}"),
            guard := e_goto }
        show NoGotoHasTarget' (trans.instructions.push assert_inst)
        exact noGotoHasTarget'_push trans.instructions assert_inst h
          (fun h_eq => by
            have : InstructionType.ASSERT = InstructionType.GOTO := h_eq
            cases this)
      | .error _ =>
        simp [h_expr, Bind.bind, Except.bind] at h_run
  cmdStep_call fname cmd trans ans h_call h_run h := by
    obtain ⟨procName, callArgs, md, h_eq⟩ := h_call
    subst h_eq
    -- The .call branch pushes a single FUNCTION_CALL.
    unfold Strata.coreCFGToGotoCmdStep at h_run
    simp only at h_run
    generalize h_args :
        (Core.CallArg.getInputExprs callArgs).mapM
          (Lambda.LExpr.toGotoExprCtx
            (TBase := ⟨Core.ExpressionMetadata, Unit⟩) []) = argRes at h_run
    match argRes, h_args with
    | .ok argExprs, _ =>
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      rw [← h_run]
      apply noGotoHasTarget'_push _ _ h
      intro h_eq
      -- The pushed FUNCTION_CALL instruction's type ≠ GOTO.
      have : InstructionType.FUNCTION_CALL = InstructionType.GOTO := h_eq
      cases this
    | .error _, _ =>
      simp [Bind.bind, Except.bind] at h_run
  emitLabel label srcLoc trans h := by
    -- emitLabel pushes a LOCATION instruction.
    let new_instr : CProverGOTO.Instruction :=
      { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        labels := [label], code := Code.skip }
    show NoGotoHasTarget' (trans.instructions.push new_instr)
    exact noGotoHasTarget'_push trans.instructions new_instr h
      (fun h_eq => by
        have : InstructionType.LOCATION = InstructionType.GOTO := h_eq
        cases this)
  emitCondGoto guard srcLoc trans h := by
    -- emitCondGoto pushes a GOTO with target := none.
    let new_instr : CProverGOTO.Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := guard, target := none }
    show NoGotoHasTarget' (trans.instructions.push new_instr)
    exact noGotoHasTarget'_push trans.instructions new_instr h (fun _ => rfl)
  emitUncondGoto srcLoc trans h := by
    -- emitUncondGoto pushes a GOTO with guard := true, target := none.
    let new_instr : CProverGOTO.Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := Expr.true, target := none }
    show NoGotoHasTarget' (trans.instructions.push new_instr)
    exact noGotoHasTarget'_push trans.instructions new_instr h (fun _ => rfl)
  endFunctionEmit md fname trans h := by
    apply noGotoHasTarget'_push _ _ h
    intro h_eq
    unfold endFunctionInstr at h_eq
    have : InstructionType.END_FUNCTION = InstructionType.GOTO := h_eq
    cases this

/-! ## Preservation through the patches-fold (no-contracts case)

Under empty `loopContracts`, the patch step is a no-op on `trans`
(per A4's `coreCFGToGotoPatchStep_no_contracts_trans_eq`). So
`NoGotoHasTarget` transfers trivially. -/

theorem patchesFoldlM_preserves_no_goto_target_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_no_target : NoGotoHasTarget acc.2) :
    NoGotoHasTarget acc'.2 := by
  rw [patchesFoldlM_no_contracts_trans_eq labelMap patches acc acc' h_run]
  exact h_no_target

/-! ## Patcher reverse-target lemma

We need: if `patchGotoTargets trans patches` produces a GOTO with
`target = some t` at index `pc`, and the pre-patcher target at `pc`
was `none`, then `(pc, t) ∈ patches`.

Strategy: prove the contrapositive. If `pc` doesn't appear as a first
projection in `patches`, the patcher leaves `(pc).target` alone.
Equivalently: if the post target is `some t` and the pre target is
`none`, `pc` must appear as a first projection. Then we extract `t`
via the patcher's "last patch wins" lemma. -/

/-- Single-patch: setting target at index `i ≠ idx` leaves the value
at `i` unchanged. -/
private theorem patch_one_other_index
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (h_neq : i ≠ idx) :
    (a.set! idx { a[idx]! with target := some tgt })[i]? = a[i]? := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases h_idx : idx < a.size
  · exact Array.getElem?_setIfInBounds_ne h_neq.symm
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)]

/-- Single-patch: setting target at idx (in-bounds) gives `target =
some tgt` at idx. -/
private theorem patch_one_target_local
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    ∃ instr,
      (a.set! idx { a[idx]! with target := some tgt })[idx]? = some instr ∧
      instr.target = some tgt := by
  rw [Array.set!_eq_setIfInBounds]
  have h_lt : idx < (a.setIfInBounds idx { a[idx]! with target := some tgt }).size := by
    simp [h_idx]
  refine ⟨{ a[idx]! with target := some tgt }, ?_, rfl⟩
  rw [Array.getElem?_eq_getElem h_lt]
  rw [Array.getElem_setIfInBounds_self]

/-- Patcher fold preserves size. -/
private theorem patch_foldl_preserves_size_local
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat)) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps).size = a.size := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl]
    rw [ih]
    rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- If `pc` is not the first projection of any patch, the patcher
doesn't touch index `pc`. -/
private theorem patch_foldl_unchanged_when_idx_not_in
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc : Nat) (h_no_idx : ∀ p ∈ ps, p.1 ≠ pc) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps)[pc]? = a[pc]? := by
  induction ps generalizing a with
  | nil => simp
  | cons p rest ih =>
    simp only [List.foldl]
    have h_p_neq : p.1 ≠ pc := h_no_idx p (by simp)
    have h_rest_neq : ∀ q ∈ rest, q.1 ≠ pc :=
      fun q hq => h_no_idx q (by simp [hq])
    rw [ih _ h_rest_neq]
    have h_neq : pc ≠ p.1 := Ne.symm h_p_neq
    exact patch_one_other_index a p.1 p.2 pc h_neq

/-- Patcher's foldl preserves `target = some tgt` at `idx`, provided
no later patch in the list has first projection `idx`. -/
private theorem patch_foldl_target_preserved_when_idx_unique_in_tail
    (a : Array CProverGOTO.Instruction) (idx : Nat) (tgt : Nat)
    (ps : List (Nat × Nat))
    (h_target : ∃ instr, a[idx]? = some instr ∧ instr.target = some tgt)
    (h_tail_no_idx : ∀ p ∈ ps, p.1 ≠ idx) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[idx]? = some instr ∧
      instr.target = some tgt := by
  induction ps generalizing a with
  | nil => exact h_target
  | cons p rest ih =>
    simp only [List.foldl]
    have h_p_neq : p.1 ≠ idx := h_tail_no_idx p (by simp)
    have h_rest_neq : ∀ q ∈ rest, q.1 ≠ idx :=
      fun q hq => h_tail_no_idx q (by simp [hq])
    apply ih
    · obtain ⟨instr, h_at, h_tgt⟩ := h_target
      have h_neq : idx ≠ p.1 := Ne.symm h_p_neq
      rw [patch_one_other_index a p.1 p.2 idx h_neq]
      exact ⟨instr, h_at, h_tgt⟩
    · exact h_rest_neq

/-- Existence of "last occurrence" decomposition. -/
private theorem last_occurrence_split
    (ps : List (Nat × Nat)) (pc : Nat)
    (h : ∃ p ∈ ps, p.1 = pc) :
    ∃ pre t suf, ps = pre ++ (pc, t) :: suf ∧
                 ∀ p ∈ suf, p.1 ≠ pc := by
  induction ps with
  | nil => obtain ⟨p, hp, _⟩ := h; cases hp
  | cons head rest ih =>
    by_cases h_rest : ∃ p ∈ rest, p.1 = pc
    · obtain ⟨pre', t', suf', h_eq', h_no_idx'⟩ := ih h_rest
      refine ⟨head :: pre', t', suf', ?_, h_no_idx'⟩
      rw [List.cons_append, h_eq']
    · -- ¬∃ p ∈ rest, p.1 = pc means ∀ p ∈ rest, p.1 ≠ pc.
      have h_rest' : ∀ p ∈ rest, p.1 ≠ pc := by
        intro p hp h_eq
        exact h_rest ⟨p, hp, h_eq⟩
      by_cases h_head : head.1 = pc
      · refine ⟨[], head.2, rest, ?_, ?_⟩
        · simp; rw [← h_head]
        · exact h_rest'
      · obtain ⟨p, hp, h_eq⟩ := h
        rw [List.mem_cons] at hp
        rcases hp with h_phead | h_prest
        · subst h_phead
          exact absurd h_eq h_head
        · exact absurd h_eq (h_rest' p h_prest)

/-- "Last patch at pc determines the target". -/
private theorem patch_foldl_target_at_last
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc t : Nat)
    (h_last_eq : ∃ pre suf, ps = pre ++ (pc, t) :: suf ∧
                            ∀ p ∈ suf, p.1 ≠ pc)
    (h_idx : pc < a.size) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[pc]? = some instr ∧
      instr.target = some t := by
  obtain ⟨pre, suf, h_eq, h_suf_no_idx⟩ := h_last_eq
  rw [h_eq]
  rw [List.foldl_append, List.foldl_cons]
  let a_pre := List.foldl
    (fun acc (p : Nat × Nat) =>
      acc.set! p.fst { acc[p.fst]! with target := some p.snd })
    a pre
  have h_size_apre : a_pre.size = a.size := patch_foldl_preserves_size_local a pre
  have h_idx_apre : pc < a_pre.size := h_size_apre ▸ h_idx
  obtain ⟨_, h_at_apre_set, h_target_apre_set⟩ := patch_one_target_local a_pre pc t h_idx_apre
  exact patch_foldl_target_preserved_when_idx_unique_in_tail
    (a_pre.set! pc { a_pre[pc]! with target := some t }) pc t suf
    ⟨_, h_at_apre_set, h_target_apre_set⟩ h_suf_no_idx

/-- **Reverse-direction patcher post-condition.** If the post-patcher
target at `pc` is `some t` and the pre-patcher target at `pc` is
`none`, then `(pc, t) ∈ ps`. -/
private theorem patch_foldl_target_some_in_list
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
    (pc t : Nat) (instr_pre instr_post : CProverGOTO.Instruction)
    (h_pre_at : a[pc]? = some instr_pre)
    (h_pre_target : instr_pre.target = none)
    (h_post_at :
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[pc]? = some instr_post)
    (h_post_target : instr_post.target = some t) :
    (pc, t) ∈ ps := by
  by_cases h_some : ∃ p ∈ ps, p.1 = pc
  · have h_idx_lt : pc < a.size := by
      rcases Array.getElem?_eq_some_iff.mp h_pre_at with ⟨h_lt, _⟩
      exact h_lt
    obtain ⟨pre, t', suf, h_eq, h_suf_no_idx⟩ := last_occurrence_split ps pc h_some
    obtain ⟨_, h_at_post', h_target_post'⟩ :=
      patch_foldl_target_at_last a ps pc t' ⟨pre, suf, h_eq, h_suf_no_idx⟩ h_idx_lt
    rw [h_at_post'] at h_post_at
    injection h_post_at with h_eq2
    rw [← h_eq2, h_target_post'] at h_post_target
    injection h_post_target with h_t_eq
    rw [h_eq, ← h_t_eq]
    exact List.mem_append_right pre (by simp)
  · -- ¬∃ p ∈ ps, p.1 = pc means ∀ p ∈ ps, p.1 ≠ pc.
    have h_no_idx : ∀ p ∈ ps, p.1 ≠ pc := by
      intro p hp h_eq
      exact h_some ⟨p, hp, h_eq⟩
    rw [patch_foldl_unchanged_when_idx_not_in a ps pc h_no_idx] at h_post_at
    rw [h_pre_at] at h_post_at
    injection h_post_at with h_eq
    rw [← h_eq, h_pre_target] at h_post_target
    cases h_post_target

/-- Reverse-direction patcher post-condition (top-level form). If the
post-patcher target at `pc` is `some t` and the pre-patcher target at
`pc` was `none`, then `(pc, t) ∈ patches`. -/
theorem patchGotoTargets_target_some_in_patches
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (pc t : Nat) (instr_pre instr_post : Instruction)
    (h_pre_at : trans.instructions[pc]? = some instr_pre)
    (h_pre_target : instr_pre.target = none)
    (h_post_at : (Imperative.patchGotoTargets trans patches).instructions[pc]? = some instr_post)
    (h_post_target : instr_post.target = some t) :
    (pc, t) ∈ patches := by
  unfold Imperative.patchGotoTargets at h_post_at
  simp only at h_post_at
  exact patch_foldl_target_some_in_list trans.instructions patches pc t
    instr_pre instr_post h_pre_at h_pre_target h_post_at h_post_target

/-! ## Patches-fold reverse direction

Given the patches-fold succeeds with output `acc'.1 = resolved`, every
`(pc, target) ∈ resolved` either was in the initial `acc.1`, or comes
from some `(pc, label) ∈ patches` with `labelMap[label]? = some
target`. -/

/-- Per-step reverse direction: for `(pc, target) ∈ acc'.1`, either
`(pc, target) ∈ acc.1` or `(pc, target)` is the new prepended pair
(in which case `pc = idxLabel.1` and there exists `label` with
`labelMap[label]? = some target` — namely `idxLabel.2`). -/
theorem coreCFGToGotoPatchStep_no_contracts_resolved_reverse
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    (pc = idxLabel.1 ∧ labelMap[idxLabel.2]? = some target) := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  -- Get a labelMap lookup for `label` from the patch step's success.
  obtain ⟨targetLoc, h_lookup⟩ :=
    coreCFGToGotoPatchStep_success_lookup labelMap ∅
      (resolvedPatches, trans) acc' (idx, label) h_run
  -- The patch step prepends (idx, targetLoc) to resolvedPatches.
  have h_acc'_eq : acc'.1 = (idx, targetLoc) :: resolvedPatches :=
    coreCFGToGotoPatchStep_no_contracts_resolvedPatches labelMap
      (resolvedPatches, trans) acc' (idx, label) targetLoc h_lookup h_run
  rw [h_acc'_eq] at h_in
  simp only [List.mem_cons] at h_in
  rcases h_in with h_eq | h_old
  · -- (idx, targetLoc) = (pc, target).
    injection h_eq with h_pc h_target
    -- h_pc : pc = idx, h_target : target = targetLoc.
    right
    refine ⟨h_pc, ?_⟩
    rw [h_target]
    exact h_lookup
  · left; exact h_old

/-- Patches-fold reverse: every `(pc, target) ∈ acc'.1` either was in
`acc.1`, or comes from some `(pc, label) ∈ patches` with
`labelMap[label]? = some target`. -/
theorem patchesFoldlM_no_contracts_resolved_reverse
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    ∃ label, (pc, label) ∈ patches ∧ labelMap[label]? = some target := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    left; exact h_in
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_ih := ih acc₁ h_run
      rcases h_ih with h_in_acc₁ | ⟨lbl, h_in_rest, h_lookup⟩
      · -- (pc, target) ∈ acc₁.1. Reverse the head step.
        have := coreCFGToGotoPatchStep_no_contracts_resolved_reverse
          labelMap acc acc₁ head h_step pc target h_in_acc₁
        rcases this with h_acc | ⟨h_pc, h_lookup⟩
        · left; exact h_acc
        · right
          refine ⟨head.2, ?_, h_lookup⟩
          obtain ⟨h₁, h₂⟩ := head
          subst h_pc
          exact List.mem_cons_self
      · -- (pc, lbl) ∈ rest. So (pc, lbl) ∈ head :: rest.
        right
        exact ⟨lbl, by simp [h_in_rest], h_lookup⟩
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Array form of `patchesFoldlM_no_contracts_resolved_reverse`. -/
theorem patchesFoldlM_no_contracts_resolved_reverse_array
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (pc target : Nat) (h_in : (pc, target) ∈ acc'.1) :
    (pc, target) ∈ acc.1 ∨
    ∃ label, (pc, label) ∈ patches ∧ labelMap[label]? = some target := by
  rw [← Array.foldlM_toList] at h_run
  obtain h := patchesFoldlM_no_contracts_resolved_reverse
    labelMap patches.toList acc acc' h_run pc target h_in
  rcases h with h | ⟨lbl, h_in', h_lookup⟩
  · left; exact h
  · right
    refine ⟨lbl, ?_, h_lookup⟩
    exact Array.mem_toList_iff.mp h_in'

/-! ## labelMap keys are block labels

Every key in the post-blocks-fold labelMap was inserted by some
block-step, hence corresponds to a block in the input list. -/

/-- One-step block-fold: any key in `st'.labelMap` either was in
`st.labelMap` or is the head block's label. -/
theorem coreCFGToGotoBlockStep_labelMap_key
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (label : String) (pc : Nat)
    (h_lookup : st'.labelMap[label]? = some pc) :
    label = lblBlk.1 ∨ st.labelMap[label]? = some pc := by
  rw [coreCFGToGotoBlockStep_labelMap fname lblBlk st st' h_run] at h_lookup
  rw [Std.HashMap.getElem?_insert] at h_lookup
  by_cases h : lblBlk.1 = label
  · left; exact h.symm
  · simp [h] at h_lookup
    right; exact h_lookup

/-- Blocks-fold preserves "labelMap keys are in initial keys ∪ blocks
labels". -/
theorem blocksFoldlM_labelMap_keys_subset
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (label : String) (pc : Nat)
    (h_lookup : st'.labelMap[label]? = some pc) :
    (∃ pc', st.labelMap[label]? = some pc') ∨
    label ∈ blocks.map Prod.fst := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    left; exact ⟨pc, h_lookup⟩
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_ih := ih st₁ h_run
      rcases h_ih with ⟨pc₁, h_in_st₁⟩ | h_in_rest
      · -- label is in st₁.labelMap. Reverse the head step.
        rcases coreCFGToGotoBlockStep_labelMap_key fname head st st₁ h_step
                label pc₁ h_in_st₁ with h_eq | h_in_st
        · -- label = head.1, so it's a block label.
          right
          rw [h_eq]
          exact List.mem_cons_self
        · left; exact ⟨pc₁, h_in_st⟩
      · -- label is in rest.
        right
        exact List.mem_cons_of_mem _ h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- After the blocks-fold from the initial state (empty labelMap),
every labelMap key is a block label. -/
theorem blocksFoldlM_labelMap_keys_in_blocks
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname)
              ({ trans := trans₀, pendingPatches := #[], labelMap := {},
                 loopContracts := {} } : Strata.CoreCFGTransLoopState)
            = Except.ok st_final)
    (label : String) (pc : Nat)
    (h_lookup : st_final.labelMap[label]? = some pc) :
    label ∈ blocks.map Prod.fst := by
  rcases blocksFoldlM_labelMap_keys_subset fname blocks _ st_final h_run label pc h_lookup
    with ⟨pc', h_init⟩ | h_block
  · -- Initial labelMap is empty, so this is impossible.
    show label ∈ blocks.map Prod.fst
    have : (∅ : Std.HashMap String Nat)[label]? = some pc' := h_init
    rw [Std.HashMap.getElem?_empty] at this
    cases this
  · exact h_block

/-! ## Final composition: `EveryGotoTargetIsBlockLabel` of the translator's output

We now compose:

1. `coreCFGToGotoTransform_decompose` to extract `st_final, resolved,
   trans_post`.
2. `blocksFoldlM_preserves_no_goto_target` to establish
   `NoGotoHasTarget st_final.trans` (with the trivial empty initial
   state base case).
3. Under `loopContracts = ∅`, `trans_post = st_final.trans` via
   `patchesFoldlM_no_contracts_trans_eq`. So `NoGotoHasTarget
   trans_post`.
4. `ans = patchGotoTargets trans_post resolved`, so a GOTO at `pc` in
   `ans` with `target = some t` had pre-target `none`, hence by the
   reverse-target lemma `(pc, t) ∈ resolved`.
5. `(pc, t) ∈ resolved` reverse-traces to `∃ label, (pc, label) ∈
   pendingPatches ∧ labelMap[label]? = some t`.
6. Such a `label` is a block label by `blocksFoldlM_labelMap_keys_in_blocks`.
7. Find the corresponding `(label, blk) ∈ cfg.blocks`. -/

/-- **Top-level theorem.** Given a successful run of
`coreCFGToGotoTransform`, every emitted GOTO instruction's target
value is a `labelMap` entry for some block in `cfg.blocks` (where
`labelMap` is the translator's hashmap-keyed labelMap). -/
theorem everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_goto_target : NoGotoHasTarget trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      (hashMapToLabelMap st_final.labelMap) := by
  -- Step 1: decompose ans's structure.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- The blocks-fold result is unique.
  have h_st_final_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    injection h_blocks_run'
  subst h_st_final_eq
  -- Step 2: NoGotoHasTarget through blocks-fold (via BlocksFoldClosed) +
  -- patches-fold no-op.
  have h_init' : NoGotoHasTarget' trans₀.instructions := h_init_no_goto_target
  have h_no_goto_target_st_final : NoGotoHasTarget' st_final.trans.instructions :=
    BlocksFoldClosed.of_blocks_run (P := NoGotoHasTarget') functionName cfg trans₀
      h_init' st_final h_blocks_run
  -- Step 3: patchesFoldlM with empty contracts: trans unchanged.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- Step 4: feed everyone into the predicate.
  intros pc target instr h_at h_ty h_target
  -- ans.instrAt pc = ans.instructions[pc]?, so unfolding:
  have h_at' : ans.instructions[pc]? = some instr := h_at
  rw [h_ans_eq] at h_at'
  -- The GOTO at pc has target = some target in patchGotoTargets trans_post resolved.
  -- The pre-patcher target is in trans_post = st_final.trans, which has NoGotoHasTarget.
  -- So pre-target = none. Apply patchGotoTargets_target_some_in_patches.
  -- We need access to trans_post.instructions[pc]?.
  have h_size_post : (Imperative.patchGotoTargets trans_post resolved).instructions.size
                      = trans_post.instructions.size :=
    patchGotoTargets_preserves_size trans_post resolved
  have h_pc_lt_post : pc < (Imperative.patchGotoTargets trans_post resolved).instructions.size := by
    rcases Array.getElem?_eq_some_iff.mp h_at' with ⟨h_lt, _⟩
    exact h_lt
  have h_pc_lt_pre : pc < trans_post.instructions.size := h_size_post ▸ h_pc_lt_post
  obtain ⟨instr_pre, h_pre_at, _, _, _, _⟩ :=
    patchGotoTargets_preserves_full_except_target trans_post resolved pc instr h_at'
  have h_pre_target_none : instr_pre.target = none := by
    rw [h_trans_post_eq] at h_pre_at
    -- instr_pre.type = instr.type (preserved by patcher), and instr.type = .GOTO.
    -- We need instr_pre to be a GOTO. Let's deduce.
    have h_pre_ty : instr_pre.type = .GOTO := by
      -- Use patchGotoTargets_preserves_type to get instr.type = instr_pre.type.
      obtain ⟨instr_pre', h_at_pre', h_ty_eq⟩ :=
        patchGotoTargets_preserves_type trans_post resolved pc instr h_at'
      rw [h_trans_post_eq] at h_at_pre'
      rw [h_at_pre'] at h_pre_at
      injection h_pre_at with h_inj
      -- h_inj : instr_pre' = instr_pre.
      rw [← h_inj, ← h_ty_eq]
      exact h_ty
    exact h_no_goto_target_st_final h_pre_at h_pre_ty
  have h_in_resolved : (pc, target) ∈ resolved := by
    rw [h_trans_post_eq] at h_pre_at
    -- patch direction: in_resolved follows from reverse-target lemma applied to st_final.trans.
    have h_pre_at_post : trans_post.instructions[pc]? = some instr_pre := by
      rw [h_trans_post_eq]; exact h_pre_at
    -- The post-patcher form.
    have h_post_at_post : (Imperative.patchGotoTargets trans_post resolved).instructions[pc]? = some instr := h_at'
    exact patchGotoTargets_target_some_in_patches trans_post resolved pc target
      instr_pre instr h_pre_at_post h_pre_target_none h_post_at_post h_target
  -- Step 5: reverse-trace (pc, target) ∈ resolved to a pendingPatch with labelMap lookup.
  have h_resolved_initial_acc : (pc, target) ∉ ([] : List (Nat × Nat)) := by simp
  rcases patchesFoldlM_no_contracts_resolved_reverse_array st_final.labelMap
    st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
    h_patches_run pc target h_in_resolved with h_in_acc | ⟨lbl, h_in_pp, h_lookup⟩
  · simp at h_in_acc
  · -- lbl: ∃ label, (pc, label) ∈ pendingPatches ∧ labelMap[label]? = some target.
    -- By blocksFoldlM_labelMap_keys_in_blocks, lbl is a block label.
    have h_lbl_in : lbl ∈ cfg.blocks.map Prod.fst := by
      apply blocksFoldlM_labelMap_keys_in_blocks functionName cfg.blocks trans₀ st_final
      · simp [coreCFGToGotoInitState] at h_blocks_run
        exact h_blocks_run
      · exact h_lookup
    -- Find the corresponding block.
    rw [List.mem_map] at h_lbl_in
    obtain ⟨pair, h_pair_in, h_pair_eq⟩ := h_lbl_in
    obtain ⟨l', blk⟩ := pair
    simp at h_pair_eq
    -- h_pair_eq : l' = lbl. Substitute (eliminates lbl, keeps l').
    subst h_pair_eq
    refine ⟨l', blk, h_pair_in, ?_⟩
    -- Goal: hashMapToLabelMap st_final.labelMap l' = some target.
    show st_final.labelMap[l']? = some target
    exact h_lookup

/-! ## `wf.labelMap` form (caller-supplied bridge)

The supervisor's spec asks for the property keyed by `wf.labelMap`
(an arbitrary `WellFormedTranslation`'s labelMap), not by the
translator's `hashMapToLabelMap st_final.labelMap`.

For an *arbitrary* `wf`, the bridge requires uniqueness of the
labelMap over `cfg.blocks` labels — i.e., `wf.labelMap l = some pc'`
implies `pc' = hashMapToLabelMap st_final.labelMap l`. This is
genuinely outside `WellFormedTranslation`'s current vocabulary
(which only constrains forward CFG → program direction; see R7a's
report for the analysis).

The clean way to deliver the `wf.labelMap` form is to either
1. add a labelMap-uniqueness field to `WellFormedTranslation`, or
2. take an explicit `h_labelMap_agree` hypothesis bridging
   `wf.labelMap` and `hashMapToLabelMap st_final.labelMap` over
   `cfg.blocks` labels.

We choose option 2: take the bridge as a caller obligation. For the
v4 caller (which constructs `wf` via
`coreCFGToGotoTransform_wellFormed_strengthened`), the bridge is
trivially provable: the strengthened theorem's WF is built from
`hashMapToLabelMap st_final.labelMap`, so the equality holds
definitionally. -/

/-- **Top-level theorem (`wf.labelMap` form).** Given a successful
run of `coreCFGToGotoTransform`, an arbitrary
`WellFormedTranslation` for the resulting program, and a bridge
hypothesis `h_labelMap_agree` connecting `wf.labelMap` with the
translator's `hashMapToLabelMap st_final.labelMap` on `cfg.blocks`
labels, every emitted GOTO instruction's target value is a
`wf.labelMap` entry for some block in `cfg.blocks`. -/
theorem everyGotoTargetIsLabelMapEntry_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_goto_target : NoGotoHasTarget trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (wf : WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool)
    -- Bridge: `wf.labelMap` agrees with the translator's hashmap-keyed
    -- labelMap on the `target`-direction (consequence of `wf.labelMap_total`
    -- + LOCATION-uniqueness of `pgm.instructions`; trivially provable for
    -- `wf` constructed via `coreCFGToGotoTransform_wellFormed_strengthened`).
    (h_labelMap_agree :
      ∀ l blk target, (l, blk) ∈ cfg.blocks →
        st_final.labelMap[l]? = some target →
        wf.labelMap l = some target) :
    GotoTargetInRange.EveryGotoTargetIsLabelMapEntry cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      wf.labelMap := by
  intros pc target instr h_at h_ty h_target
  obtain ⟨l, blk, h_in, h_lookup⟩ :=
    everyGotoTargetIsLabelMapEntry_of_translator_translatorMap
      Env functionName cfg trans₀ h_init_no_goto_target
      h_loopContracts_empty_post ans h_run st_final h_blocks_run
      h_at h_ty h_target
  refine ⟨l, blk, h_in, ?_⟩
  -- h_lookup : hashMapToLabelMap st_final.labelMap l = some target.
  -- Bridge to wf.labelMap via the agreement hypothesis.
  have h_lookup_st : st_final.labelMap[l]? = some target := h_lookup
  exact h_labelMap_agree l blk target h_in h_lookup_st

end CProverGOTO.GotoTargetProvenance
