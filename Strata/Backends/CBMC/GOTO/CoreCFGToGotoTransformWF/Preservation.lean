/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Shape
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # WellFormedTranslation - Preservation lemmas

This file is part 2 of the CoreCFGToGotoTransformWF split. It
provides the size_eq / locationNum_eq_index preservation lemmas
under each emit/Cmd/patcher action, plus the innerCmdLoop shadow,
toGotoInstructions monotonicity, and per-block layout production.
-/

namespace CProverGOTO

open Imperative

public section

/-! ## Preservation under `emitLabel`

The outer loop body starts each iteration by emitting a LOCATION
instruction via `emitLabel`. We need to know that this preserves the
`size_eq` and `locationNum_eq_index` invariants, and that the new
`labelMap` (extended with `label ↦ trans.nextLoc`) keeps the partial
WF working. -/

/-- After `emitLabel`, the new transform's `instructions.size` still
equals its `nextLoc` (each goes up by 1). -/
theorem emitLabel_preserves_size_eq
    (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    (Imperative.emitLabel label srcLoc trans).instructions.size =
      (Imperative.emitLabel label srcLoc trans).nextLoc := by
  simp [Imperative.emitLabel, Array.size_push, h_size]

/-- After `emitLabel`, the new transform's `locationNum`s still match
their array indices: the existing prefix is preserved, and the
freshly-pushed LOCATION has `locationNum = trans.nextLoc =
trans.instructions.size`. -/
theorem emitLabel_preserves_locationNum_eq_index
    (label : String) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitLabel label srcLoc trans).instructions[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  -- Compute `(emitLabel ..).instructions` as a `push` so the rewrite
  -- patterns apply.
  let new_instr : CProverGOTO.Instruction :=
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := CProverGOTO.Code.skip }
  have h_unfold : (Imperative.emitLabel label srcLoc trans).instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    -- h : some trans.instructions[i] = some instr
    have h' : trans.instructions[i]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_loc i instr h'
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq : i = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      show new_instr.locationNum = trans.instructions.size
      simp [new_instr, h_size]
    · have h_lt' : trans.instructions.size < i := by omega
      have h_push_size :
          (trans.instructions.push new_instr).size = trans.instructions.size + 1 := by
        simp [Array.size_push]
      have h_oor : (trans.instructions.push new_instr).size ≤ i := by
        rw [h_push_size]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-! ## Preservation under `Cmd.toGotoInstructions`

After processing one Core command via the imperative
`Cmd.toGotoInstructions`, the resulting `trans'` still satisfies the
`size_eq` and `locationNum_eq_index` invariants. Because each branch of
`Cmd.toGotoInstructions` either pushes one or two instructions and
advances `nextLoc` by the same number (provided by the per-shape
sub-lemmas above), the calculation is direct. -/

/-- `Cmd.toGotoInstructions` preserves `instructions.size = nextLoc`. -/
theorem toGotoInstructions_preserves_size_eq
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, _i_decl, _i_assn, _, _, _, _, _, _, _, _,
              h_inst, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst, h_next]
      show (trans.instructions ++ #[_, _]).size = _
      simp [Array.size_append, h_size]
    | nondet =>
      obtain ⟨_gty, _i_decl, _, _, _, _, h_inst, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, _i_assn, _, _, _, _, _, h_inst, h_next⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
    | nondet =>
      obtain ⟨_gty, _i_assn, _, _, _, _, h_inst, h_next⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, h_next, Array.size_push, h_size]
  | assert label e md =>
    obtain ⟨_e_goto, _i, _, _, _, _, h_inst, h_next⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, h_next, Array.size_push, h_size]
  | assume label e md =>
    obtain ⟨_e_goto, _i, _, _, _, _, h_inst, h_next⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, h_next, Array.size_push, h_size]
  | cover label e md =>
    -- `cover` is structurally similar to `assert` but emits an ASSERT
    -- with a different comment. We unfold directly for size-preservation.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      simp [Array.size_push, h_size]
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- Generic helper: pushing one fresh instruction whose `locationNum =
trans.nextLoc` preserves `locationNum_eq_index`, given the loop
invariant. -/
private theorem push_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (new_instr : CProverGOTO.Instruction)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i)
    (h_new : new_instr.locationNum = trans.nextLoc) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.push new_instr)[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    have h' : trans.instructions[i]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_loc i instr h'
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq : i = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      rw [h_new, h_size]
    · have h_lt' : trans.instructions.size < i := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ i := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-- Generic helper: appending two fresh instructions whose `locationNum`
fields are `trans.nextLoc` and `trans.nextLoc + 1` preserves
`locationNum_eq_index`. Used for the `init_det` case. -/
private theorem append_two_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (i₀ i₁ : CProverGOTO.Instruction)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i)
    (h_new0 : i₀.locationNum = trans.nextLoc)
    (h_new1 : i₁.locationNum = trans.nextLoc + 1) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.append #[i₀, i₁])[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  -- Replace .append with `++ #[i₀, i₁]`.
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h
  by_cases h_lt : i < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h
    exact h_loc i instr h
  · have h_ge : trans.instructions.size ≤ i := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : i = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      subst h
      rw [h_new0, h_size]
    · by_cases h_eq1 : i = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h
        simp at h
        subst h
        rw [h_new1, h_size]
      · -- i > size + 1: out of bounds.
        have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ i := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h
        exact absurd h (by simp)

/-- `Cmd.toGotoInstructions` preserves `locationNum_eq_index` on the
emitted prefix. -/
theorem toGotoInstructions_preserves_locationNum_eq_index
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, i_decl, i_assn, _, _, _, _, h_decl_loc,
              _, _, h_assn_loc, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      exact append_two_preserves_locationNum_eq_index
        trans i_decl i_assn h_size h_loc h_decl_loc h_assn_loc
    | nondet =>
      obtain ⟨_gty, i_decl, _, _, _, h_loc_new, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_decl h_size h_loc h_loc_new
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, i_assn, _, _, _, _, h_loc_new, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_assn h_size h_loc h_loc_new
    | nondet =>
      obtain ⟨_gty, i_assn, _, _, _, h_loc_new, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst]
      exact push_preserves_locationNum_eq_index
        trans i_assn h_size h_loc h_loc_new
  | assert label e md =>
    obtain ⟨_e_goto, i, _, _, _, h_loc_new, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact push_preserves_locationNum_eq_index
      trans i h_size h_loc h_loc_new
  | assume label e md =>
    obtain ⟨_e_goto, i, _, _, _, h_loc_new, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact push_preserves_locationNum_eq_index
      trans i h_size h_loc h_loc_new
  | cover label e md =>
    -- Direct unfold + push.
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      -- ans.instructions = trans.instructions.push assert_inst
      -- where assert_inst.locationNum = trans.nextLoc.
      apply push_preserves_locationNum_eq_index trans _ h_size h_loc
      rfl
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation under transfer-emit helpers -/

/-- `emitCondGoto` preserves `instructions.size = nextLoc`. -/
theorem emitCondGoto_preserves_size_eq
    (guard : CProverGOTO.Expr) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc) :
    let p := Imperative.emitCondGoto guard srcLoc trans
    p.fst.instructions.size = p.fst.nextLoc := by
  simp [Imperative.emitCondGoto, Imperative.emitGoto, Array.size_push, h_size]

/-- `emitCondGoto` preserves `locationNum_eq_index`. -/
theorem emitCondGoto_preserves_locationNum_eq_index
    (guard : CProverGOTO.Expr) (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitCondGoto guard srcLoc trans).fst.instructions[i]? =
        some instr →
      instr.locationNum = i := by
  intro i instr h
  let new_instr : CProverGOTO.Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := guard, target := none }
  have h_unfold : (Imperative.emitCondGoto guard srcLoc trans).fst.instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  exact push_preserves_locationNum_eq_index trans new_instr
    h_size h_loc rfl i instr h

/-- `emitUncondGoto` preserves `locationNum_eq_index`. -/
theorem emitUncondGoto_preserves_locationNum_eq_index
    (srcLoc : CProverGOTO.SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.emitUncondGoto srcLoc trans).fst.instructions[i]? =
        some instr →
      instr.locationNum = i := by
  intro i instr h
  let new_instr : CProverGOTO.Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := CProverGOTO.Expr.true, target := none }
  have h_unfold : (Imperative.emitUncondGoto srcLoc trans).fst.instructions
      = trans.instructions.push new_instr := by rfl
  rw [h_unfold] at h
  exact push_preserves_locationNum_eq_index trans new_instr
    h_size h_loc rfl i instr h

/-! ## Preservation under `END_FUNCTION` emission

The `.finish` branch of `coreCFGToGotoTransform`'s outer-loop body
inlines an END_FUNCTION emit (no helper exists), so we model it
directly as a push of an instruction with the right shape. -/

/-- The shape of the `.finish md` branch's emitted END_FUNCTION
instruction. The translator hardcodes:
* `type = .END_FUNCTION`,
* `locationNum = trans.nextLoc`,
* `sourceLoc = metadataToSourceLoc md fname trans.sourceText`. -/
@[expose] def endFunctionInstr
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    CProverGOTO.Instruction :=
  { type := .END_FUNCTION,
    locationNum := trans.nextLoc,
    sourceLoc := Imperative.metadataToSourceLoc md fname trans.sourceText }

/-- `END_FUNCTION` emit preserves `locationNum_eq_index`. -/
theorem endFunction_emit_preserves_locationNum_eq_index
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (trans.instructions.push (endFunctionInstr md fname trans))[i]? =
        some instr →
      instr.locationNum = i :=
  push_preserves_locationNum_eq_index trans (endFunctionInstr md fname trans)
    h_size h_loc rfl

/-! ## Preservation under `patchGotoTargets`

The patcher only edits `target` fields, never `locationNum`s. So the
`locationNum_eq_index` invariant transfers unchanged. -/

/-- `Array.set!` with a record update on `target` doesn't change
`locationNum`. -/
private theorem patch_one_preserves_locationNum
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        a[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr →
      instr.locationNum = i := by
  intro i instr h
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · -- Set at in-bounds idx via setIfInBounds.
    by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set :
          i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      subst h
      -- The patched record's locationNum = a[i]!.locationNum.
      -- And a[i]!.locationNum = a[i].locationNum (in-bounds) = i by h_loc.
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      have h_loc_eq : a[i].locationNum = i := h_loc i a[i] h_at
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      simp [h_getD, h_loc_eq]
    · -- i ≠ idx: setIfInBounds preserves a[i]?.
      rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact h_loc i instr h
  · -- idx out of range: setIfInBounds is a no-op.
    rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact h_loc i instr h

/-- `Array.set!` with a record update on `target` preserves the
type field. -/
private theorem patch_one_preserves_type
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.type = instr_pre.type := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set : i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      refine ⟨a[i], h_at, ?_⟩
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      rw [← h]
      simp [h_getD]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl⟩

/-- `patchGotoTargets` preserves the type field at any in-bounds
index — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_type
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.type = instr_pre.type := by
  unfold Imperative.patchGotoTargets at h
  simp only at h
  -- Generalize over the array.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (i : Nat) (instr : CProverGOTO.Instruction),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps)[i]? = some instr →
        ∃ instr_pre, a[i]? = some instr_pre ∧ instr.type = instr_pre.type := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_ty_after_first⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_ty_pre⟩ :=
        patch_one_preserves_type a p.1 p.2 i instr_after_first h_after_first
      exact ⟨instr_pre, h_pre, h_ty_after_first.trans h_ty_pre⟩
  exact hgen _ _ _ _ h

/-- `patchGotoTargets` preserves `locationNum_eq_index` on the underlying
array — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_locationNum_eq_index
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr →
      instr.locationNum = i := by
  -- Generalise so the IH works at every prefix.
  unfold Imperative.patchGotoTargets
  simp only
  -- We're in the foldl shape now; induct on patches.
  intro i instr
  -- A more general statement: for any `a` satisfying `h_loc`, the
  -- foldl over `patches` preserves `h_loc`.
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (h : ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          a[i]? = some instr → instr.locationNum = i),
        ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          (List.foldl
            (fun acc (p : Nat × Nat) =>
              acc.set! p.fst { acc[p.fst]! with target := some p.snd })
            a ps)[i]? = some instr → instr.locationNum = i := by
    intro a ps h
    induction ps generalizing a with
    | nil =>
      intro i instr h2
      simp only [List.foldl] at h2
      exact h i instr h2
    | cons p ps ih =>
      intro i instr h2
      simp only [List.foldl] at h2
      apply ih (a.set! p.fst { a[p.fst]! with target := some p.snd })
        (patch_one_preserves_locationNum a p.fst p.snd h)
      exact h2
  exact hgen _ _ h_loc i instr

/-- A single patch step preserves the `labels` field. Used to lift the
`labels = [l]` invariant from `st_final.trans` to `ans`. -/
private theorem patch_one_preserves_labels
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.labels = instr_pre.labels := by
  rw [Array.set!_eq_setIfInBounds] at h
  by_cases h_idx : idx < a.size
  · by_cases h_eq : i = idx
    · subst h_eq
      have h_lt_set :
          i < (a.setIfInBounds i { a[i]! with target := some tgt }).size := by
        simp [h_idx]
      rw [Array.getElem?_eq_getElem h_lt_set] at h
      rw [Array.getElem_setIfInBounds_self] at h
      injection h with h
      have h_at : a[i]? = some a[i] := Array.getElem?_eq_getElem h_idx
      refine ⟨a[i], h_at, ?_⟩
      have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
      rw [← h]
      simp [h_getD]
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl⟩

/-- `patchGotoTargets` preserves the `labels` field. -/
theorem patchGotoTargets_preserves_labels
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.labels = instr_pre.labels := by
  unfold Imperative.patchGotoTargets at h
  simp only at h
  have hgen :
      ∀ (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat))
        (i : Nat) (instr : CProverGOTO.Instruction),
        (List.foldl
          (fun acc (p : Nat × Nat) =>
            acc.set! p.fst { acc[p.fst]! with target := some p.snd })
          a ps)[i]? = some instr →
        ∃ instr_pre, a[i]? = some instr_pre ∧
          instr.labels = instr_pre.labels := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_lab_after⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_lab_pre⟩ :=
        patch_one_preserves_labels a p.1 p.2 i instr_after_first h_after_first
      exact ⟨instr_pre, h_pre, h_lab_after.trans h_lab_pre⟩
  exact hgen _ _ _ _ h

/-! ## Inner-loop shadow: a foldlM over the admitted `.cmd c` cases

The `coreCFGToGotoTransform`'s inner `for cmd in block.cmds do` loop is
imperative and dispatches on `cmd.cmd / cmd.call`. Under the
admitted-commands fragment (`isAdmittedCmd`), only the `.cmd c` branch
is taken, so the inner loop is morally a `foldlM` of
`Cmd.toGotoInstructions` over the `c`-extractions of `block.cmds`.

We give this a clean recursive name here, and prove that the empty
list and inductive step both preserve the loop invariants we care
about. -/

/-- Run `Cmd.toGotoInstructions` on each admitted `.cmd c` of a block's
command list, threading the transform state. Errors out on any
non-admitted command. -/
@[expose] def innerCmdLoop
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    Except Std.Format (Imperative.GotoTransform Core.Expression.TyEnv) :=
  match cmds with
  | [] => Except.ok trans
  | .cmd c :: rest => do
    let trans' ← (Imperative.Cmd.toGotoInstructions T fname c trans).mapError
      (fun e => f!"{e}")
    innerCmdLoop trans'.T fname rest trans'
  | .call _ _ _ :: _ =>
    Except.error f!"[innerCmdLoop] .call is not in the admitted fragment"

/-- Empty body: the inner loop is a no-op. -/
theorem innerCmdLoop_nil
    (T : Core.Expression.TyEnv) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    innerCmdLoop T fname [] trans = Except.ok trans := rfl

/-! ## Monotonicity of `Cmd.toGotoInstructions` -/

/-- `Cmd.toGotoInstructions` only grows the instruction array. -/
theorem toGotoInstructions_size_le
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      show trans.instructions.size ≤ (trans.instructions ++ #[_,_]).size
      rw [Array.size_append]; simp
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, Array.size_push]; omega
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, Array.size_push]; omega
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, Array.size_push]; omega
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, Array.size_push]; omega
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, Array.size_push]; omega
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      rw [← h_run, Array.size_push]; omega
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- `Cmd.toGotoInstructions` preserves the input prefix on `?`-lookups:
any index `k < trans.instructions.size` reads the same in
`ans.instructions[k]?` as `trans.instructions[k]?`. (The `?`-lookup
form avoids the dependent-type elaboration issues that the
proof-style lookup hits.) -/
theorem toGotoInstructions_instructions_prefix?
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (k : Nat) (h_k : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, i₀, i₁, _, _, _, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      have h_eq : trans.instructions.append #[i₀, i₁] = trans.instructions ++ #[i₀, i₁] := rfl
      rw [h_eq, Array.getElem?_append_left h_k]
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
    | nondet =>
      obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst, Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      let assert_inst : CProverGOTO.Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := Imperative.metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h_inst : ans.instructions = trans.instructions.push assert_inst := by
        rw [← h_run]
      rw [h_inst]
      rw [Array.getElem?_push_lt h_k, Array.getElem?_eq_getElem h_k]
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- `innerCmdLoop` only grows the instruction array. -/
theorem innerCmdLoop_size_le
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    rw [← h_run]; exact Nat.le_refl _
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have := toGotoInstructions_size_le T fname c trans trans' h_step
        have := ih trans'.T trans' h_run
        omega
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-- `innerCmdLoop` preserves the input prefix on `?`-lookups: any
index `k < trans.instructions.size` reads the same in
`ans.instructions[k]?` as `trans.instructions[k]?`. -/
theorem innerCmdLoop_instructions_prefix?
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (k : Nat) (h_k : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  induction cmds generalizing T trans with
  | nil =>
    rw [innerCmdLoop_nil] at h_run
    injection h_run with h_run
    subst h_run
    rfl
  | cons cmd rest ih =>
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        have h_k_trans' : k < trans'.instructions.size := by
          have := toGotoInstructions_size_le T fname c trans trans' h_step; omega
        rw [ih trans'.T trans' h_run h_k_trans']
        exact toGotoInstructions_instructions_prefix? T fname c trans trans' h_step k h_k
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      unfold innerCmdLoop at h_run
      simp at h_run

/-! ## Per-block layout production

The layout_block_body theorem: each admitted `.cmd c` at position `k`
in `cmds` was emitted at offset `trans.nextLoc + cmdsPrefixInstrCount
cmds k`. We use a `pgm.instructions[i]?`-style prefix hypothesis (so
the proof avoids the dependent-type-rewrite issues of the
`?`-less form). -/

/-- Foldl-accumulator extraction: `foldl f k l = k + foldl f 0 l` for
the per-cmd instr-count function. Used in the offset calculations. -/
theorem foldl_gotoInstrCount_extract_acc :
    ∀ (l : List Core.Command) (k : Nat),
      List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) k l =
      k + List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 l := by
  intro l
  induction l with
  | nil => simp
  | cons hd tl ih =>
    intro k
    simp only [List.foldl]
    rw [ih (k + Core.CmdExt.gotoInstrCount hd),
        ih (0 + Core.CmdExt.gotoInstrCount hd)]
    omega

/-- Per-Cmd nextLoc-advance: `Cmd.toGotoInstructions T fname c trans
= .ok ans` implies `ans.nextLoc = trans.nextLoc +
Imperative.Cmd.gotoInstrCount c`. -/
theorem toGotoInstructions_nextLoc_advance
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans) :
    ans.nextLoc = trans.nextLoc + Imperative.Cmd.gotoInstrCount c := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_next]; rfl
    | nondet =>
      obtain ⟨_, _, _, _, _, _, _, h_next, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_next]; rfl
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, _, _, _, _, _, _, _, h_next⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_next]; rfl
    | nondet =>
      obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_next]; rfl
  | assert label e md =>
    obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_next]; rfl
  | assume label e md =>
    obtain ⟨_, _, _, _, _, _, _, h_next⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_next]; rfl
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      rw [← h_run]; rfl
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- The full per-block layout theorem: each admitted `.cmd c` at
position `k` in `cmds` was emitted at offset `trans.nextLoc +
cmdsPrefixInstrCount cmds k`. -/
theorem innerCmdLoop_layout_block_body
    (T : Core.Expression.TyEnv) (fname : String)
    (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : innerCmdLoop T fname cmds trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_admitted :
      ∀ (k : Nat) (h : k < cmds.length),
        Core.CmdExt.isAdmittedCmd (cmds[k]'h) = true)
    (h_prefix :
      ∀ (k : Nat) (h : k < ans.instructions.size),
        pgm.instructions[k]? = some ans.instructions[k]) :
    ∀ (k : Nat) (inner : Imperative.Cmd Core.Expression)
      (h : k < cmds.length),
      cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (trans.nextLoc + cmdsPrefixInstrCount cmds k) inner := by
  induction cmds generalizing T trans with
  | nil =>
    intro k inner h_lt _
    simp at h_lt
  | cons cmd rest ih =>
    intro k inner h_lt h_at
    cases cmd with
    | cmd c =>
      unfold innerCmdLoop at h_run
      match h_step :
          Imperative.Cmd.toGotoInstructions T fname c trans with
      | .ok trans' =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        match k with
        | 0 =>
          -- Head case. h_at : (.cmd c) = .cmd inner, so after simp,
          -- h_at : c = inner.
          simp at h_at
          -- We substitute `inner` (the binding from `intro inner`) with
          -- `c` (the case-split variable). h_at says they're equal.
          rw [← h_at]
          -- Now goal mentions `c` in place of `inner`.
          have h_prefix0 : cmdsPrefixInstrCount (Core.CmdExt.cmd c :: rest) 0 = 0 :=
            rfl
          rw [h_prefix0, Nat.add_zero]
          -- Build h_prefix' for trans' from h_prefix on ans.
          have h_prefix' :
              ∀ (k : Nat) (h : k < trans'.instructions.size),
                pgm.instructions[k]? = some trans'.instructions[k] := by
            intro k h_k
            have h_size' : trans'.instructions.size = trans'.nextLoc :=
              toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
            have h_size_le_ans :
                trans'.instructions.size ≤ ans.instructions.size :=
              innerCmdLoop_size_le trans'.T fname rest trans' ans h_run
            have h_k_ans : k < ans.instructions.size := by omega
            have h_eq_q :
                ans.instructions[k]? = trans'.instructions[k]? :=
              innerCmdLoop_instructions_prefix? trans'.T fname rest trans' ans h_run k h_k
            rw [h_prefix k h_k_ans]
            rw [Array.getElem?_eq_getElem h_k_ans] at h_eq_q
            rw [Array.getElem?_eq_getElem h_k] at h_eq_q
            injection h_eq_q with h_eq_q
            rw [h_eq_q]
          have h_admitted0 := h_admitted 0 (by simp)
          exact cmdEmittedAt_of_toGotoInstructions
            T fname c h_admitted0 trans trans' h_step h_size
            pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_prefix'
        | k + 1 =>
          -- Tail case: recurse.
          have h_admitted' :
              ∀ (k' : Nat) (h : k' < rest.length),
                Core.CmdExt.isAdmittedCmd (rest[k']'h) = true := by
            intro k' h_k'
            have : k' + 1 < (Core.CmdExt.cmd c :: rest).length := by
              show Nat.succ k' < Nat.succ rest.length
              exact Nat.succ_lt_succ h_k'
            have := h_admitted (k' + 1) this
            simpa using this
          have h_lt_rest : k < rest.length := by
            simp at h_lt
            exact Nat.lt_of_succ_lt_succ (Nat.succ_lt_succ h_lt)
          have h_at_rest : rest[k]'h_lt_rest = .cmd inner := by
            have := h_at
            simp at this
            exact this
          have h_size' : trans'.instructions.size = trans'.nextLoc :=
            toGotoInstructions_preserves_size_eq T fname c trans trans' h_step h_size
          have h_advance :
              trans'.nextLoc = trans.nextLoc + Imperative.Cmd.gotoInstrCount c :=
            toGotoInstructions_nextLoc_advance T fname c trans trans' h_step
          have h_ih := ih trans'.T trans' h_run h_size' h_admitted' k inner h_lt_rest h_at_rest
          -- Adjust the offset.
          have h_offset_eq :
              trans'.nextLoc + cmdsPrefixInstrCount rest k =
              trans.nextLoc + cmdsPrefixInstrCount (Core.CmdExt.cmd c :: rest) (k + 1) := by
            rw [h_advance]
            -- cmdsPrefixInstrCount (cmd c :: rest) (k+1)
            --   = ((cmd c :: rest).take (k+1)).foldl ...
            --   = (cmd c :: rest.take k).foldl ...
            -- via List.take_succ_cons.
            simp only [cmdsPrefixInstrCount, List.take_succ_cons, List.foldl]
            -- Apply foldl-acc-extraction lemma to factor out the initial
            -- accumulator.
            rw [foldl_gotoInstrCount_extract_acc (rest.take k)
                (0 + Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c))]
            -- Both sides have foldl 0 (rest.take k) plus various
            -- Imperative.Cmd.gotoInstrCount c terms.
            -- Core.CmdExt.gotoInstrCount (.cmd c) = Imperative.Cmd.gotoInstrCount c.
            show trans.nextLoc + Imperative.Cmd.gotoInstrCount c +
                cmdsPrefixInstrCount rest k =
              trans.nextLoc + (0 + Core.CmdExt.gotoInstrCount (Core.CmdExt.cmd c) +
                List.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 (rest.take k))
            simp [cmdsPrefixInstrCount, Core.CmdExt.gotoInstrCount]
            omega
          rw [h_offset_eq] at h_ih
          exact h_ih
      | .error _ =>
        simp only [h_step, Except.mapError, Bind.bind, Except.bind] at h_run
        cases h_run
    | call _ _ _ =>
      have h_contra := h_admitted 0 (by simp)
      simp [Core.CmdExt.isAdmittedCmd] at h_contra


end -- public section

end CProverGOTO
