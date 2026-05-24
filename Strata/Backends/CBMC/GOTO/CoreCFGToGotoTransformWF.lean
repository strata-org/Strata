/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOInvariants
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline
public import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOCorrect
public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF.Shape
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

/-! # Discharging `WellFormedTranslation` against `coreCFGToGotoTransform`

This module proves that the program output by
`Strata.coreCFGToGotoTransform` (composed with
`procedureToGotoCtxViaCFG`) satisfies the `WellFormedTranslation`
predicate consumed by `CProverGOTO.coreCFGToGoto_forward_simulation`.

The file is organised in three layers:

1. **Per-`Cmd` shape lemmas** (`Cmd_toGotoInstructions_*_ok`): for each
   constructor of `Imperative.Cmd Core.Expression` (in the admitted
   fragment), the resulting `GotoTransform` has a precisely-described
   `instructions` suffix appended and `nextLoc` advanced by exactly
   `Imperative.Cmd.gotoInstrCount`.

2. **Emit-helper shape lemmas** (`emitLabel_shape`, `emitCondGoto_shape`,
   `emitUncondGoto_shape`): one-liners characterising each helper's
   suffix.

3. **`patchGotoTargets` invariants**: the second pass mutates only the
   `target` field, so all type/guard/code/locationNum invariants
   transfer through patching unchanged.

These layers compose into `coreCFGToGotoTransform_wellFormed_nonempty`
and the strengthened `coreCFGToGotoTransform_wellFormed_strengthened`
at the bottom of the module.
-/

namespace CProverGOTO

open Imperative

public section

/-- An empty `LabelMap`: returns `none` for every label. -/
@[expose] def emptyLabelMap : LabelMap := fun _ => none

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
private theorem foldl_gotoInstrCount_extract_acc :
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

/-! ## LabelMap operations and invariants

The translator threads a `Std.HashMap String Nat` for `labelMap`,
inserting `label ↦ trans.nextLoc` at the start of each outer-loop
iteration. We model the labelMap as a `LabelMap = String → Option Nat`
function, which is the form `WellFormedTranslation` consumes.

The key operation: extending an existing `labelMap` with `label ↦ pc`.
This only preserves injectivity when `label` is fresh (not already in
the map's domain), which corresponds to the implicit
`BlockLabelsDistinct cfg` requirement on the input CFG. -/

/-- Extend a `LabelMap` with one new `label ↦ pc` mapping. -/
@[expose] def labelMapInsert
    (m : LabelMap) (label : String) (pc : Nat) : LabelMap :=
  fun l => if l = label then some pc else m l

/-- After `labelMapInsert`, the inserted label resolves to its `pc`. -/
@[simp] theorem labelMapInsert_self
    (m : LabelMap) (label : String) (pc : Nat) :
    (labelMapInsert m label pc) label = some pc := by
  unfold labelMapInsert
  simp

/-- After `labelMapInsert`, an unrelated label resolves the same as in
the original map. -/
@[simp] theorem labelMapInsert_other
    (m : LabelMap) (label l : String) (pc : Nat) (h : l ≠ label) :
    (labelMapInsert m label pc) l = m l := by
  unfold labelMapInsert
  simp [h]

/-- Convert a `Std.HashMap String Nat` to a `LabelMap = String →
Option Nat` via `m.get?`. The translator's `CoreCFGTransLoopState`
threads a `HashMap`; the `WellFormedTranslation` consumer expects a
function form. -/
@[expose] def hashMapToLabelMap (m : Std.HashMap String Nat) : LabelMap :=
  fun l => m[l]?

/-- The empty hashmap converts to `emptyLabelMap`. -/
@[simp] theorem hashMapToLabelMap_empty :
    hashMapToLabelMap (∅ : Std.HashMap String Nat) = emptyLabelMap := by
  funext l
  unfold hashMapToLabelMap emptyLabelMap
  simp

/-! ## Per-cmd / per-block step preservation

`coreCFGToGotoTransform` is structured as

```
cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) initSt
  >>= λ st => st.pendingPatches.foldlM (Strata.coreCFGToGotoPatchStep ..) ([], st.trans)
  >>= λ (resolved, trans) => Imperative.patchGotoTargets trans resolved
```

with named per-cmd / per-block / per-patch step functions. The
preservation lemmas below characterise each step's effect on the
partial `WellFormedTranslation` invariant. -/

/-- The per-cmd step `Strata.coreCFGToGotoCmdStep` agrees with
`Cmd.toGotoInstructions` on the `.cmd c` case, and produces a single
appended FUNCTION_CALL instruction on the `.call` case. -/
theorem coreCFGToGotoCmdStep_cmd
    (fname : String) (c : Imperative.Cmd Core.Expression)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv) :
    Strata.coreCFGToGotoCmdStep fname trans (.cmd c) =
      Imperative.Cmd.toGotoInstructions trans.T fname c trans := by
  unfold Strata.coreCFGToGotoCmdStep
  rfl

/-- The per-cmd step preserves `instructions.size = nextLoc` on
admitted commands (i.e., `.cmd c`; `.call` is rejected by
`isAdmittedCmd`). -/
theorem coreCFGToGotoCmdStep_preserves_size_eq
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_size_eq trans.T fname c trans ans h_run h_size
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The per-cmd step preserves `locationNum = index` on admitted
commands. -/
theorem coreCFGToGotoCmdStep_preserves_locationNum_eq_index
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_locationNum_eq_index
      trans.T fname c trans ans h_run h_size h_loc
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold via `foldlM` preserves `size_eq`, when each cmd is
admitted by `isAdmittedCmd`. -/
theorem cmdsFoldlM_preserves_size_eq
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc) :
    ans.instructions.size = ans.nextLoc := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The cmds-fold via `foldlM` preserves `locationNum_eq_index`. -/
theorem cmdsFoldlM_preserves_locationNum_eq_index
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_size : trans.instructions.size = trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size' : trans'.instructions.size = trans'.nextLoc :=
        coreCFGToGotoCmdStep_preserves_size_eq fname cmd trans trans'
          h_admitted_cmd h_step h_size
      have h_loc' :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            trans'.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoCmdStep_preserves_locationNum_eq_index
          fname cmd trans trans' h_admitted_cmd h_step h_size h_loc
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      exact ih trans' h_admitted_rest h_run h_size' h_loc'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-cmd step's `nextLoc` advance equals `Core.CmdExt.gotoInstrCount cmd`. -/
theorem coreCFGToGotoCmdStep_nextLoc_advance
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    ans.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    have := toGotoInstructions_nextLoc_advance trans.T fname c trans ans h_run
    rw [this]
    rfl
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold's `nextLoc` advance equals `DetBlockBodyInstrCount`
applied to a synthetic block. -/
theorem cmdsFoldlM_nextLoc_advance
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    ans.nextLoc =
      trans.nextLoc + cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; simp
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_advance' : trans'.nextLoc = trans.nextLoc + Core.CmdExt.gotoInstrCount cmd :=
        coreCFGToGotoCmdStep_nextLoc_advance fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run
      rw [h_ih, h_advance']
      -- Goal: trans.nextLoc + gotoInstrCount cmd + foldl (+) 0 rest =
      --        trans.nextLoc + foldl (+) 0 (cmd :: rest)
      simp only [List.foldl]
      rw [foldl_gotoInstrCount_extract_acc rest (0 + Core.CmdExt.gotoInstrCount cmd)]
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Per-block step preservation

The per-block step's body is a sequence of three pieces: `emitLabel`,
`block.cmds.foldlM coreCFGToGotoCmdStep`, and the transfer-emit branch
(condGoto or finish). The lemmas below establish that this composition
preserves `size_eq` and `locationNum_eq_index`. -/

/-- The per-block step preserves `size_eq` (admitted cmds only). -/
theorem coreCFGToGotoBlockStep_preserves_size_eq
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel produces a state with size_eq.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  -- Unfold the step function and the inner do-block.
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  -- Now `h_run` has shape `match (foldlM ...) with .ok x => match transfer with ... | .error => Except.error _`.
  -- Case on the inner-fold result.
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    -- h_run now is `(match transfer ...) = Except.ok st'`. Case on transfer.
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push, h_size₂]
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push, h_size₂]
  | .error e, h_inner =>
    simp at h_run

/-- The per-block step preserves `locationNum_eq_index`. -/
theorem coreCFGToGotoBlockStep_preserves_locationNum_eq_index
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel preserves size_eq + locationNum_eq_index.
  have h_size₁ :
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).instructions.size =
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname }
        st.trans).nextLoc :=
    emitLabel_preserves_size_eq label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
  have h_loc₁ :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[i]? = some instr → instr.locationNum = i :=
    emitLabel_preserves_locationNum_eq_index label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size h_loc
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_size₂ : trans₂.instructions.size = trans₂.nextLoc :=
      cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁
    have h_loc₂ :
        ∀ (i : Nat) (instr : CProverGOTO.Instruction),
          trans₂.instructions[i]? = some instr → instr.locationNum = i :=
      cmdsFoldlM_preserves_locationNum_eq_index fname blk.cmds _ trans₂
        h_admitted h_inner h_size₁ h_loc₁
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, h_cond_eval =>
        simp only at h_run
        injection h_run with h_run
        intro i instr h
        rw [← h_run] at h
        -- After two emitGoto pushes, the array has 2 more instructions.
        -- Use emitCondGoto / emitUncondGoto preservation lemmas.
        have h_after_neg :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst.instructions[i]? = some instr → instr.locationNum = i :=
          emitCondGoto_preserves_locationNum_eq_index
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂ h_loc₂
        have h_after_neg_size :
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.instructions.size =
          (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            trans₂).fst.nextLoc :=
          emitCondGoto_preserves_size_eq
            (CProverGOTO.Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_size₂
        have h_after_uncond :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            (Imperative.emitUncondGoto
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              (Imperative.emitCondGoto (CProverGOTO.Expr.not cond_expr)
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                trans₂).fst).fst.instructions[i]? = some instr →
            instr.locationNum = i :=
          emitUncondGoto_preserves_locationNum_eq_index
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
            _ h_after_neg_size h_after_neg
        exact h_after_uncond i instr h
      | .error e, h_cond_eval =>
        simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      intro i instr h
      rw [← h_run] at h
      -- After pushing 1 END_FUNCTION, locationNum_eq_index transfers via
      -- a generic push lemma.
      exact endFunction_emit_preserves_locationNum_eq_index md fname trans₂ h_size₂ h_loc₂ i instr h
  | .error e, h_inner =>
    simp at h_run

/-! ### Per-block step layout effects

The per-block step's effect on `st`'s fields:
* `st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc`
* `st'.trans.nextLoc = st.trans.nextLoc + 1 + bodyCount + transferCount`
* The block's pc (= `st.trans.nextLoc`) addresses a LOCATION instruction
  in `st'.trans.instructions` (the leading `emitLabel` push).
* For `.finish md`: position `pc + 1 + bodyCount` holds an END_FUNCTION.
* For `.condGoto cond lt lf md`: positions `pc + 1 + bodyCount` and
  `pc + 1 + bodyCount + 1` hold two GOTOs (target = none, guard =
  `e_goto.not` and `Expr.true` respectively).
* The pendingPatches array is extended by two patches for `.condGoto`
  blocks; preserved for `.finish` blocks. -/

/-- The per-block step's effect on `st.labelMap` is to insert
`lblBlk.1 ↦ st.trans.nextLoc`. -/
theorem coreCFGToGotoBlockStep_labelMap
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, _ =>
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.finish md`
blocks: it advances by `1 + bodyCount + 1` (the trailing `+1` is the
END_FUNCTION push). -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_finish
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    injection h_run with h_run
    rw [← h_run]
    show trans₂.nextLoc + 1 = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1
    omega
  | .error _, _ => simp at h_run

/-- The per-block step's effect on `st.trans.nextLoc` for `.condGoto`
blocks: it advances by `1 + bodyCount + 2`. -/
theorem coreCFGToGotoBlockStep_nextLoc_advance_condGoto
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st'.trans.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 2 := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_advance₂ :
        trans₂.nextLoc = st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk := by
      have := cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
          st.trans.nextLoc + 1 := rfl
      rw [h_after_label] at this
      rw [this]
      simp [DetBlockBodyInstrCount]
    rw [h_transfer] at h_run
    simp only at h_run
    generalize h_cond_eval :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
    match cond_eval, h_cond_eval with
    | .ok cond_expr, _ =>
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      omega
    | .error _, _ => simp at h_run
  | .error _, _ => simp at h_run

/-! ### Per-block step instruction-array prefix preservation

The per-block step only appends to `trans.instructions`. This means
positions `[0, st.trans.instructions.size)` keep the same instruction
through the block step. Composed with foldlM, this gives positions
`[0, st_initial.trans.instructions.size)` retaining their original
contents through all blocks. -/

/-- Each step in `cmdsFoldlM` only grows the instruction array. -/
theorem coreCFGToGotoCmdStep_size_le
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_size_le trans.T fname c trans ans h_run
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- Each step in `cmdsFoldlM` preserves the instruction-array prefix
on `?`-lookups. -/
theorem coreCFGToGotoCmdStep_instructions_prefix?
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : Core.CmdExt.isAdmittedCmd cmd = true)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_instructions_prefix? trans.T fname c trans ans h_run k h
  | call _ _ _ =>
    simp [Core.CmdExt.isAdmittedCmd] at h_admitted

/-- The cmds-fold preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `ans` as in `trans`. -/
theorem cmdsFoldlM_instructions_prefix?
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (k : Nat) (h : k < trans.instructions.size) :
    ans.instructions[k]? = trans.instructions[k]? := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_size_le : trans.instructions.size ≤ trans'.instructions.size :=
        coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_k' : k < trans'.instructions.size := Nat.lt_of_lt_of_le h h_size_le
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have h_ih := ih trans' h_admitted_rest h_run h_k'
      rw [h_ih]
      exact coreCFGToGotoCmdStep_instructions_prefix? fname cmd trans trans' h_admitted_cmd h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- `cmdsFoldlM_size_le` — the cmds-fold only grows the instruction
array. -/
theorem cmdsFoldlM_size_le
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    trans.instructions.size ≤ ans.instructions.size := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_le := coreCFGToGotoCmdStep_size_le fname cmd trans trans' h_admitted_cmd h_step
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      have := ih trans' h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The per-block step only grows the instruction array. -/
theorem coreCFGToGotoBlockStep_size_le
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push]
        omega
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      simp [Array.size_push]
      omega
  | .error _, _ => simp at h_run

/-- The per-block step preserves the instruction-array prefix on
`?`-lookups: any index `k` below the input size returns the same
instruction in `st'.trans` as in `st.trans`. -/
theorem coreCFGToGotoBlockStep_instructions_prefix?
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- emitLabel(...).instructions = st.trans.instructions.push <new>
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_k_after_label :
        k < (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_label_lookup :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? = st.trans.instructions[k]? := by
      rw [h_label_unfold]
      rw [Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]
    have h_inner_prefix :
        trans₂.instructions[k]? =
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[k]? :=
      cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner k h_k_after_label
    have h_inner_size_le :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size ≤ trans₂.instructions.size :=
      cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        have h_k_in_post_first :
            k < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_k_in_post_first,
            Array.getElem_push_lt h_k_in_trans₂,
            ← Array.getElem?_eq_getElem h_k_in_trans₂]
        rw [h_inner_prefix, h_label_lookup]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_k_in_trans₂ : k < trans₂.instructions.size := by omega
      rw [Array.getElem?_push_lt h_k_in_trans₂,
          ← Array.getElem?_eq_getElem h_k_in_trans₂]
      rw [h_inner_prefix, h_label_lookup]
  | .error _, _ => simp at h_run

/-! ### Per-block step layout post-conditions

After one block step, certain instructions are at specific positions in
`st'.trans.instructions`:

* The LOCATION instruction is at `st.trans.nextLoc`.
* For `.finish md` blocks: the END_FUNCTION is at `st.trans.nextLoc + 1
  + bodyCount`.
* For `.condGoto cond lt lf md` blocks: two GOTOs at `st.trans.nextLoc
  + 1 + bodyCount` (guard `e_goto.not`, target `none`) and at `+1`
  (guard `Expr.true`, target `none`).

These results are stable through subsequent block steps because of
`coreCFGToGotoBlockStep_instructions_prefix?`. -/

/-- After one block step, the LOCATION instruction is at
`st.trans.nextLoc` in `st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_location_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc]? = some instr ∧
      instr.type = .LOCATION := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- The LOCATION instruction is the LAST one pushed by emitLabel.
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_label_at :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [h_label_unfold, Array.getElem?_push_eq]
    -- Show that the inner cmds-fold preserves this LOCATION.
    have h_pc_lt : st.trans.instructions.size <
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_pc_in_trans₂ :
        trans₂.instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner _ h_pc_lt]
      exact h_label_at
    -- pc = st.trans.nextLoc = st.trans.instructions.size by h_size.
    have h_pc_eq : st.trans.nextLoc = st.trans.instructions.size := h_size.symm
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        rw [h_pc_eq]
        have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
          have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
          rw [h_label_size] at this; omega
        have h_pc_in_first :
            st.trans.instructions.size < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_pc_in_first,
            Array.getElem_push_lt h_pc_in_trans₂_size,
            ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
        rw [h_pc_in_trans₂]
        exact ⟨_, rfl, rfl⟩
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      rw [h_pc_eq]
      have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
        have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
        rw [h_label_size] at this; omega
      rw [Array.getElem?_push_lt h_pc_in_trans₂_size,
          ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
      rw [h_pc_in_trans₂]
      exact ⟨_, rfl, rfl⟩
  | .error _, _ => simp at h_run

/-- Strengthened version of `coreCFGToGotoBlockStep_location_at_pc`:
the LOCATION instruction at `st.trans.nextLoc` carries the block's
label in its `labels` field — exactly `[label]`. Used to pin
`wf.labelMap l` to the translator's hashmap-keyed labelMap by
exhibiting at most one LOCATION per label. -/
theorem coreCFGToGotoBlockStep_location_at_pc_with_labels
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc]? = some instr ∧
      instr.type = .LOCATION ∧
      instr.labels = [lblBlk.1] := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_unfold :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions =
        st.trans.instructions.push
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := rfl
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      rw [h_label_unfold, Array.size_push]
    have h_label_at :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [h_label_unfold, Array.getElem?_push_eq]
    have h_pc_lt : st.trans.instructions.size <
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size := by
      rw [h_label_size]; omega
    have h_pc_in_trans₂ :
        trans₂.instructions[st.trans.instructions.size]? = some
          { type := .LOCATION, locationNum := st.trans.nextLoc,
            sourceLoc := { CProverGOTO.SourceLocation.nil with function := fname },
            labels := [label], code := CProverGOTO.Code.skip } := by
      rw [cmdsFoldlM_instructions_prefix? fname blk.cmds _ trans₂ h_admitted h_inner _ h_pc_lt]
      exact h_label_at
    have h_pc_eq : st.trans.nextLoc = st.trans.instructions.size := h_size.symm
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        rw [h_pc_eq]
        have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
          have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
          rw [h_label_size] at this; omega
        have h_pc_in_first :
            st.trans.instructions.size < (trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc, target := .none }).size := by
          simp [Array.size_push]; omega
        rw [Array.getElem?_push_lt h_pc_in_first,
            Array.getElem_push_lt h_pc_in_trans₂_size,
            ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
        rw [h_pc_in_trans₂]
        exact ⟨_, rfl, rfl, rfl⟩
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      rw [h_pc_eq]
      have h_pc_in_trans₂_size : st.trans.instructions.size < trans₂.instructions.size := by
        have := cmdsFoldlM_size_le fname blk.cmds _ trans₂ h_admitted h_inner
        rw [h_label_size] at this; omega
      rw [Array.getElem?_push_lt h_pc_in_trans₂_size,
          ← Array.getElem?_eq_getElem h_pc_in_trans₂_size]
      rw [h_pc_in_trans₂]
      exact ⟨_, rfl, rfl, rfl⟩
  | .error _, _ => simp at h_run

/-- After one block step on a `.finish md` block, the END_FUNCTION
instruction is at `st.trans.nextLoc + 1 + bodyCount` in
`st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_finish_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .finish md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr ∧
      instr.type = .END_FUNCTION := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    injection h_run with h_run
    rw [← h_run]
    -- After the END_FUNCTION push, position trans₂.instructions.size = pc + 1 + bodyCount
    -- holds the new END_FUNCTION instruction.
    have h_target_eq :
        st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
      rw [h_inner_size]; omega
    rw [h_target_eq]
    refine ⟨{ type := .END_FUNCTION, locationNum := trans₂.nextLoc,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText }, ?_, rfl⟩
    show (trans₂.instructions.push _)[trans₂.instructions.size]? = some _
    exact Array.getElem?_push_size
  | .error _, _ => simp at h_run

/-- After one block step on a `.condGoto cond lt lf md` block, two GOTO
instructions appear at `st.trans.nextLoc + 1 + bodyCount` (guard
`e_goto.not`, target `none`) and at `+1` (guard `Expr.true`, target
`none`). -/
theorem coreCFGToGotoBlockStep_condGoto_at_pc
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    ∃ instr_neg instr_uncond e_goto,
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2]? = some instr_neg ∧
      instr_neg.type = .GOTO ∧
      instr_neg.target = none ∧
      instr_neg.guard = e_goto.not ∧
      Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = .ok e_goto ∧
      st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1]? = some instr_uncond ∧
      instr_uncond.type = .GOTO ∧
      instr_uncond.target = none ∧
      instr_uncond.guard = CProverGOTO.Expr.true := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    -- Use generalize-with-equation style to keep h_eq usable.
    -- We must `revert h_run` to expose the type containing the LHS of the cond_eval.
    revert h_run
    generalize h_eq :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = res
    intro h_run
    -- Capture h_eq into the existential pre-emptively.
    -- Re-state h_eq before the cases analysis (so it's not over a substituted res).
    cases res with
    | error _ => simp at h_run
    | ok cond_expr =>
      -- Now h_eq : ... = Except.ok cond_expr.
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      have h_pc_neg_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
        rw [h_inner_size]; omega
      have h_pc_uncond_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 = trans₂.instructions.size + 1 := by
        rw [h_inner_size]; omega
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      have h_neg :
          ((trans₂.instructions.push
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc }).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size]?
          = some
              { type := .GOTO, guard := cond_expr.not,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc } := by
        rw [Array.getElem?_push_lt (by simp [Array.size_push])]
        congr 1
        exact Array.getElem_push_eq
      -- For h_uncond, use the fact that pushing onto an array of size n+1 makes
      -- the new last element accessible via getElem? at index n+1.
      -- We use `Array.getElem?_push_size` after rewriting.
      have h_uncond :
          ((trans₂.instructions.push
              ({ type := .GOTO, guard := cond_expr.not,
                 sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                 locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).push
            { type := .GOTO, guard := CProverGOTO.Expr.true,
              sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
              locationNum := trans₂.nextLoc + 1 })[trans₂.instructions.size + 1]?
          = some
              { type := .GOTO, guard := CProverGOTO.Expr.true,
                sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                locationNum := trans₂.nextLoc + 1 } := by
        let arr1 := trans₂.instructions.push
            ({ type := .GOTO, guard := cond_expr.not,
               sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
               locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)
        have h_size_inner : arr1.size = trans₂.instructions.size + 1 := by
          simp [arr1, Array.size_push]
        show (arr1.push _)[trans₂.instructions.size + 1]? = _
        rw [← h_size_inner]
        exact Array.getElem?_push_size
      refine ⟨_, _, cond_expr, by rw [h_pc_neg_eq]; exact h_neg, rfl, rfl, rfl, ?_,
        by rw [h_pc_uncond_eq]; exact h_uncond, rfl, rfl, rfl⟩
      -- h_eq has the form `Lambda.LExpr.toGotoExprCtx [] cond = Except.ok cond_expr`,
      -- but simp may have already substituted in the goal; either way, rfl or h_eq
      -- works.
      first | rfl | exact h_eq
  | .error _, _ => simp at h_run

/-- The outer-loop fold preserves `size_eq` if every block's body is
admitted. -/
theorem blocksFoldlM_preserves_size_eq
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    st'.trans.instructions.size = st'.trans.nextLoc := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer-loop fold preserves `locationNum_eq_index`. -/
theorem blocksFoldlM_preserves_locationNum_eq_index
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st.trans.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      st'.trans.instructions[i]? = some instr → instr.locationNum = i := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname head st st₁ h_admitted_head h_step h_size
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            st₁.trans.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoBlockStep_preserves_locationNum_eq_index fname head st st₁
          h_admitted_head h_step h_size h_loc
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_loc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Outer-loop foldlM layout-fact preservation

The per-block layout facts (LOCATION at pc, END_FUNCTION/condGoto-pair
at the end of the block) need to be propagated through subsequent
block iterations using `coreCFGToGotoBlockStep_instructions_prefix?`.

The labelMap accumulates entries for each processed block; we need
that distinct block labels stay distinct in the final HashMap. -/

/-- The outer foldlM only grows the instruction array. -/
theorem blocksFoldlM_size_le
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st') :
    st.trans.instructions.size ≤ st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact Nat.le_refl _
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have := ih st₁ h_admitted_rest h_run
      omega
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The outer foldlM preserves the instruction-array prefix. -/
theorem blocksFoldlM_instructions_prefix?
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (k : Nat) (h : k < st.trans.instructions.size) :
    st'.trans.instructions[k]? = st.trans.instructions[k]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_le := coreCFGToGotoBlockStep_size_le fname head st st₁ h_admitted_head h_step
      have h_k₁ : k < st₁.trans.instructions.size := Nat.lt_of_lt_of_le h h_le
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_ih := ih st₁ h_admitted_rest h_run h_k₁
      rw [h_ih]
      exact coreCFGToGotoBlockStep_instructions_prefix? fname head st st₁ h_admitted_head h_step k h
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Layout-fact propagation through foldlM

For each `(l, blk)` in the processed prefix, we want the LOCATION,
END_FUNCTION, or condGoto-pair of that block to remain in the final
`st_final.trans.instructions` array at the same offset. The position
of the block (the snapshot of `nextLoc` at the start of the block's
iteration) is captured by walking the foldlM with an accumulator.

The labelMap accumulates entries — block `i` inserts `(label_i ↦
pc_i)`. Subsequent iterations may overwrite if `label_j = label_i` for
`j > i`. To ensure the labelMap-correspondence works, we require
distinct labels (`BlockLabelsDistinct`).

These lemmas thread a `BlockLabelsDistinct` hypothesis: the labels of
all blocks in `blocks` are pairwise distinct. -/

/-- A list of blocks has pairwise distinct labels. -/
@[expose] def BlockLabelsDistinct
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression)) :
    Prop :=
  List.Pairwise (fun a b => a.1 ≠ b.1) blocks

/-- A `Pairwise` distinctness on labels implies any element's label is
distinct from all subsequent labels. -/
theorem BlockLabelsDistinct_head_neq_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    ∀ p ∈ rest, head.1 ≠ p.1 := by
  unfold BlockLabelsDistinct at h
  cases h with
  | cons h_head h_rest =>
    intro p h_in
    exact h_head p h_in

/-- A `Pairwise` distinctness on the tail. -/
theorem BlockLabelsDistinct_tail
    (head : String × Imperative.DetBlock String Core.Command Core.Expression)
    (rest : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (h : BlockLabelsDistinct (head :: rest)) :
    BlockLabelsDistinct rest := by
  unfold BlockLabelsDistinct at h ⊢
  cases h with
  | cons _ h_rest => exact h_rest

/-- After the foldlM, if a label is in the labelMap of the input
state, it remains the same in the output state — provided the label is
not the head of any block in the processed list (because each block's
step only inserts its own label). -/
theorem blocksFoldlM_labelMap_preserves_external
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (l : String) (h_not_in : ∀ p ∈ blocks, p.1 ≠ l) :
    st'.labelMap[l]? = st.labelMap[l]? := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ head.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted head (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_lbl₁ : st₁.labelMap = st.labelMap.insert head.1 st.trans.nextLoc :=
        coreCFGToGotoBlockStep_labelMap fname head st st₁ h_step
      have h_not_l_head : head.1 ≠ l := h_not_in head (by simp)
      have h_not_l_rest : ∀ p ∈ rest, p.1 ≠ l := fun p hp => h_not_in p (by simp [hp])
      have h_ih := ih st₁ h_admitted_rest h_run h_not_l_rest
      rw [h_ih, h_lbl₁]
      rw [Std.HashMap.getElem?_insert]
      have h_l_neq : ¬ head.1 = l := h_not_l_head
      simp [h_l_neq]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that the foldlM produces
`st_final`, there exists a `pc` with:
* `st_final.labelMap[l]? = some pc`
* `st_final.trans.instructions[pc]? = some instr` and `instr.type = .LOCATION`
* `pc < st_final.trans.instructions.size`

The proof works by induction on `blocks`. -/
theorem blocksFoldlM_layout_location
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk, (l, blk) ∈ blocks →
      ∃ pc instr,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧
        pc < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    intro l blk h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk h_in
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st₁ : st.trans.instructions.size ≤ st₁.trans.instructions.size :=
        coreCFGToGotoBlockStep_size_le fname hd st st₁ h_admitted_head h_step
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      -- Either (l, blk) = hd, or (l, blk) ∈ rest.
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd.
        subst h_eq
        obtain ⟨instr, h_at_st₁, h_ty⟩ :=
          coreCFGToGotoBlockStep_location_at_pc fname (l, blk) st st₁ h_admitted_head h_step h_size
        have h_pc_lt_st₁ : st.trans.nextLoc < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_pc_lt_st' : st.trans.nextLoc < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_pc_lt_st₁ h_le_st'
        have h_at_st' : st'.trans.instructions[st.trans.nextLoc]? = some instr := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? := by
          exact blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr, h_lbl_st', h_at_st', h_ty, h_pc_lt_st'⟩
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Strengthened `blocksFoldlM_layout_location`: also exposes that the
LOCATION instruction's `labels` field equals `[l]`. Used to prove that
any `WellFormedTranslation`'s `labelMap l` agrees with the translator's
hashmap-keyed labelMap on `cfg.blocks` labels. -/
theorem blocksFoldlM_layout_location_with_labels
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk, (l, blk) ∈ blocks →
      ∃ pc instr,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧
        instr.labels = [l] ∧
        pc < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    intro l blk h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk h_in
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st₁ : st.trans.instructions.size ≤ st₁.trans.instructions.size :=
        coreCFGToGotoBlockStep_size_le fname hd st st₁ h_admitted_head h_step
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd.
        subst h_eq
        obtain ⟨instr, h_at_st₁, h_ty, h_labels⟩ :=
          coreCFGToGotoBlockStep_location_at_pc_with_labels fname (l, blk) st st₁
            h_admitted_head h_step h_size
        have h_pc_lt_st₁ : st.trans.nextLoc < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_pc_lt_st' : st.trans.nextLoc < st'.trans.instructions.size :=
          Nat.lt_of_lt_of_le h_pc_lt_st₁ h_le_st'
        have h_at_st' : st'.trans.instructions[st.trans.nextLoc]? = some instr := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? := by
          exact blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr, h_lbl_st', h_at_st', h_ty, h_labels, h_pc_lt_st'⟩
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For each `(l, blk) ∈ blocks` such that `blk.transfer = .finish md`,
the foldlM puts an END_FUNCTION at `pc + 1 + bodyCount` for the
appropriate pc. -/
theorem blocksFoldlM_layout_finish
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk md, (l, blk) ∈ blocks → blk.transfer = .finish md →
      ∃ pc instr_end,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_end ∧
        instr_end.type = .END_FUNCTION := by
  induction blocks generalizing st with
  | nil =>
    intro l blk md h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk md h_in h_transfer
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · subst h_eq
        -- (l, blk) is the head; transfer is .finish md.
        obtain ⟨instr_end, h_at_st₁, h_ty⟩ :=
          coreCFGToGotoBlockStep_finish_at_pc fname (l, blk) st st₁ md h_transfer h_admitted_head h_step h_size
        -- Propagate through the rest of the foldlM.
        have h_pc_lt_st₁ : st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_st₁
          exact h_at_st₁.1
        have h_at_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk]? =
              some instr_end := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_lt_st₁]
          exact h_at_st₁
        -- Now show st'.labelMap[l]? = some st.trans.nextLoc.
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        refine ⟨st.trans.nextLoc, instr_end, h_lbl_st', h_at_st', h_ty⟩
      · -- Apply IH on rest.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk md h_in_rest h_transfer
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patch-step preservation (under empty loopContracts)

The patch step (`coreCFGToGotoPatchStep`) either fails (label
unresolved), prepends `(idx, targetLoc)` to `resolvedPatches`, or also
mutates `trans.instructions[idx].guard` for loop contracts. We
discharge the patch step under the hypothesis `loopContracts = ∅`,
which is the case for any CFG without loop-invariant or loop-decreases
metadata; concrete callers verifying the WF property pass this
hypothesis. -/

/-- When `loopContracts` is empty, the patch step returns the input
`trans` unchanged (only modifies `resolvedPatches`). -/
theorem coreCFGToGotoPatchStep_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    acc'.2 = acc.2 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  cases h_lookup : labelMap[label]? with
  | none =>
    rw [h_lookup] at h_run
    simp at h_run
  | some targetLoc =>
    rw [h_lookup] at h_run
    -- With empty loopContracts, there are no entries.
    have h_lc : (∅ : Std.HashMap String (Imperative.MetaData Core.Expression))[label]? = none := by
      simp
    rw [h_lc] at h_run
    simp [pure, Except.pure] at h_run
    rw [← h_run]

/-- The patch step preserves `size_eq` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_size

/-- The patch step preserves `locationNum_eq_index` when `loopContracts` is empty. -/
theorem coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_loc

/-- The patches-fold preserves the transform under empty loop contracts. -/
theorem patchesFoldlM_no_contracts_trans_eq
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc') :
    acc'.2 = acc.2 := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; rfl
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp at h_run
      have h_eq₁ : acc₁.2 = acc.2 :=
        coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc₁ head h_step
      rw [ih acc₁ h_run, h_eq₁]
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `size_eq` (no loop contracts). -/
theorem patchesFoldlM_preserves_size_eq_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_size : acc.2.instructions.size = acc.2.nextLoc) :
    acc'.2.instructions.size = acc'.2.nextLoc := by
  -- Convert to list-foldlM for inductive reasoning.
  rw [← Array.foldlM_toList] at h_run
  -- Now `patches.toList.foldlM ... acc = .ok acc'`.
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_size
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_size₁ : acc₁.2.instructions.size = acc₁.2.nextLoc :=
        coreCFGToGotoPatchStep_preserves_size_eq_no_contracts labelMap acc acc₁ head h_step h_size
      exact ih acc₁ h_size₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The patches-fold preserves `locationNum_eq_index` (no loop contracts). -/
theorem patchesFoldlM_preserves_locationNum_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        acc.2.instructions[i]? = some instr → instr.locationNum = i) :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      acc'.2.instructions[i]? = some instr → instr.locationNum = i := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  clear h_eq
  induction patchesL generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_loc
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_loc₁ :
          ∀ (i : Nat) (instr : CProverGOTO.Instruction),
            acc₁.2.instructions[i]? = some instr → instr.locationNum = i :=
        coreCFGToGotoPatchStep_preserves_locationNum_no_contracts
          labelMap acc acc₁ head h_step h_loc
      exact ih acc₁ h_loc₁ h_run
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Structural soundness of the translator output

`coreCFGToGotoTransform_size_eq_and_loc` is the structural half of the
top-level theorem: under the right hypotheses, the translator's output
satisfies `instructions.size = nextLoc` and every instruction's
`locationNum` equals its array index. -/

/-- After the translator runs (under no-loop-contracts and admitted-cmds
hypotheses), the output `ans : GotoTransform` satisfies:
* `ans.instructions.size = ans.nextLoc`,
* every instruction's `locationNum` equals its array index. -/
theorem coreCFGToGotoTransform_size_eq_and_loc
    (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final)
    (h_loopContracts_empty : st_final.loopContracts = ∅)
    (resolved : List (Nat × Nat))
    (trans_post : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_patches_run :
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post))
    (h_ans_eq : ans = Imperative.patchGotoTargets trans_post resolved) :
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  -- Step 1: the blocks-fold preserves size_eq + locationNum_eq_index.
  have h_size_st : st_final.trans.instructions.size = st_final.trans.nextLoc :=
    blocksFoldlM_preserves_size_eq functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size
  have h_loc_st :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        st_final.trans.instructions[i]? = some instr → instr.locationNum = i :=
    blocksFoldlM_preserves_locationNum_eq_index functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb) h_blocks_run h_init_size h_init_loc
  -- Step 2: the patches-fold preserves them under the empty-loopContracts hypothesis.
  rw [h_loopContracts_empty] at h_patches_run
  have h_size_post : trans_post.instructions.size = trans_post.nextLoc :=
    patchesFoldlM_preserves_size_eq_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_size_st
  have h_loc_post :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans_post.instructions[i]? = some instr → instr.locationNum = i :=
    patchesFoldlM_preserves_locationNum_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_loc_st
  -- Step 3: patchGotoTargets preserves them.
  have h_size_ans : ans.instructions.size = ans.nextLoc := by
    rw [h_ans_eq]
    rw [patchGotoTargets_preserves_size, patchGotoTargets_preserves_nextLoc]
    exact h_size_post
  have h_loc_ans :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        ans.instructions[i]? = some instr → instr.locationNum = i := by
    intro i instr h
    rw [h_ans_eq] at h
    exact patchGotoTargets_preserves_locationNum_eq_index trans_post resolved h_loc_post i instr h
  exact ⟨h_size_ans, h_loc_ans⟩

/-! ### Translator decomposition

Initial state for the translator's forward pass and an explicit
unfolding of the translator into `do let st ← ...; let (r, t) ← ...;
return ...` form. -/

/-- Initial loop-state for `coreCFGToGotoTransform`'s forward pass. -/
@[expose] def coreCFGToGotoInitState
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    : Strata.CoreCFGTransLoopState :=
  { trans := trans₀, pendingPatches := #[], labelMap := {}, loopContracts := {} }

/-- The translator's output factors through the post-blocks-fold,
post-patches-fold, and a final `patchGotoTargets`. The proof works by
case-analysis on `cfg.blocks` to dispense with the entry-check, then
walking the two foldlM chains with `match`. -/
theorem coreCFGToGotoTransform_decompose
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∃ (st_final : Strata.CoreCFGTransLoopState)
      (resolved : List (Nat × Nat))
      (trans_post : Imperative.GotoTransform Core.Expression.TyEnv),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final ∧
      st_final.pendingPatches.foldlM
        (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
        ([], st_final.trans)
      = Except.ok (resolved, trans_post) ∧
      ans = Imperative.patchGotoTargets trans_post resolved := by
  unfold Strata.coreCFGToGotoTransform at h_run
  -- Two cases on cfg.blocks for the entry-check; both dispatch to the same body.
  -- We use a unified strategy: rewrite the entry-check to `pure ()` first when the
  -- entry condition holds; in the empty-blocks case, the entry-check is `pure ()`
  -- directly. Use `match` on cfg.blocks via h_blocks.
  match h_blocks : cfg.blocks with
  | [] =>
    -- With empty blocks, both folds are trivial and the entry-check is `pure ()`.
    -- After the `match h_blocks : cfg.blocks with | [] =>`, in this branch
    -- `cfg.blocks` may already be substituted, so we don't `rw [h_blocks]`.
    refine ⟨coreCFGToGotoInitState trans₀, [], trans₀, ?_, ?_, ?_⟩
    · -- Goal: [].foldlM ... = ok (initState trans₀). Holds by rfl.
      rfl
    · rfl
    · -- ans = patchGotoTargets trans₀ [].
      rw [h_blocks] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure, List.foldlM] at h_run
      injection h_run with h_run
      rw [← h_run]
  | (firstLabel, firstBlk) :: tail =>
    rw [h_blocks] at h_run
    simp only at h_run
    by_cases h_eq : firstLabel = cfg.entry
    · -- Entry match; if-bypassed.
      have h_neq : (firstLabel != cfg.entry) = false := by simp [h_eq]
      simp only [h_neq, Bool.false_eq_true, if_false] at h_run
      simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
      -- Match on the blocks-fold result. Use the literal initSt record so it unifies with h_run.
      generalize h_blocks_fold :
        ((firstLabel, firstBlk) :: tail).foldlM
          (Strata.coreCFGToGotoBlockStep functionName)
          ({ trans := trans₀, pendingPatches := #[], labelMap := {},
             loopContracts := {} } : Strata.CoreCFGTransLoopState)
          = blocks_fold at h_run
      match blocks_fold, h_blocks_fold with
      | .ok st_final, h_blocks_fold =>
        simp only at h_run -- reduce `match Except.ok st_final` step
        generalize h_patches_fold :
          st_final.pendingPatches.foldlM
            (Strata.coreCFGToGotoPatchStep st_final.labelMap st_final.loopContracts)
            ([], st_final.trans) = patches_fold at h_run
        match patches_fold, h_patches_fold with
        | .ok (resolved, trans_post), h_patches_fold =>
          refine ⟨st_final, resolved, trans_post, ?_, h_patches_fold, ?_⟩
          · -- Goal: ((firstLabel, firstBlk) :: tail).foldlM ... (initState trans₀) = ok st_final.
            -- (cfg.blocks already substituted by Lean's match-rewrite.)
            -- coreCFGToGotoInitState unfolds to the literal record in h_blocks_fold.
            simp only [coreCFGToGotoInitState]
            exact h_blocks_fold
          · simp only at h_run
            injection h_run with h_run; rw [← h_run]
        | .error _, _ => simp at h_run
      | .error _, _ => simp at h_run
    · -- Entry mismatch; throws.
      have h_neq : (firstLabel != cfg.entry) = true := by simp [h_eq]
      simp only [h_neq, if_true, throw, throwThe, MonadExcept.throw,
                 Bind.bind, Except.bind] at h_run
      cases h_run

/-! ### Direct structural soundness

Composes `coreCFGToGotoTransform_decompose` with
`coreCFGToGotoTransform_size_eq_and_loc` to deliver the structural
guarantees of `coreCFGToGotoTransform`'s output directly from input
hypotheses + a "post-blocks-fold loopContracts is empty" hypothesis. -/

/-- The translator's output satisfies `size_eq` and
`locationNum_eq_index`, given input hypotheses + the post-blocks-fold
hypothesis that `loopContracts` is empty (true for any CFG without
loop-invariant or decreases metadata). -/
theorem coreCFGToGotoTransform_size_eq_and_loc_direct
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ans.instructions.size = ans.nextLoc ∧
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  exact coreCFGToGotoTransform_size_eq_and_loc functionName cfg trans₀
    h_init_size h_init_loc h_admitted_blocks ans
    st_final h_blocks_run (h_loopContracts_empty_post st_final h_blocks_run)
    resolved trans_post h_patches_run h_ans_eq



/-- The hypothesis bundle for `coreCFGToGotoTransform_wellFormed_via_shadow`:
captures all the facts that an outer-loop equivalence proof must
supply about the `coreCFGToGotoTransform`'s output. -/
structure CoreCFGToGotoTransformShadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression) where
  /-- The final labelMap, total over `cfg.blocks`. -/
  finalLabelMap : LabelMap
  /-- Every CFG block label has a `pc` in `finalLabelMap`. -/
  labelMap_total :
    ∀ l, l ∈ cfg.blocks.map Prod.fst → (finalLabelMap l).isSome
  /-- Distinct labels map to distinct `pc`s. -/
  labelMap_inj :
    ∀ l₁ l₂ pc, finalLabelMap l₁ = some pc → finalLabelMap l₂ = some pc → l₁ = l₂
  /-- The `instructions.size = nextLoc` invariant on the final state. -/
  size_eq : ans.instructions.size = ans.nextLoc
  /-- Every instruction's `locationNum = index`. -/
  locationNum_eq_index :
    ∀ (i : Nat) (instr : CProverGOTO.Instruction),
      ans.instructions[i]? = some instr → instr.locationNum = i
  /-- For each CFG block label, `instrAt` of its `pc` returns a LOCATION
  instruction. -/
  layout_location :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
      ∃ instr, ans.instructions[pc]? = some instr ∧ instr.type = .LOCATION
  /-- The LOCATION instruction at `finalLabelMap l`'s `pc` carries `[l]` in
  its `labels` field. -/
  layout_location_labels :
    ∀ l blk pc,
      (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
      ∃ instr, ans.instructions[pc]? = some instr ∧
        instr.type = .LOCATION ∧ instr.labels = [l]
  /-- For each `condGoto` block, two GOTO instructions appear at the
  end with proper targets. -/
  layout_cond_goto :
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        ans.instructions[pc_neg]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        finalLabelMap lf = some pc_lf ∧
        ans.instructions[pc_uncond]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        finalLabelMap lt = some pc_lt
  /-- The condGoto guards have the right shape. -/
  layout_cond_goto_guards :
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true
  /-- For each `finish` block, an END_FUNCTION appears after the body. -/
  layout_finish :
    ∀ l blk pc md, (l, blk) ∈ cfg.blocks →
      finalLabelMap l = some pc →
      blk.transfer = .finish md →
      ∃ pc_end instr_end,
        pc_end = pc + 1 + DetBlockBodyInstrCount blk ∧
        ans.instructions[pc_end]? = some instr_end ∧
        instr_end.type = .END_FUNCTION
  /-- For each block body, the per-Cmd layout holds. -/
  layout_block_body :
    ∀ l blk pc, (l, blk) ∈ cfg.blocks → finalLabelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions } -- temporary program
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner
  /-- The CFG's entry label is in the map. -/
  entry_in_map : ∃ pc, finalLabelMap cfg.entry = some pc

/-- Bridge from `CoreCFGToGotoTransformShadow` to
`WellFormedTranslation`: build the witness over the program whose
instructions equal `ans.instructions`. The bridge is essentially a
field-by-field copy — each field of `WellFormedTranslation` is
provided directly by the corresponding field of
`CoreCFGToGotoTransformShadow`, modulo the
`instrAt`-vs-`instructions[?]` rephrasing. -/
def wellFormedTranslation_of_shadow
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (shadow : CoreCFGToGotoTransformShadow cfg Env functionName
                trans₀ ans δ δ_goto δ_goto_bool) :
    WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool where
  labelMap := shadow.finalLabelMap
  labelMap_total := shadow.labelMap_total
  labelMap_inj := shadow.labelMap_inj
  layout_location := by
    intro l blk pc h_in h_lookup
    obtain ⟨instr, h_at, h_ty⟩ := shadow.layout_location l blk pc h_in h_lookup
    refine ⟨instr, ?_, h_ty⟩
    -- Goal: pgm.instrAt pc = some instr, where pgm.instructions = ans.instructions.
    show ans.instructions[pc]? = some instr
    exact h_at
  layout_location_labels := by
    intro l blk pc h_in h_lookup
    obtain ⟨instr, h_at, h_ty, h_labels⟩ :=
      shadow.layout_location_labels l blk pc h_in h_lookup
    refine ⟨instr, ?_, h_ty, h_labels⟩
    show ans.instructions[pc]? = some instr
    exact h_at
  layout_cond_goto := by
    intro l blk pc cond lt lf md h_in h_lookup h_transfer
    obtain ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, h_at_neg, h_ty_neg, h_target_neg, h_lf_lookup,
            h_at_uncond, h_ty_uncond, h_target_uncond, h_lt_lookup⟩ :=
      shadow.layout_cond_goto l blk pc cond lt lf md h_in h_lookup h_transfer
    refine ⟨pc_neg, pc_uncond, pc_lf, pc_lt, instr_neg, instr_uncond,
            h_pc_neg, h_pc_uncond, ?_, h_ty_neg, h_target_neg, h_lf_lookup,
            ?_, h_ty_uncond, h_target_uncond, h_lt_lookup⟩
    · show ans.instructions[pc_neg]? = some instr_neg
      exact h_at_neg
    · show ans.instructions[pc_uncond]? = some instr_uncond
      exact h_at_uncond
  layout_cond_goto_guards := by
    intro l blk pc cond lt lf md instr_neg instr_uncond h_in h_lookup h_transfer h_neg h_uncond
    -- The hypotheses use Program.instrAt; convert to ans.instructions[?].
    have h_neg' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg := h_neg
    have h_uncond' : ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond := h_uncond
    exact shadow.layout_cond_goto_guards l blk pc cond lt lf md instr_neg instr_uncond
      h_in h_lookup h_transfer h_neg' h_uncond'
  layout_finish := by
    intro l blk pc md h_in h_lookup h_transfer
    obtain ⟨pc_end, instr_end, h_pc_end, h_at_end, h_ty_end⟩ :=
      shadow.layout_finish l blk pc md h_in h_lookup h_transfer
    refine ⟨pc_end, instr_end, h_pc_end, ?_, h_ty_end⟩
    show ans.instructions[pc_end]? = some instr_end
    exact h_at_end
  layout_block_body := shadow.layout_block_body
  entry_in_map := shadow.entry_in_map
  locationNum_eq_index := by
    intro i instr h
    -- Goal: instr.locationNum = i, where h : pgm.instrAt i = some instr.
    -- pgm.instrAt i = ans.instructions[i]? by the program's instructions field.
    have h' : ans.instructions[i]? = some instr := h
    exact shadow.locationNum_eq_index i instr h'

/-! ## Top-level theorem

`coreCFGToGotoTransform_wellFormed_nonempty` proves
`Nonempty (WellFormedTranslation ...)` — there exists a witness for
the well-formedness predicate over the translator's output. The proof
composes:

1. `coreCFGToGotoTransform_size_eq_and_loc_direct` (size_eq + locationNum).
2. `blocksFoldlM_layout_location` and `blocksFoldlM_layout_finish` for
   the LOCATION and END_FUNCTION layouts.
3. `patchGotoTargets_preserves_type` to bridge from
   `st_final.trans.instructions` to `ans.instructions`.
4. External hypotheses for the unproven layout fields
   (`layout_cond_goto`, `layout_cond_goto_guards`, `layout_block_body`,
   `labelMap_inj`, `entry_in_map`).

`Nonempty` form sidesteps the motive-typing issues with
`Classical.choose` on `coreCFGToGotoTransform_decompose`'s ∃-witness:
the goal is now a `Prop` (`Nonempty _`) so `obtain` on the `∃` works
directly. -/

/-- Top-level theorem in `Nonempty` form: `coreCFGToGotoTransform`
produces a `WellFormedTranslation`-witnessed program (under the
hypotheses). -/
theorem coreCFGToGotoTransform_wellFormed_nonempty
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_layout_cond_goto :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
          pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
          pc_uncond = pc_neg + 1 ∧
          ans.instructions[pc_neg]? = some instr_neg ∧
          instr_neg.type = .GOTO ∧
          instr_neg.target = some pc_lf ∧
          hashMapToLabelMap st_final.labelMap lf = some pc_lf ∧
          ans.instructions[pc_uncond]? = some instr_uncond ∧
          instr_uncond.type = .GOTO ∧
          instr_uncond.target = some pc_lt ∧
          hashMapToLabelMap st_final.labelMap lt = some pc_lt)
    (h_layout_cond_goto_guards :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc cond lt lf md instr_neg instr_uncond,
        (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
        blk.transfer = .condGoto cond lt lf md →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
        ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
        ∃ e_goto,
          instr_neg.guard = e_goto.not ∧
          ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
          instr_uncond.guard = CProverGOTO.Expr.true)
    (h_layout_block_body :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l blk pc, (l, blk) ∈ cfg.blocks →
        hashMapToLabelMap st_final.labelMap l = some pc →
      ∀ k inner,
        (h : k < blk.cmds.length) →
        blk.cmds[k]'h = .cmd inner →
        CmdEmittedAt δ δ_goto δ_goto_bool
          { name := "", parameterIdentifiers := #[],
            instructions := ans.instructions }
          (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
          inner)
    (h_labelMap_inj :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∀ l₁ l₂ pc,
        hashMapToLabelMap st_final.labelMap l₁ = some pc →
        hashMapToLabelMap st_final.labelMap l₂ = some pc →
        l₁ = l₂)
    (h_entry_in_map :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀) = Except.ok st_final →
      ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Decompose the translator's output (in Prop, so obtain works).
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- size_eq + locationNum_eq_index from structural soundness.
  obtain ⟨h_size_ans, h_loc_ans⟩ :=
    coreCFGToGotoTransform_size_eq_and_loc_direct Env functionName cfg trans₀
      h_init_size h_init_loc
      (fun l blk h_in c h_c => h_admitted_blocks l blk h_in c h_c)
      h_loopContracts_empty_post ans h_run
  -- Layout lemmas at the post-blocks-fold state.
  have h_layout_loc_st :=
    blocksFoldlM_layout_location functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  have h_layout_loc_labels_st :=
    blocksFoldlM_layout_location_with_labels functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  have h_layout_fin_st :=
    blocksFoldlM_layout_finish functionName cfg.blocks _ st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run h_init_size h_distinct
  -- Patches + patchGotoTargets preserve the array under loop-contracts-empty.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- Helper: at any pc, ans.instructions[pc]? gives some instr with type
  -- preserved from st_final.trans.instructions[pc]?.
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  have h_ans_type_at :
      ∀ (pc : Nat) (instr_st : CProverGOTO.Instruction),
        st_final.trans.instructions[pc]? = some instr_st →
        ∃ instr_ans,
          ans.instructions[pc]? = some instr_ans ∧
          instr_ans.type = instr_st.type := by
    intro pc instr_st h_at_st
    have h_size_ans' : ans.instructions.size = st_final.trans.instructions.size := by
      rw [h_ans_eq']
      exact patchGotoTargets_preserves_size st_final.trans resolved
    have h_pc_lt : pc < ans.instructions.size := by
      have h_st_lt : pc < st_final.trans.instructions.size :=
        Array.getElem?_eq_some_iff.mp h_at_st |>.1
      omega
    have h_at_ans_eq : ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
      rw [h_ans_eq']
    have h_at_ans : ans.instructions[pc]? = some ans.instructions[pc] :=
      Array.getElem?_eq_getElem h_pc_lt
    refine ⟨ans.instructions[pc], h_at_ans, ?_⟩
    -- Use patchGotoTargets_preserves_type. The hypothesis h_at_ans is over
    -- ans.instructions; we rewrite to get over patchGotoTargets.
    have h_at_patched :
        (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc]? = some ans.instructions[pc] := by
      rw [← h_at_ans_eq]; exact h_at_ans
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved pc _ h_at_patched
    rw [h_at_pre] at h_at_st
    injection h_at_st with h_at_st
    rw [h_ty_eq]; rw [← h_at_st]
  -- labelMap_total: every block label is in st_final.labelMap.
  have h_labelMap_total :
      ∀ l, l ∈ cfg.blocks.map Prod.fst →
        (hashMapToLabelMap st_final.labelMap l).isSome := by
    intro l h_in
    rw [List.mem_map] at h_in
    obtain ⟨p, h_in', h_eq⟩ := h_in
    obtain ⟨l', blk⟩ := p
    simp at h_eq
    subst h_eq
    obtain ⟨pc, _, h_lookup, _, _, _⟩ := h_layout_loc_st l' blk h_in'
    show (st_final.labelMap[l']?).isSome
    rw [h_lookup]; rfl
  -- Build the shadow.
  refine ⟨wellFormedTranslation_of_shadow cfg Env functionName trans₀ ans
            δ δ_goto δ_goto_bool ?_⟩
  exact {
    finalLabelMap := hashMapToLabelMap st_final.labelMap
    labelMap_total := h_labelMap_total
    labelMap_inj := h_labelMap_inj st_final h_blocks_run
    size_eq := h_size_ans
    locationNum_eq_index := h_loc_ans
    layout_location := by
      intro l blk pc h_in h_lookup
      obtain ⟨pc', instr, h_lookup', h_at_st, h_ty_st, _⟩ := h_layout_loc_st l blk h_in
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at pc' instr h_at_st
      refine ⟨instr_ans, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_location_labels := by
      intro l blk pc h_in h_lookup
      obtain ⟨pc', instr_st, h_lookup', h_at_st, h_ty_st, h_labels_st, _⟩ :=
        h_layout_loc_labels_st l blk h_in
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      -- Lift the LOCATION fact + labels through the patcher.
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at pc' instr_st h_at_st
      -- Use the labels-preserving lemma.
      have h_at_patched :
          (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc']?
            = some instr_ans := by
        have h_at_ans_eq : ans.instructions =
            (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
          rw [h_ans_eq']
        rw [← h_at_ans_eq]; exact h_at_ans
      obtain ⟨instr_pre_lab, h_pre_lab, h_lab_eq⟩ :=
        patchGotoTargets_preserves_labels st_final.trans resolved pc' _ h_at_patched
      have h_inst_eq : instr_pre_lab = instr_st := by
        rw [h_pre_lab] at h_at_st
        injection h_at_st
      refine ⟨instr_ans, h_pc_eq ▸ h_at_ans, ?_, ?_⟩
      · rw [h_ty_eq]; exact h_ty_st
      · rw [h_lab_eq, h_inst_eq]; exact h_labels_st
    layout_cond_goto := h_layout_cond_goto st_final h_blocks_run
    layout_cond_goto_guards := h_layout_cond_goto_guards st_final h_blocks_run
    layout_finish := by
      intro l blk pc md h_in h_lookup h_transfer
      obtain ⟨pc', instr_end, h_lookup', h_at_st, h_ty_st⟩ :=
        h_layout_fin_st l blk md h_in h_transfer
      have h_pc_eq : pc = pc' := by
        unfold hashMapToLabelMap at h_lookup
        rw [h_lookup'] at h_lookup
        exact (Option.some.inj h_lookup).symm
      obtain ⟨instr_ans, h_at_ans, h_ty_eq⟩ := h_ans_type_at _ instr_end h_at_st
      refine ⟨pc' + 1 + DetBlockBodyInstrCount blk, instr_ans, h_pc_eq ▸ rfl, h_pc_eq ▸ h_at_ans, ?_⟩
      rw [h_ty_eq]; exact h_ty_st
    layout_block_body := h_layout_block_body st_final h_blocks_run
    entry_in_map := h_entry_in_map st_final h_blocks_run
  }

/-! ## Closures for hypothesis-parameter fields of `_wellFormed_nonempty`

Each closure theorem (`entry_in_map_of_translator`,
`labelMap_inj_of_translator`, `layout_block_body_of_translator`) takes
the same inputs as `coreCFGToGotoTransform_wellFormed_nonempty` and
produces the matching hypothesis shape. The
`layout_cond_goto`/`layout_cond_goto_guards` closures are below
(`layout_cond_goto_of_translator`, `layout_cond_goto_guards_of_translator`). -/

/-- Closure for `entry_in_map`. Trivial corollary of
`blocksFoldlM_layout_location` — given `cfg.blocks.head?.map Prod.fst =
some cfg.entry` (the entry-first invariant the translator checks), the
first block's label IS `cfg.entry`, so `(cfg.entry, _) ∈ cfg.blocks`,
and `blocksFoldlM_layout_location` gives the labelMap entry.

The translator's entry-check ensures `cfg.blocks ≠ []` whenever the
entry is to be used. We require `h_entry_first` to be supplied; in the
`coreCFGToGotoTransform_decompose` empty-blocks branch, the labelMap
remains empty and `entry_in_map` is unprovable — but the entry-check
in `coreCFGToGotoTransform` would have to either accept `cfg.blocks = []`
(and then nothing references `cfg.entry`) or reject. The translator's
implementation does both: it accepts `cfg.blocks = []` as a no-op, but
then `h_entry_first` (which the caller supplies) constrains the case. -/
theorem entry_in_map_of_translator
    (cfg : Core.DetCFG)
    (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∃ pc, hashMapToLabelMap st_final.labelMap cfg.entry = some pc := by
  intro st_final h_blocks_run
  -- The `head?` witness gives us a (l, blk) ∈ cfg.blocks with l = cfg.entry.
  cases h_blocks : cfg.blocks with
  | nil =>
    -- head?.map _ = none ≠ some cfg.entry; contradiction.
    rw [h_blocks] at h_entry_first
    simp at h_entry_first
  | cons hd rest =>
    obtain ⟨l, blk⟩ := hd
    rw [h_blocks] at h_entry_first
    simp at h_entry_first
    -- h_entry_first : l = cfg.entry. Substitute.
    subst h_entry_first
    -- Apply blocksFoldlM_layout_location.
    have h_in : (cfg.entry, blk) ∈ cfg.blocks := by
      rw [h_blocks]; simp
    have h_init_size_st :
        (coreCFGToGotoInitState trans₀).trans.instructions.size =
          (coreCFGToGotoInitState trans₀).trans.nextLoc := by
      simp [coreCFGToGotoInitState]; exact h_init_size
    have h_admitted_st :
        ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
          Core.CmdExt.isAdmittedCmd c = true :=
      fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
    obtain ⟨pc, _, h_lookup, _, _, _⟩ :=
      blocksFoldlM_layout_location functionName cfg.blocks _ st_final
        h_admitted_st h_blocks_run h_init_size_st h_distinct cfg.entry blk h_in
    refine ⟨pc, ?_⟩
    show st_final.labelMap[cfg.entry]? = some pc
    exact h_lookup

/-! ### Helpers for `labelMap_inj_of_translator`

The strategy is a stronger combined invariant `(I)`:
1. Every pc in the labelMap is `< trans.nextLoc`.
2. The labelMap is injective.

Each block step preserves `(I)` because:
- The newly inserted pc equals the pre-step `nextLoc`, which is
  strictly less than the post-step `nextLoc` (by
  `coreCFGToGotoBlockStep_nextLoc_advance_*`). So all post-step pcs
  remain `< new nextLoc`.
- For injectivity: pre-existing pcs were `< pre-step nextLoc`; the new
  pc equals the pre-step `nextLoc`. So no old entry can collide with
  the new entry. Within the old entries, injectivity follows from
  the IH. Within the new entry alone, trivially distinct.

`(I)` holds at the initial state (empty labelMap). Applying via
`blocksFoldlM` yields `(I)` at `st_final`, from which `labelMap_inj`
follows. -/

/-- Combined invariant: labelMap codomain is bounded by `nextLoc`
and the labelMap is injective. -/
@[expose] def labelMapBoundedAndInj
    (m : Std.HashMap String Nat) (nextLoc : Nat) : Prop :=
  (∀ (l : String) (pc : Nat), m[l]? = some pc → pc < nextLoc) ∧
  (∀ (l₁ l₂ : String) (pc : Nat),
    m[l₁]? = some pc → m[l₂]? = some pc → l₁ = l₂)

/-- The empty labelMap satisfies the invariant trivially. -/
theorem labelMapBoundedAndInj_empty (n : Nat) :
    labelMapBoundedAndInj (∅ : Std.HashMap String Nat) n := by
  refine ⟨?_, ?_⟩
  · intro l pc h
    simp [Std.HashMap.getElem?_empty] at h
  · intro l₁ l₂ pc h₁ h₂
    simp [Std.HashMap.getElem?_empty] at h₁

/-- Per-block step preserves `labelMapBoundedAndInj`, because the new
pc equals the old `nextLoc` and the new `nextLoc` strictly advances. -/
theorem coreCFGToGotoBlockStep_preserves_labelMapBoundedAndInj
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_inv : labelMapBoundedAndInj st.labelMap st.trans.nextLoc) :
    labelMapBoundedAndInj st'.labelMap st'.trans.nextLoc := by
  obtain ⟨h_bound, h_inj⟩ := h_inv
  -- The labelMap effect: insert lblBlk.1 ↦ st.trans.nextLoc.
  have h_lbl : st'.labelMap = st.labelMap.insert lblBlk.1 st.trans.nextLoc :=
    coreCFGToGotoBlockStep_labelMap fname lblBlk st st' h_run
  -- The nextLoc advance: depending on transfer.
  have h_advance : st.trans.nextLoc < st'.trans.nextLoc := by
    cases h_t : lblBlk.2.transfer with
    | condGoto cond lt lf md =>
      have := coreCFGToGotoBlockStep_nextLoc_advance_condGoto fname lblBlk st st'
        cond lt lf md h_t h_admitted h_run
      rw [this]; omega
    | finish md =>
      have := coreCFGToGotoBlockStep_nextLoc_advance_finish fname lblBlk st st'
        md h_t h_admitted h_run
      rw [this]; omega
  refine ⟨?_, ?_⟩
  · -- bound preservation.
    intro l pc h_at
    rw [h_lbl] at h_at
    rw [Std.HashMap.getElem?_insert] at h_at
    by_cases h_eq : lblBlk.1 = l
    · simp [h_eq] at h_at
      omega
    · have : ¬ lblBlk.1 = l := h_eq
      simp [this] at h_at
      have h_pc_lt_old := h_bound l pc h_at
      omega
  · -- injectivity preservation.
    intro l₁ l₂ pc h₁ h₂
    rw [h_lbl] at h₁ h₂
    rw [Std.HashMap.getElem?_insert] at h₁ h₂
    by_cases h_eq₁ : lblBlk.1 = l₁
    · by_cases h_eq₂ : lblBlk.1 = l₂
      · rw [← h_eq₁, ← h_eq₂]
      · -- l₁ = lblBlk.1, l₂ ≠ lblBlk.1.
        simp [h_eq₁] at h₁
        have h_neq₂ : ¬ lblBlk.1 = l₂ := h_eq₂
        simp [h_neq₂] at h₂
        -- h₁: pc = st.trans.nextLoc. h₂: st.labelMap[l₂]? = some pc, with pc < st.trans.nextLoc.
        have h_pc_lt := h_bound l₂ pc h₂
        subst h₁
        omega
    · by_cases h_eq₂ : lblBlk.1 = l₂
      · -- Symmetric.
        have h_neq₁ : ¬ lblBlk.1 = l₁ := h_eq₁
        simp [h_neq₁] at h₁
        simp [h_eq₂] at h₂
        have h_pc_lt := h_bound l₁ pc h₁
        subst h₂
        omega
      · -- Neither = lblBlk.1; both come from old map.
        have h_neq₁ : ¬ lblBlk.1 = l₁ := h_eq₁
        have h_neq₂ : ¬ lblBlk.1 = l₂ := h_eq₂
        simp [h_neq₁] at h₁
        simp [h_neq₂] at h₂
        exact h_inj l₁ l₂ pc h₁ h₂

/-- The blocks-fold preserves `labelMapBoundedAndInj`. -/
theorem blocksFoldlM_preserves_labelMapBoundedAndInj
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_inv : labelMapBoundedAndInj st.labelMap st.trans.nextLoc) :
    labelMapBoundedAndInj st'.labelMap st'.trans.nextLoc := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_inv
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_inv₁ : labelMapBoundedAndInj st₁.labelMap st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_labelMapBoundedAndInj fname hd st st₁
          h_admitted_head h_step h_inv
      exact ih st₁ h_admitted_rest h_run h_inv₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Closure for `labelMap_inj`. Distinct CFG block labels map to
distinct pcs in the post-blocks-fold state, by way of the invariant
`labelMapBoundedAndInj`. -/
theorem labelMap_inj_of_translator
    (cfg : Core.DetCFG)
    (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l₁ l₂ pc,
      hashMapToLabelMap st_final.labelMap l₁ = some pc →
      hashMapToLabelMap st_final.labelMap l₂ = some pc →
      l₁ = l₂ := by
  intro st_final h_blocks_run l₁ l₂ pc h₁ h₂
  -- Apply the foldlM lift with the empty initial labelMap invariant.
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
  have h_inv₀ :
      labelMapBoundedAndInj (coreCFGToGotoInitState trans₀).labelMap
        (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]
    exact labelMapBoundedAndInj_empty trans₀.nextLoc
  obtain ⟨_, h_inj⟩ :=
    blocksFoldlM_preserves_labelMapBoundedAndInj functionName cfg.blocks
      _ st_final h_admitted_st h_blocks_run h_inv₀
  -- Convert hashMapToLabelMap form to st_final.labelMap[?]? form.
  exact h_inj l₁ l₂ pc h₁ h₂

/-! ### Helpers for `layout_block_body_of_translator`

The closure proceeds in three layers:

1. **Equivalence**: `cmdsFoldlM_eq_innerCmdLoop_on_admitted` — on
   admitted commands, `cmdsFoldlM coreCFGToGotoCmdStep trans = ok ans`
   iff `innerCmdLoop trans.T fname cmds trans = ok ans`. This lets us
   reuse `innerCmdLoop_layout_block_body` directly.

2. **Per-block extraction**: `coreCFGToGotoBlockStep_layout_block_body`
   — for a successful per-block step, the body cmds emit at
   `pre_step_nextLoc + 1 + cmdsPrefixInstrCount blk.cmds k` in the
   post-step `st'.trans`.

3. **Outer-fold lift**: `blocksFoldlM_layout_block_body` — for each
   `(l, blk) ∈ cfg.blocks`, the layout extends to `st_final.trans`.

4. **Patcher bridge**: combine with `patchGotoTargets_preserves_*` to
   move from `st_final.trans.instructions` to `ans.instructions`. -/

/-- `cmdsFoldlM` and `innerCmdLoop` produce the same `ans` on the
admitted-commands fragment. The first iteration's `T` argument to
`innerCmdLoop` is `trans.T`; subsequent iterations thread `trans'.T`
matching `coreCFGToGotoCmdStep`'s `trans.T` lookup. -/
theorem cmdsFoldlM_eq_innerCmdLoop_on_admitted
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_admitted : ∀ c ∈ cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans) :
    innerCmdLoop trans.T fname cmds trans = Except.ok ans := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run
    rw [innerCmdLoop_nil]
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_cmd := h_admitted cmd (by simp)
      have h_admitted_rest : ∀ c ∈ rest, Core.CmdExt.isAdmittedCmd c = true :=
        fun c hc => h_admitted c (by simp [hc])
      cases cmd with
      | cmd c =>
        rw [coreCFGToGotoCmdStep_cmd] at h_step
        unfold innerCmdLoop
        simp only [h_step, Except.mapError, Bind.bind, Except.bind]
        exact ih trans' h_admitted_rest h_run
      | call _ _ _ =>
        simp [Core.CmdExt.isAdmittedCmd] at h_admitted_cmd
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Per-block step layout-extraction. For a block step that succeeds,
each admitted command in `blk.cmds` is emitted at the right offset in
`st'.trans.instructions`. -/
theorem coreCFGToGotoBlockStep_layout_block_body
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < st'.trans.instructions.size),
        pgm.instructions[k]? = some st'.trans.instructions[k]) :
    ∀ (k : Nat) (inner : Imperative.Cmd Core.Expression)
      (h : k < lblBlk.2.cmds.length),
      lblBlk.2.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (st.trans.nextLoc + 1 + cmdsPrefixInstrCount lblBlk.2.cmds k) inner := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Unfold the block step.
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    -- Step 1: extract size-eq for trans₂ via cmdsFoldlM_preserves_size_eq.
    have h_size_after_label :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).instructions.size =
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc :=
      emitLabel_preserves_size_eq label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_size
    -- Step 2: convert cmdsFoldlM to innerCmdLoop on the admitted fragment.
    have h_inner_cmd :
        innerCmdLoop
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans).T
          fname blk.cmds
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        = Except.ok trans₂ :=
      cmdsFoldlM_eq_innerCmdLoop_on_admitted fname blk.cmds _ trans₂ h_admitted h_inner
    -- Step 3: extract h_prefix' for trans₂. We need
    -- ∀ k h, pgm.instructions[k]? = some trans₂.instructions[k].
    -- This requires a chain: trans₂.size ≤ st'.size, then the trans₂-prefix
    -- extends through transfer-emit + outer.
    have h_size_le_st' : trans₂.instructions.size ≤ st'.trans.instructions.size := by
      cases h_t : blk.transfer with
      | condGoto cond lt lf md =>
        rw [h_t] at h_run
        simp only at h_run
        generalize h_cond_eval :
            Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
              = cond_eval at h_run
        match cond_eval, h_cond_eval with
        | .ok cond_expr, _ =>
          simp only at h_run
          injection h_run with h_run
          rw [← h_run]
          simp [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto, Array.size_push]
          omega
        | .error _, _ => simp at h_run
      | finish md =>
        rw [h_t] at h_run
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        simp [Array.size_push]
    have h_trans₂_prefix :
        ∀ (k : Nat) (h : k < trans₂.instructions.size),
          st'.trans.instructions[k]? = some trans₂.instructions[k] := by
      intro k h_k
      -- Use the existing cmdsFoldlM_instructions_prefix? + the
      -- already-proven block-step prefix lemma. The block step's
      -- post-state has instructions extending trans₂'s instructions.
      have h_size_le_eq : trans₂.instructions.size ≤ st'.trans.instructions.size :=
        h_size_le_st'
      have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_size_le_eq
      -- We need the prefix-? on st'.trans. Since the block step only pushes
      -- 1 or 2 transfer instructions on top of trans₂, the prefix relation
      -- holds at all k < trans₂.instructions.size.
      have h_eq : st'.trans.instructions[k]? = trans₂.instructions[k]? := by
        cases h_t : blk.transfer with
        | condGoto cond lt lf md =>
          rw [h_t] at h_run
          simp only at h_run
          generalize h_cond_eval :
              Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
                = cond_eval at h_run
          match cond_eval, h_cond_eval with
          | .ok cond_expr, _ =>
            simp only at h_run
            injection h_run with h_run
            rw [← h_run]
            simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
            -- Goal: ((trans₂.instructions.push i₁).push i₂)[k]? = trans₂.instructions[k]?.
            -- Apply outer push (size grows by 1; k still in range).
            have h_k_post_first :
                k < (trans₂.instructions.push
                  ({ type := .GOTO, guard := cond_expr.not,
                     sourceLoc := Imperative.metadataToSourceLoc md fname trans₂.sourceText,
                     locationNum := trans₂.nextLoc } : CProverGOTO.Instruction)).size := by
              rw [Array.size_push]; exact Nat.lt_succ_of_lt h_k
            rw [Array.getElem?_push_lt h_k_post_first]
            -- Goal: some (trans₂.instructions.push inst1)[k] = trans₂.instructions[k]?
            rw [Array.getElem_push_lt h_k]
            rw [Array.getElem?_eq_getElem h_k]
          | .error _, _ => simp at h_run
        | finish md =>
          rw [h_t] at h_run
          simp only at h_run
          injection h_run with h_run
          rw [← h_run]
          rw [Array.getElem?_push_lt h_k]
          rw [Array.getElem?_eq_getElem h_k]
      rw [h_eq]
      exact Array.getElem?_eq_getElem h_k
    have h_prefix_trans₂ :
        ∀ (k : Nat) (h : k < trans₂.instructions.size),
          pgm.instructions[k]? = some trans₂.instructions[k] := by
      intro k h_k
      have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_size_le_st'
      rw [h_prefix k h_k']
      have h_eq := h_trans₂_prefix k h_k
      rw [Array.getElem?_eq_getElem h_k'] at h_eq
      injection h_eq with h_eq
      rw [h_eq]
    -- Step 4: now apply innerCmdLoop_layout_block_body.
    intro k inner h_lt h_at
    have h_admitted_indexed :
        ∀ (k : Nat) (h : k < blk.cmds.length),
          Core.CmdExt.isAdmittedCmd (blk.cmds[k]'h) = true := by
      intro k h_k
      exact h_admitted blk.cmds[k] (List.getElem_mem _)
    have h_layout :=
      innerCmdLoop_layout_block_body
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).T
        fname blk.cmds
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans)
        trans₂ h_inner_cmd h_size_after_label
        pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_admitted_indexed
        h_prefix_trans₂ k inner h_lt h_at
    -- The offset in h_layout is
    -- (emitLabel ...).nextLoc + cmdsPrefixInstrCount blk.cmds k
    -- = (st.trans.nextLoc + 1) + cmdsPrefixInstrCount blk.cmds k
    -- = st.trans.nextLoc + 1 + cmdsPrefixInstrCount blk.cmds k.
    have h_after_label_nextLoc :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname } st.trans).nextLoc =
        st.trans.nextLoc + 1 := rfl
    rw [h_after_label_nextLoc] at h_layout
    exact h_layout
  | .error _, _ => simp at h_run

/-- The blocks-fold extends `coreCFGToGotoBlockStep_layout_block_body`
to the outer fold. For each `(l, blk) ∈ blocks` such that the foldlM
produces `st_final`, the body of `blk` is emitted at the right
offsets relative to `st_final.labelMap[l]?`. -/
theorem blocksFoldlM_layout_block_body
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks)
    (pgm : Program)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_prefix :
      ∀ (k : Nat) (h : k < st'.trans.instructions.size),
        pgm.instructions[k]? = some st'.trans.instructions[k]) :
    ∀ l blk pc, (l, blk) ∈ blocks →
      st'.labelMap[l]? = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool pgm
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k) inner := by
  induction blocks generalizing st with
  | nil =>
    intro l blk pc h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk pc h_in h_lookup k inner h_lt h_at
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest :=
        BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      -- h_prefix on st'.trans, transferred to st₁.trans:
      have h_prefix₁ :
          ∀ (k : Nat) (h : k < st₁.trans.instructions.size),
            pgm.instructions[k]? = some st₁.trans.instructions[k] := by
        intro k h_k
        have h_k' : k < st'.trans.instructions.size := Nat.lt_of_lt_of_le h_k h_le_st'
        rw [h_prefix k h_k']
        have h_eq :=
          blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run k h_k
        rw [Array.getElem?_eq_getElem h_k'] at h_eq
        rw [Array.getElem?_eq_getElem h_k] at h_eq
        injection h_eq with h_eq
        rw [h_eq]
      -- Either (l, blk) = hd, or (l, blk) ∈ rest.
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · -- (l, blk) = hd. Extract the layout from the head step.
        subst h_eq
        -- The labelMap entry for hd.1 = l in st₁ is st.trans.nextLoc.
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_p_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_p_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl_st'] at h_lookup
        rw [h_lbl₁] at h_lookup
        rw [Std.HashMap.getElem?_insert] at h_lookup
        simp at h_lookup
        -- h_lookup : pc = st.trans.nextLoc.
        subst h_lookup
        -- Apply per-block layout extraction with prefix h_prefix₁.
        exact coreCFGToGotoBlockStep_layout_block_body fname (l, blk) st st₁
          h_admitted_head h_step h_size pgm δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
          h_prefix₁ k inner h_lt h_at
      · -- (l, blk) ∈ rest. Apply IH.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest
          l blk pc h_in_rest h_lookup k inner h_lt h_at
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patcher preserves full instruction except target

The patcher only writes the `target` field. Hence every other field
(`type`, `guard`, `code`, `locationNum`, `sourceLoc`, `labels`) is
preserved at any index.

For `layout_block_body_of_translator`, we need to lift `CmdEmittedAt`
over the body cmds from `st_final.trans` to `ans` (the patched
output). Since `CmdEmittedAt` constructors check only `type`, `guard`,
`code` (not `target`), the lift via this lemma works straight
through. -/

/-- A single patch step preserves the non-target fields. -/
private theorem patch_one_preserves_full_except_target
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.type = instr_pre.type ∧
      instr.guard = instr_pre.guard ∧
      instr.code = instr_pre.code ∧
      instr.locationNum = instr_pre.locationNum := by
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
      refine ⟨a[i], h_at, ?_, ?_, ?_, ?_⟩ <;>
        (have h_getD : a[i]! = a[i] := getElem!_pos a i h_idx
         rw [← h]
         simp [h_getD])
    · rw [Array.getElem?_setIfInBounds_ne (Ne.symm h_eq)] at h
      exact ⟨instr, h, rfl, rfl, rfl, rfl⟩
  · rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)] at h
    exact ⟨instr, h, rfl, rfl, rfl, rfl⟩

/-- `patchGotoTargets` preserves the non-target fields at any
in-bounds index — the patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_full_except_target
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.type = instr_pre.type ∧
      instr.guard = instr_pre.guard ∧
      instr.code = instr_pre.code ∧
      instr.locationNum = instr_pre.locationNum := by
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
          instr.type = instr_pre.type ∧
          instr.guard = instr_pre.guard ∧
          instr.code = instr_pre.code ∧
          instr.locationNum = instr_pre.locationNum := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl, rfl, rfl, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_ty_after, h_g_after, h_c_after, h_l_after⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_ty_pre, h_g_pre, h_c_pre, h_l_pre⟩ :=
        patch_one_preserves_full_except_target a p.1 p.2 i instr_after_first h_after_first
      refine ⟨instr_pre, h_pre, ?_, ?_, ?_, ?_⟩
      · exact h_ty_after.trans h_ty_pre
      · exact h_g_after.trans h_g_pre
      · exact h_c_after.trans h_c_pre
      · exact h_l_after.trans h_l_pre
  exact hgen _ _ _ _ h

/-- Closure for `layout_block_body`. Given the per-block-body layout
on `st_final.trans.instructions` (from `blocksFoldlM_layout_block_body`),
lift to `ans.instructions` via `patchGotoTargets_preserves_full_except_target`.
Only `type`, `guard`, `code` fields matter for `CmdEmittedAt`, all of
which are preserved by the patcher. -/
theorem layout_block_body_of_translator
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e)) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc, (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
    ∀ k inner,
      (h : k < blk.cmds.length) →
      blk.cmds[k]'h = .cmd inner →
      CmdEmittedAt δ δ_goto δ_goto_bool
        { name := "", parameterIdentifiers := #[],
          instructions := ans.instructions }
        (pc + 1 + cmdsPrefixInstrCount blk.cmds k)
        inner := by
  intro st_final h_blocks_run l blk pc h_in h_lookup k inner h_lt h_at
  -- Decompose the translator output to bridge st_final.trans to ans.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- The decomposition gives a (potentially different) st_final'. Show they agree.
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    exact Except.ok.inj h_blocks_run'
  subst h_st_eq
  -- patches preserve trans (loopContracts empty).
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  have h_ans_eq' : ans = Imperative.patchGotoTargets st_final.trans resolved := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Apply the per-block-body extraction on st_final.trans first.
  -- We need a pgm with instructions = st_final.trans.instructions and the trivial prefix.
  let pgm_st : Program :=
    { name := "", parameterIdentifiers := #[],
      instructions := st_final.trans.instructions }
  have h_admitted_st :
      ∀ lblBlk ∈ cfg.blocks, ∀ c ∈ lblBlk.2.cmds,
        Core.CmdExt.isAdmittedCmd c = true :=
    fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb
  have h_init_size_st :
      (coreCFGToGotoInitState trans₀).trans.instructions.size =
        (coreCFGToGotoInitState trans₀).trans.nextLoc := by
    simp [coreCFGToGotoInitState]; exact h_init_size
  have h_lookup_st : st_final.labelMap[l]? = some pc := h_lookup
  have h_prefix_trivial :
      ∀ (k : Nat) (h : k < st_final.trans.instructions.size),
        pgm_st.instructions[k]? = some st_final.trans.instructions[k] := by
    intro k h_k
    show st_final.trans.instructions[k]? = some st_final.trans.instructions[k]
    exact Array.getElem?_eq_getElem h_k
  have h_emit_st :=
    blocksFoldlM_layout_block_body functionName cfg.blocks _ st_final
      h_admitted_st h_blocks_run h_init_size_st h_distinct
      pgm_st δ δ_goto δ_goto_bool h_expr_corr h_tx_eq h_prefix_trivial
      l blk pc h_in h_lookup_st k inner h_lt h_at
  -- Now bridge from pgm_st (over st_final.trans) to the goal (over ans).
  -- The trick: CmdEmittedAt only checks type/guard/code, all preserved by patchGotoTargets.
  -- We do a case analysis on h_emit_st's constructor and rebuild over ans.
  -- The patcher preservation:
  have h_preserves :
      ∀ (idx : Nat) (instr_ans : CProverGOTO.Instruction),
        ans.instructions[idx]? = some instr_ans →
        ∃ instr_st, st_final.trans.instructions[idx]? = some instr_st ∧
          instr_ans.type = instr_st.type ∧
          instr_ans.guard = instr_st.guard ∧
          instr_ans.code = instr_st.code ∧
          instr_ans.locationNum = instr_st.locationNum := by
    intro idx instr_ans h_at_ans
    rw [h_ans_eq'] at h_at_ans
    exact patchGotoTargets_preserves_full_except_target st_final.trans resolved idx instr_ans h_at_ans
  -- Reverse direction: at any in-bounds idx of st_final.trans, ans has SOME instruction
  -- with the same type/code/guard/locationNum.
  have h_size_eq : ans.instructions.size = st_final.trans.instructions.size := by
    rw [h_ans_eq']
    exact patchGotoTargets_preserves_size st_final.trans resolved
  have h_st_to_ans :
      ∀ (idx : Nat) (instr_st : CProverGOTO.Instruction),
        st_final.trans.instructions[idx]? = some instr_st →
        ∃ instr_ans, ans.instructions[idx]? = some instr_ans ∧
          instr_ans.type = instr_st.type ∧
          instr_ans.guard = instr_st.guard ∧
          instr_ans.code = instr_st.code := by
    intro idx instr_st h_at_st
    have h_idx_lt : idx < st_final.trans.instructions.size :=
      (Array.getElem?_eq_some_iff.mp h_at_st).1
    have h_idx_lt_ans : idx < ans.instructions.size := by rw [h_size_eq]; exact h_idx_lt
    have h_at_ans : ans.instructions[idx]? = some ans.instructions[idx] :=
      Array.getElem?_eq_getElem h_idx_lt_ans
    obtain ⟨instr_st', h_at_st', h_ty, h_g, h_c, _⟩ :=
      h_preserves idx ans.instructions[idx] h_at_ans
    rw [h_at_st'] at h_at_st
    injection h_at_st with h_st_eq
    refine ⟨ans.instructions[idx], h_at_ans, ?_, ?_, ?_⟩ <;>
      simp [h_ty, h_g, h_c, h_st_eq]
  -- Now case-split on h_emit_st and rebuild each constructor over ans.
  -- This is mechanical: each constructor's hypotheses need to be rebuilt by replacing
  -- pgm_st-instructions with ans-instructions while preserving type/code/guard.
  -- The constructor's pc arg is unified with the relation's pc, so cases
  -- doesn't bind a fresh name for it.
  cases h_emit_st with
  | init_det v ty e_core md i_decl i_assn h_decl_at h_decl_ty h_assn_at h_assn_ty
              e_goto gty h_decl_code h_assn_code h_translated =>
    obtain ⟨i_decl', h_at_decl', h_ty_decl', _, h_c_decl'⟩ :=
      h_st_to_ans _ i_decl h_decl_at
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    refine CmdEmittedAt.init_det _ v ty e_core md i_decl' i_assn'
      h_at_decl' (h_ty_decl'.trans h_decl_ty)
      h_at_assn' (h_ty_assn'.trans h_assn_ty)
      e_goto gty ?_ ?_ h_translated
    · rw [h_c_decl']; exact h_decl_code
    · rw [h_c_assn']; exact h_assn_code
  | init_nondet v ty md i_decl h_decl_at h_decl_ty gty h_decl_code =>
    obtain ⟨i_decl', h_at_decl', h_ty_decl', _, h_c_decl'⟩ :=
      h_st_to_ans _ i_decl h_decl_at
    refine CmdEmittedAt.init_nondet _ v ty md i_decl' h_at_decl'
      (h_ty_decl'.trans h_decl_ty) gty ?_
    rw [h_c_decl']; exact h_decl_code
  | set_det v e_core md i_assn h_assn_at h_assn_ty e_goto gty h_assn_code h_translated =>
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    refine CmdEmittedAt.set_det _ v e_core md i_assn'
      h_at_assn' (h_ty_assn'.trans h_assn_ty)
      e_goto gty ?_ h_translated
    rw [h_c_assn']; exact h_assn_code
  | set_nondet v md i_assn h_assn_at h_assn_ty gty h_assn_code =>
    obtain ⟨i_assn', h_at_assn', h_ty_assn', _, h_c_assn'⟩ :=
      h_st_to_ans _ i_assn h_assn_at
    obtain ⟨e_nondet, h_assn_code_eq, h_id, h_ty_e⟩ := h_assn_code
    refine CmdEmittedAt.set_nondet _ v md i_assn'
      h_at_assn' (h_ty_assn'.trans h_assn_ty) gty
      ⟨e_nondet, ?_, h_id, h_ty_e⟩
    rw [h_c_assn']; exact h_assn_code_eq
  | assert_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.assert_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | assume_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.assume_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard
  | cover_emit label e_core md i h_at_st h_ty e_goto h_guard h_translated =>
    obtain ⟨i', h_at', h_ty', h_g', _⟩ := h_st_to_ans _ i h_at_st
    refine CmdEmittedAt.cover_emit _ label e_core md i' h_at' (h_ty'.trans h_ty)
      e_goto ?_ h_translated
    rw [h_g']; exact h_guard

/-! ## `layout_cond_goto` + guards closures

This section discharges:
* `layout_cond_goto` — every `.condGoto` block produces two GOTO
  instructions at the right pcs with the right targets *after patching*.
* `layout_cond_goto_guards` — those two GOTO instructions carry the
  expected guards (`e_goto.not` and `Expr.true`).

The crux is a **patcher post-condition** lemma
(`patchGotoTargets_target_at_patched_idx`): under unique-indices
patches, if `(idx, tgt) ∈ patches` and `idx < array.size`, then the
patched array at `idx` has `target = some tgt`.

Combined with a `pendingPatches`-tracking invariant and the fact that
every `.condGoto` per-block step pushes exactly two patches
(`(falseIdx, lf)` and `(trueIdx, lt)`) at strictly increasing indices,
we obtain `layout_cond_goto`. The guards lemma is mostly a
restatement of `coreCFGToGotoBlockStep_condGoto_at_pc` lifted across
the foldlM and through the patcher.
-/

/-! ### Patcher post-condition: `target` at patched indices

For an in-bounds index appearing in the patches list with a unique
first projection, `patchGotoTargets` stores `some tgt` at that index.

We work with two flavours:
* **`patchOne`** lemma: for a single patch `(idx, tgt)`, the result has
  `target = some tgt` at `idx` when `idx < array.size`.
* **Inductive lift** to `patchGotoTargets`, leveraging that any later
  patches don't touch `idx` (under uniqueness).
-/

/-- Single-patch post-condition: setting `target` via `set!` at an in-
bounds index produces `target = some tgt` at that index. -/
private theorem patch_one_target_eq
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    (a.set! idx { a[idx]! with target := some tgt })[idx]?
      = some { a[idx]! with target := some tgt } := by
  rw [Array.set!_eq_setIfInBounds]
  have h_lt : idx < (a.setIfInBounds idx { a[idx]! with target := some tgt }).size := by
    simp [h_idx]
  rw [Array.getElem?_eq_getElem h_lt]
  rw [Array.getElem_setIfInBounds_self]

/-- The target of the result of a single-patch `set!` is `some tgt`. -/
private theorem patch_one_target
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (h_idx : idx < a.size) :
    ∃ instr,
      (a.set! idx { a[idx]! with target := some tgt })[idx]? = some instr ∧
      instr.target = some tgt := by
  refine ⟨{ a[idx]! with target := some tgt }, patch_one_target_eq a idx tgt h_idx, rfl⟩

/-- Single-patch preserves array size. -/
private theorem patch_one_preserves_size
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat) :
    (a.set! idx { a[idx]! with target := some tgt }).size = a.size := by
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- The single-patch fold preserves array size. -/
private theorem patch_foldl_preserves_size
    (a : Array CProverGOTO.Instruction) (ps : List (Nat × Nat)) :
    (List.foldl
      (fun acc (p : Nat × Nat) =>
        acc.set! p.fst { acc[p.fst]! with target := some p.snd })
      a ps).size = a.size := by
  induction ps generalizing a with
  | nil => simp
  | cons p ps ih =>
    simp only [List.foldl]
    rw [ih, patch_one_preserves_size]

/-- Single-patch preserves the value at any index different from the
patched one. -/
private theorem patch_one_other_index
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (h_neq : i ≠ idx) :
    (a.set! idx { a[idx]! with target := some tgt })[i]? = a[i]? := by
  rw [Array.set!_eq_setIfInBounds]
  by_cases h_idx : idx < a.size
  · -- in-bounds: setIfInBounds does the actual write at idx; getElem? at i ≠ idx is the same.
    exact Array.getElem?_setIfInBounds_ne h_neq.symm
  · -- out-of-bounds: setIfInBounds is a no-op.
    rw [Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt h_idx)]

/-- The patcher's foldl preserves `target = some tgt` at `idx`,
provided no later patch in the list has first projection `idx`. -/
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
    have h_rest_neq : ∀ q ∈ rest, q.1 ≠ idx := fun q hq => h_tail_no_idx q (by simp [hq])
    apply ih
    · obtain ⟨instr, h_at, h_tgt⟩ := h_target
      have h_neq : idx ≠ p.1 := Ne.symm h_p_neq
      rw [patch_one_other_index a p.1 p.2 idx h_neq]
      exact ⟨instr, h_at, h_tgt⟩
    · exact h_rest_neq

/-- Patches with the form `(idx, tgt) :: rest`, where `rest` doesn't
contain `idx` as a first projection: after the foldl, the result at
`idx` has `target = some tgt`, provided `idx < array.size`. -/
private theorem patch_foldl_target_head
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (rest : List (Nat × Nat))
    (h_idx : idx < a.size)
    (h_rest_no_idx : ∀ p ∈ rest, p.1 ≠ idx) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ((idx, tgt) :: rest))[idx]? = some instr ∧
      instr.target = some tgt := by
  simp only [List.foldl]
  obtain ⟨instr, h_at, h_tgt⟩ := patch_one_target a idx tgt h_idx
  exact patch_foldl_target_preserved_when_idx_unique_in_tail
    (a.set! idx { a[idx]! with target := some tgt }) idx tgt rest
    ⟨instr, h_at, h_tgt⟩ h_rest_no_idx

/-- General patcher post-condition: if `(idx, tgt)` is in the patches
list with no later element sharing the same first projection, and
`idx < array.size`, then the patched array at `idx` has
`target = some tgt`. -/
private theorem patch_foldl_target_at_idx_when_last
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (ps : List (Nat × Nat))
    (h_in : ∃ pre suf, ps = pre ++ (idx, tgt) :: suf ∧
        (∀ p ∈ suf, p.1 ≠ idx))
    (h_idx : idx < a.size) :
    ∃ instr,
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd })
        a ps)[idx]? = some instr ∧
      instr.target = some tgt := by
  obtain ⟨pre, suf, h_eq, h_suf_no_idx⟩ := h_in
  rw [h_eq]
  rw [List.foldl_append]
  -- After processing pre, we get some array b with b.size = a.size.
  have h_b_size :
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd }) a pre).size = a.size :=
    patch_foldl_preserves_size a pre
  have h_idx_b :
      idx <
      (List.foldl
        (fun acc (p : Nat × Nat) =>
          acc.set! p.fst { acc[p.fst]! with target := some p.snd }) a pre).size := h_b_size ▸ h_idx
  -- Now apply patch_foldl_target_head with (idx, tgt) :: suf.
  exact patch_foldl_target_head _ idx tgt suf h_idx_b h_suf_no_idx

/-- The main patcher post-condition: under unique first-projections in
`patches`, every `(idx, tgt) ∈ patches` with `idx < trans.instructions.size`
gives `(patchGotoTargets trans patches).instructions[idx].target = some tgt`. -/
theorem patchGotoTargets_target_at_patched_idx
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_unique : List.Pairwise (fun a b => a.1 ≠ b.1) patches)
    (idx tgt : Nat)
    (h_in : (idx, tgt) ∈ patches)
    (h_idx : idx < trans.instructions.size) :
    ∃ instr,
      (Imperative.patchGotoTargets trans patches).instructions[idx]? = some instr ∧
      instr.target = some tgt := by
  unfold Imperative.patchGotoTargets
  simp only
  -- Split patches at (idx, tgt) and apply patch_foldl_target_at_idx_when_last.
  obtain ⟨pre, suf, h_eq⟩ := List.append_of_mem h_in
  have h_suf_no_idx : ∀ p ∈ suf, p.1 ≠ idx := by
    intro p hp
    -- (idx, tgt) appears in `pre ++ (idx, tgt) :: suf` BEFORE p ∈ suf.
    -- By Pairwise, (idx, tgt).1 ≠ p.1, i.e., idx ≠ p.1, so p.1 ≠ idx.
    rw [h_eq] at h_unique
    rw [List.pairwise_append] at h_unique
    obtain ⟨_, h_tail, _⟩ := h_unique
    rw [List.pairwise_cons] at h_tail
    obtain ⟨h_head, _⟩ := h_tail
    exact (h_head p hp).symm
  exact patch_foldl_target_at_idx_when_last trans.instructions idx tgt patches
    ⟨pre, suf, h_eq, h_suf_no_idx⟩ h_idx

/-! ### Tracking pendingPatches across the block fold

We track three properties of `pendingPatches` through `coreCFGToGotoBlockStep`:
* `IndicesDistinct`: all indices in `pendingPatches` are distinct.
* `IndicesBounded` (relative to `st`): all indices are
  < `st.trans.instructions.size`.
* For each `.condGoto` block at `pc`, the corresponding patches
  `(pc + 1 + bodyCount, lf)` and `(pc + 1 + bodyCount + 1, lt)` are
  members of `pendingPatches` after processing.
-/

/-- After the per-block step, the `pendingPatches` from input `st` are
preserved (via push for `.condGoto`, identity for `.finish`). -/
theorem coreCFGToGotoBlockStep_pendingPatches_preserves
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (p : Nat × String) (h_in : p ∈ st.pendingPatches) :
    p ∈ st'.pendingPatches := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, _ =>
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        -- Goal: p ∈ ((st.pendingPatches.push (..., lf)).push (..., lt)).
        -- Reduce via Array.mem_push.
        simp only [Array.mem_push]
        left; left; exact h_in
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      exact h_in
  | .error _, _ => simp at h_run

/-- After the foldlM, `pendingPatches` from input state are preserved. -/
theorem blocksFoldlM_pendingPatches_preserves
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (p : Nat × String) (h_in : p ∈ st.pendingPatches) :
    p ∈ st'.pendingPatches := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_in
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_in₁ : p ∈ st₁.pendingPatches :=
        coreCFGToGotoBlockStep_pendingPatches_preserves fname hd st st₁ h_step p h_in
      exact ih st₁ h_run h_in₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patches-fold-correctness lemma

For each `(idx, label) ∈ pendingPatches`, after the patches foldlM
under empty `loopContracts`, the resolved patches list contains
`(idx, targetLoc)` where `targetLoc = labelMap[label]?`. -/

/-- Per-step under empty contracts: `(idx, targetLoc) :: oldResolved`. -/
theorem coreCFGToGotoPatchStep_no_contracts_resolvedPatches
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (targetLoc : Nat)
    (h_lookup : labelMap[idxLabel.2]? = some targetLoc)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    acc'.1 = (idxLabel.1, targetLoc) :: acc.1 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  rw [h_lookup] at h_run
  simp only [Std.HashMap.getElem?_empty] at h_run
  injection h_run with h_run
  rw [← h_run]

/-- Per-step under empty contracts: `acc.1 ⊆ acc'.1`. -/
theorem patchesFoldlM_no_contracts_step_subset
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc') :
    ∀ p ∈ acc.1, p ∈ acc'.1 := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  cases h_lookup : labelMap[label]? with
  | none =>
    rw [h_lookup] at h_run
    simp at h_run
  | some targetLoc =>
    rw [h_lookup] at h_run
    simp only [Std.HashMap.getElem?_empty] at h_run
    injection h_run with h_run
    rw [← h_run]
    intro p h_p
    -- acc'.1 = (idx, targetLoc) :: resolvedPatches; old elements remain.
    simp only [List.mem_cons]
    right; exact h_p

/-- The patches foldlM only prepends to `resolvedPatches`. So input
elements are preserved in the output. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_subset
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc') :
    ∀ p ∈ acc.1, p ∈ acc'.1 := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact fun p h => h
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      intro p h_p
      have h_acc₁ : ∀ p ∈ acc.1, p ∈ acc₁.1 :=
        patchesFoldlM_no_contracts_step_subset labelMap acc acc₁ head h_step
      have h_p_acc₁ : p ∈ acc₁.1 := h_acc₁ p h_p
      exact ih acc₁ h_run p h_p_acc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- After the patches foldlM under empty contracts, every input
patch `(idx, label) ∈ pendingPatches` with a labelMap entry produces
a resolved patch in the output, AND the input resolvedPatches are
preserved. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_mem
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (idx : Nat) (label : String) (targetLoc : Nat)
    (h_in : (idx, label) ∈ patches)
    (h_lookup : labelMap[label]? = some targetLoc) :
    (idx, targetLoc) ∈ acc'.1 := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  have h_in_list : (idx, label) ∈ patchesL := by
    rw [← h_eq]; exact (Array.mem_toList_iff).mpr h_in
  clear h_eq
  induction patchesL generalizing acc with
  | nil => simp at h_in_list
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rw [List.mem_cons] at h_in_list
      rcases h_in_list with h_eq | h_in_rest
      · -- (idx, label) is the head; this step puts (idx, targetLoc) :: acc.1 in acc₁.1.
        subst h_eq
        have h_acc₁ := coreCFGToGotoPatchStep_no_contracts_resolvedPatches
          labelMap acc acc₁ (idx, label) targetLoc h_lookup h_step
        -- Then (idx, targetLoc) ∈ acc'.1, since fold preserves all initial elements.
        have h_preserve : ∀ p ∈ acc₁.1, p ∈ acc'.1 :=
          patchesFoldlM_no_contracts_resolvedPatches_subset labelMap rest acc₁ acc' h_run
        apply h_preserve
        rw [h_acc₁]
        exact List.mem_cons_self
      · -- (idx, label) ∈ rest. Apply IH.
        exact ih acc₁ h_run h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### pendingPatches index distinctness

The `pendingPatches` indices grow strictly across blocks (each block
push at indices ≥ block's start). We track this to instantiate the
patcher's "pairwise-distinct first projections" hypothesis. -/

/-- pendingPatches index bound after block step (condGoto): two new
patches at indices `pc + 1 + bodyCount` and `+1`, both <
`st'.trans.instructions.size`. -/
theorem coreCFGToGotoBlockStep_pendingPatches_indices_bound
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size) :
    ∀ p ∈ st'.pendingPatches, p.1 < st'.trans.instructions.size := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        intro p h_p
        -- p in pushed array of two elements past st.pendingPatches.
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto] at h_p
        simp only [Array.mem_push] at h_p
        -- st'.trans.instructions.size = trans₂.instructions.size + 2 (after two pushes).
        -- Note: push order: first the cond-goto, then the uncond-goto.
        show p.1 < (((Imperative.emitUncondGoto _ ((Imperative.emitCondGoto _ _ trans₂).fst)).fst).instructions).size
        simp only [Imperative.emitUncondGoto, Imperative.emitCondGoto, Imperative.emitGoto, Array.size_push]
        -- After two pushes: size = trans₂.instructions.size + 2.
        rcases h_p with (h_p | h_p) | h_p
        · -- p ∈ st.pendingPatches; old bound + everything.
          have := h_old_bound p h_p
          have h_le : st.trans.instructions.size ≤ trans₂.instructions.size := by
            rw [h_inner_size]; omega
          omega
        · -- p = (trans₂.instructions.size, lf).
          subst h_p; simp; omega
        · -- p = (trans₂.instructions.push.size, lt) = (trans₂.instructions.size + 1, lt).
          subst h_p; simp [Array.size_push]
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      -- pendingPatches preserved; state's instructions.size grew by bodyCount + 1 (END).
      intro p h_p
      have := h_old_bound p h_p
      have h_le : st.trans.instructions.size ≤ st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk + 1 := by
        omega
      -- Need st'.trans.instructions.size ≥ st.trans.instructions.size.
      show p.1 < ({ trans₂ with
        instructions := trans₂.instructions.push _,
        nextLoc := trans₂.nextLoc + 1 } : Imperative.GotoTransform Core.Expression.TyEnv).instructions.size
      simp [Array.size_push, h_inner_size]
      omega
  | .error _, _ => simp at h_run

/-- After the foldlM, all pendingPatches indices are bounded by
`st'.trans.instructions.size`. -/
theorem blocksFoldlM_pendingPatches_indices_bound
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size) :
    ∀ p ∈ st'.pendingPatches, p.1 < st'.trans.instructions.size := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_old_bound
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_bound₁ := coreCFGToGotoBlockStep_pendingPatches_indices_bound fname hd st st₁
        h_admitted_head h_step h_size h_old_bound
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_bound₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- The pendingPatches indices are pairwise distinct: any two distinct
elements have distinct first projections. We thread this through the
fold, given the input is distinct AND all input patches' indices are
strictly less than `st.trans.instructions.size`. -/
theorem coreCFGToGotoBlockStep_pendingPatches_indices_distinct
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size)
    (h_old_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st.pendingPatches.toList) :
    List.Pairwise (fun a b => a.1 ≠ b.1) st'.pendingPatches.toList := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    cases h_t : blk.transfer with
    | condGoto cond lt lf md =>
      rw [h_t] at h_run
      simp only at h_run
      generalize h_cond_eval :
          Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
      match cond_eval, h_cond_eval with
      | .ok cond_expr, _ =>
        simp only at h_run
        injection h_run with h_run
        rw [← h_run]
        -- Goal: pairwise distinct in (st.pendingPatches.push (X, lf)).push (Y, lt).toList
        -- where X = trans₂.instructions.size, Y = trans₂.instructions.size + 1.
        simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
        simp only [Array.toList_push]
        -- toList is st.pendingPatches.toList ++ [(X, lf)] ++ [(Y, lt)]
        -- = st.pendingPatches.toList ++ [(X, lf), (Y, lt)]
        rw [List.append_assoc]
        rw [List.pairwise_append]
        refine ⟨h_old_distinct, ?_, ?_⟩
        · -- Pairwise on [X] ++ [Y]: distinct first projections.
          rw [List.pairwise_append]
          refine ⟨List.pairwise_singleton _ _, List.pairwise_singleton _ _, ?_⟩
          intro a ha b hb
          simp only [List.mem_singleton] at ha hb
          subst ha; subst hb
          simp [Array.size_push]
        · -- Old elements vs new: old indices < trans₂.instructions.size.
          intro p h_p_old q h_q_new
          have h_p_lt : p.1 < st.trans.instructions.size := by
            have h_p_arr : p ∈ st.pendingPatches :=
              Array.mem_toList_iff.mp h_p_old
            exact h_old_bound p h_p_arr
          have h_le : st.trans.instructions.size ≤ trans₂.instructions.size := by
            rw [h_inner_size]; omega
          have h_p_lt_trans₂ : p.1 < trans₂.instructions.size := Nat.lt_of_lt_of_le h_p_lt h_le
          -- q is one of the two new entries; its index is ≥ trans₂.instructions.size.
          rw [List.mem_append] at h_q_new
          rcases h_q_new with h_q | h_q
          · simp only [List.mem_singleton] at h_q
            subst h_q; omega
          · simp only [List.mem_singleton] at h_q
            subst h_q; simp [Array.size_push]; omega
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      exact h_old_distinct
  | .error _, _ => simp at h_run

/-- After the foldlM, `pendingPatches` toList is pairwise index-distinct. -/
theorem blocksFoldlM_pendingPatches_indices_distinct
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_old_bound : ∀ p ∈ st.pendingPatches, p.1 < st.trans.instructions.size)
    (h_old_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st.pendingPatches.toList) :
    List.Pairwise (fun a b => a.1 ≠ b.1) st'.pendingPatches.toList := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_old_distinct
  | cons hd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_bound₁ := coreCFGToGotoBlockStep_pendingPatches_indices_bound fname hd st st₁
        h_admitted_head h_step h_size h_old_bound
      have h_distinct₁ := coreCFGToGotoBlockStep_pendingPatches_indices_distinct fname hd st st₁
        h_admitted_head h_step h_size h_old_bound h_old_distinct
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      exact ih st₁ h_admitted_rest h_run h_size₁ h_bound₁ h_distinct₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Patch step success implies labelMap lookup succeeds

If `coreCFGToGotoPatchStep` succeeds, then `labelMap[label]?` is `some _`. -/

/-- Per-step success implies labelMap lookup succeeds. -/
theorem coreCFGToGotoPatchStep_success_lookup
    (labelMap : Std.HashMap String Nat)
    (loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap loopContracts acc idxLabel = Except.ok acc') :
    ∃ targetLoc, labelMap[idxLabel.2]? = some targetLoc := by
  obtain ⟨resolvedPatches, trans⟩ := acc
  obtain ⟨idx, label⟩ := idxLabel
  unfold Strata.coreCFGToGotoPatchStep at h_run
  simp only [Bind.bind, Except.bind] at h_run
  -- Use Option.isSome destructuring.
  by_cases h_some : (labelMap[label]?).isSome
  · obtain ⟨targetLoc, h_lookup⟩ := Option.isSome_iff_exists.mp h_some
    exact ⟨targetLoc, h_lookup⟩
  · -- If not some, the step would have errored.
    have h_none : labelMap[label]? = none := Option.not_isSome_iff_eq_none.mp h_some
    rw [h_none] at h_run
    simp at h_run

/-- The full patches fold success implies every `(idx, label)` in
the input patches has a labelMap lookup. -/
theorem patchesFoldlM_success_all_lookups
    (labelMap : Std.HashMap String Nat)
    (loopContracts : Std.HashMap String (Imperative.MetaData Core.Expression))
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap loopContracts) acc
              = Except.ok acc') :
    ∀ p ∈ patches, ∃ targetLoc, labelMap[p.2]? = some targetLoc := by
  rw [← Array.foldlM_toList] at h_run
  generalize h_eq : patches.toList = patchesL at h_run
  intro p h_p
  have h_p_list : p ∈ patchesL := by
    rw [← h_eq]; exact (Array.mem_toList_iff).mpr h_p
  clear h_eq h_p
  induction patchesL generalizing acc with
  | nil => simp at h_p_list
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap loopContracts acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      rw [List.mem_cons] at h_p_list
      rcases h_p_list with h_eq | h_in_rest
      · subst h_eq
        exact coreCFGToGotoPatchStep_success_lookup labelMap loopContracts acc acc₁ p h_step
      · exact ih acc₁ h_run h_in_rest
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- For a `.condGoto` block, the per-block step pushes the patches
`(st.trans.nextLoc + 1 + bodyCount, lf)` and `(st.trans.nextLoc + 1 + bodyCount + 1, lt)`
onto `pendingPatches`. -/
theorem coreCFGToGotoBlockStep_condGoto_pendingPatches
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (cond : Core.Expression.Expr) (lt lf : String)
    (md : Imperative.MetaData Core.Expression)
    (h_transfer : lblBlk.2.transfer = .condGoto cond lt lf md)
    (h_admitted : ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc) :
    (st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2, lf) ∈ st'.pendingPatches ∧
    (st.trans.nextLoc + 1 + DetBlockBodyInstrCount lblBlk.2 + 1, lt) ∈ st'.pendingPatches := by
  obtain ⟨label, blk⟩ := lblBlk
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_label_size :
        (Imperative.emitLabel label
          { CProverGOTO.SourceLocation.nil with function := fname }
          st.trans).instructions.size = st.trans.instructions.size + 1 := by
      simp [Imperative.emitLabel, Array.size_push]
    have h_inner_size :
        trans₂.instructions.size = st.trans.instructions.size + 1 + DetBlockBodyInstrCount blk := by
      have h_size_after_label :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).instructions.size =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc :=
        emitLabel_preserves_size_eq label _ st.trans h_size
      have h_size_eq₂ : trans₂.instructions.size = trans₂.nextLoc :=
        cmdsFoldlM_preserves_size_eq fname blk.cmds _ trans₂ h_admitted h_inner h_size_after_label
      have h_advance₂ :
          trans₂.nextLoc =
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc +
            blk.cmds.foldl (fun acc c => acc + Core.CmdExt.gotoInstrCount c) 0 :=
        cmdsFoldlM_nextLoc_advance fname blk.cmds _ trans₂ h_admitted h_inner
      have h_after_label_nextLoc :
          (Imperative.emitLabel label
            { CProverGOTO.SourceLocation.nil with function := fname }
            st.trans).nextLoc = st.trans.nextLoc + 1 := rfl
      rw [h_size_eq₂, h_advance₂, h_after_label_nextLoc]
      simp [DetBlockBodyInstrCount, h_size]
    rw [h_transfer] at h_run
    simp only at h_run
    generalize h_cond_eval :
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = cond_eval at h_run
    match cond_eval, h_cond_eval with
    | .ok cond_expr, _ =>
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      -- Now show the two patches are in the resulting pendingPatches array.
      -- pendingPatches = (st.pendingPatches.push (falseIdx, lf)).push (trueIdx, lt)
      -- where falseIdx = trans₂.instructions.size, trueIdx = trans₂.instructions.size + 1.
      -- We need: (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk, lf) and
      --         (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1, lt) are in.
      have h_pc_neg_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk = trans₂.instructions.size := by
        rw [h_inner_size]; omega
      have h_pc_uncond_eq :
          st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 = trans₂.instructions.size + 1 := by
        rw [h_inner_size]; omega
      simp only [Imperative.emitCondGoto, Imperative.emitUncondGoto, Imperative.emitGoto]
      refine ⟨?_, ?_⟩
      · -- (st.trans.nextLoc + 1 + bodyCount, lf) ∈ pushed array
        rw [h_pc_neg_eq]
        simp only [Array.mem_push]
        left; right
        trivial
      · -- (st.trans.nextLoc + 1 + bodyCount + 1, lt) ∈ pushed array
        rw [h_pc_uncond_eq]
        simp only [Array.mem_push, Array.size_push]
        right
        trivial
    | .error _, _ => simp at h_run
  | .error _, _ => simp at h_run

/-! ### Lifted condGoto layout across blocksFoldlM

Lifts `coreCFGToGotoBlockStep_condGoto_at_pc` across the foldlM,
producing `pc` from the labelMap and the prefix-preservation of the
fold. -/

/-- For each `(l, blk) ∈ blocks` with `blk.transfer = .condGoto cond lt lf md`,
the foldlM produces an `st_final` where:
* `st_final.labelMap[l]? = some pc`
* `st_final.trans.instructions[pc + 1 + bodyCount]? = some instr_neg` with
  `.GOTO`, `target = none`, and guard `e_goto.not`.
* `st_final.trans.instructions[pc + 1 + bodyCount + 1]? = some instr_uncond`
  with `.GOTO`, `target = none`, and guard `Expr.true`.
* `(pc + 1 + bodyCount, lf) ∈ st_final.pendingPatches`
* `(pc + 1 + bodyCount + 1, lt) ∈ st_final.pendingPatches`

The `pc` here is the `nextLoc` BEFORE the block step processes the
block. -/
theorem blocksFoldlM_layout_cond_goto_pre_patch
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_admitted :
      ∀ lblBlk ∈ blocks, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_size : st.trans.instructions.size = st.trans.nextLoc)
    (h_distinct : BlockLabelsDistinct blocks) :
    ∀ l blk cond lt lf md, (l, blk) ∈ blocks → blk.transfer = .condGoto cond lt lf md →
      ∃ pc instr_neg instr_uncond e_goto,
        st'.labelMap[l]? = some pc ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = none ∧
        instr_neg.guard = e_goto.not ∧
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond = .ok e_goto ∧
        st'.trans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = none ∧
        instr_uncond.guard = CProverGOTO.Expr.true ∧
        (pc + 1 + DetBlockBodyInstrCount blk, lf) ∈ st'.pendingPatches ∧
        (pc + 1 + DetBlockBodyInstrCount blk + 1, lt) ∈ st'.pendingPatches := by
  induction blocks generalizing st with
  | nil =>
    intro l blk cond lt lf md h_in
    simp at h_in
  | cons hd rest ih =>
    intro l blk cond lt lf md h_in h_transfer
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st hd with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_admitted_head : ∀ c ∈ hd.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        h_admitted hd (by simp)
      have h_size₁ : st₁.trans.instructions.size = st₁.trans.nextLoc :=
        coreCFGToGotoBlockStep_preserves_size_eq fname hd st st₁ h_admitted_head h_step h_size
      have h_admitted_rest :
          ∀ lblBlk ∈ rest, ∀ c ∈ lblBlk.2.cmds, Core.CmdExt.isAdmittedCmd c = true :=
        fun lblBlk hlb => h_admitted lblBlk (by simp [hlb])
      have h_distinct_rest : BlockLabelsDistinct rest := BlockLabelsDistinct_tail hd rest h_distinct
      have h_le_st' : st₁.trans.instructions.size ≤ st'.trans.instructions.size :=
        blocksFoldlM_size_le fname rest st₁ st' h_admitted_rest h_run
      rw [List.mem_cons] at h_in
      rcases h_in with h_eq | h_in_rest
      · subst h_eq
        -- (l, blk) is the head; transfer is .condGoto cond lt lf md.
        obtain ⟨instr_neg, instr_uncond, e_goto, h_at_neg_st₁, h_ty_neg, h_tgt_neg, h_guard_neg,
                h_e_goto, h_at_uncond_st₁, h_ty_uncond, h_tgt_uncond, h_guard_uncond⟩ :=
          coreCFGToGotoBlockStep_condGoto_at_pc fname (l, blk) st st₁ cond lt lf md
            h_transfer h_admitted_head h_step h_size
        have ⟨h_pp_lf_st₁, h_pp_lt_st₁⟩ := coreCFGToGotoBlockStep_condGoto_pendingPatches
          fname (l, blk) st st₁ cond lt lf md h_transfer h_admitted_head h_step h_size
        have h_pc_neg_lt :
            st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_neg_st₁
          exact h_at_neg_st₁.1
        have h_pc_uncond_lt :
            st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1 < st₁.trans.instructions.size := by
          rw [Array.getElem?_eq_some_iff] at h_at_uncond_st₁
          exact h_at_uncond_st₁.1
        have h_at_neg_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk]?
              = some instr_neg := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_neg_lt]
          exact h_at_neg_st₁
        have h_at_uncond_st' :
            st'.trans.instructions[st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1]?
              = some instr_uncond := by
          rw [blocksFoldlM_instructions_prefix? fname rest st₁ st' h_admitted_rest h_run _ h_pc_uncond_lt]
          exact h_at_uncond_st₁
        have h_lbl₁ : st₁.labelMap = st.labelMap.insert l st.trans.nextLoc :=
          coreCFGToGotoBlockStep_labelMap fname (l, blk) st st₁ h_step
        have h_head_not_in_rest : ∀ p ∈ rest, p.1 ≠ l := by
          intro p hp h_eq
          have : l ≠ p.1 := BlockLabelsDistinct_head_neq_tail (l, blk) rest h_distinct p hp
          exact this h_eq.symm
        have h_lbl_st' :
            st'.labelMap[l]? = st₁.labelMap[l]? :=
          blocksFoldlM_labelMap_preserves_external fname rest st₁ st' h_admitted_rest
            h_run l h_head_not_in_rest
        rw [h_lbl₁] at h_lbl_st'
        rw [Std.HashMap.getElem?_insert] at h_lbl_st'
        simp at h_lbl_st'
        -- Pending patches preserve through the rest of the fold.
        have h_pp_lf_st' :
            (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk, lf) ∈ st'.pendingPatches :=
          blocksFoldlM_pendingPatches_preserves fname rest st₁ st' h_run _ h_pp_lf_st₁
        have h_pp_lt_st' :
            (st.trans.nextLoc + 1 + DetBlockBodyInstrCount blk + 1, lt) ∈ st'.pendingPatches :=
          blocksFoldlM_pendingPatches_preserves fname rest st₁ st' h_run _ h_pp_lt_st₁
        refine ⟨st.trans.nextLoc, instr_neg, instr_uncond, e_goto, h_lbl_st', h_at_neg_st',
                h_ty_neg, h_tgt_neg, h_guard_neg, h_e_goto, h_at_uncond_st', h_ty_uncond,
                h_tgt_uncond, h_guard_uncond, h_pp_lf_st', h_pp_lt_st'⟩
      · -- Apply IH on rest.
        exact ih st₁ h_admitted_rest h_run h_size₁ h_distinct_rest l blk cond lt lf md
          h_in_rest h_transfer
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Resolved-patches index distinctness

Under empty contracts, resolvedPatches inherits index-distinctness
from pendingPatches. Specifically: each step prepends `(idx, targetLoc)`
where `idx` is the head's first projection, and pendingPatches' first
projections are pairwise distinct, so resolvedPatches is too. -/

/-- Per-step under empty contracts: if the input pendingPatches list's
first projections are distinct from `acc.1`'s, then so is the output's. -/
theorem patchesFoldlM_no_contracts_resolvedPatches_pairwise_distinct
    (labelMap : Std.HashMap String Nat)
    (patches : List (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_acc_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) acc.1)
    (h_patches_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) patches)
    (h_disjoint : ∀ p ∈ acc.1, ∀ q ∈ patches, p.1 ≠ q.1) :
    List.Pairwise (fun a b => a.1 ≠ b.1) acc'.1 := by
  induction patches generalizing acc with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_acc_distinct
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoPatchStep labelMap ∅ acc head with
    | .ok acc₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      -- acc₁.1 = (head.1, targetLoc) :: acc.1
      obtain ⟨targetLoc, h_lookup⟩ :=
        coreCFGToGotoPatchStep_success_lookup labelMap ∅ acc acc₁ head h_step
      have h_acc₁_eq : acc₁.1 = (head.1, targetLoc) :: acc.1 :=
        coreCFGToGotoPatchStep_no_contracts_resolvedPatches labelMap acc acc₁ head targetLoc
          h_lookup h_step
      -- Build the IH preconditions.
      have h_distinct_rest : List.Pairwise (fun a b => a.1 ≠ b.1) rest := by
        rw [List.pairwise_cons] at h_patches_distinct
        exact h_patches_distinct.2
      have h_head_neq_rest : ∀ q ∈ rest, head.1 ≠ q.1 := by
        rw [List.pairwise_cons] at h_patches_distinct
        exact h_patches_distinct.1
      have h_acc₁_distinct : List.Pairwise (fun a b => a.1 ≠ b.1) acc₁.1 := by
        rw [h_acc₁_eq]
        rw [List.pairwise_cons]
        refine ⟨?_, h_acc_distinct⟩
        intro p hp
        -- p ∈ acc.1; head.1 ≠ p.1 by h_disjoint.
        exact (h_disjoint p hp head (by simp)).symm
      have h_disjoint_acc₁ : ∀ p ∈ acc₁.1, ∀ q ∈ rest, p.1 ≠ q.1 := by
        intro p hp q hq
        rw [h_acc₁_eq] at hp
        rw [List.mem_cons] at hp
        rcases hp with hp | hp
        · subst hp
          exact h_head_neq_rest q hq
        · exact h_disjoint p hp q (by simp [hq])
      exact ih acc₁ h_run h_acc₁_distinct h_distinct_rest h_disjoint_acc₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ### Top-level closures

Two closure theorems:
* `layout_cond_goto_of_translator`
* `layout_cond_goto_guards_of_translator`
-/

/-- The pendingPatches of the initial state (empty) are pairwise
distinct (trivially). -/
theorem coreCFGToGotoInitState_pendingPatches_distinct
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv) :
    List.Pairwise (fun a b => a.1 ≠ b.1)
      (coreCFGToGotoInitState trans₀).pendingPatches.toList := by
  simp [coreCFGToGotoInitState]

/-- The pendingPatches of the initial state are bounded (vacuously). -/
theorem coreCFGToGotoInitState_pendingPatches_bounded
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv) :
    ∀ p ∈ (coreCFGToGotoInitState trans₀).pendingPatches,
      p.1 < (coreCFGToGotoInitState trans₀).trans.instructions.size := by
  intro p hp
  simp [coreCFGToGotoInitState] at hp

/-- Closure for `layout_cond_goto`: under structural hypotheses on the
CFG and translator, every `.condGoto` block at offset `pc` produces two
GOTO instructions (after patching) with the right targets. -/
theorem layout_cond_goto_of_translator
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc cond lt lf md, (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ∃ pc_neg pc_uncond pc_lf pc_lt instr_neg instr_uncond,
        pc_neg = pc + 1 + DetBlockBodyInstrCount blk ∧
        pc_uncond = pc_neg + 1 ∧
        ans.instructions[pc_neg]? = some instr_neg ∧
        instr_neg.type = .GOTO ∧
        instr_neg.target = some pc_lf ∧
        hashMapToLabelMap st_final.labelMap lf = some pc_lf ∧
        ans.instructions[pc_uncond]? = some instr_uncond ∧
        instr_uncond.type = .GOTO ∧
        instr_uncond.target = some pc_lt ∧
        hashMapToLabelMap st_final.labelMap lt = some pc_lt := by
  intro st_final h_blocks_run l blk pc cond lt lf md h_in_blk h_lookup_l h_transfer
  -- Decompose ans = patchGotoTargets trans_post resolved.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- The two block-folds give the same st_final (functions are deterministic).
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    injection h_blocks_run'
  subst h_st_eq
  -- Apply lifted condGoto layout to extract instr_neg, instr_uncond at pre-patch positions.
  obtain ⟨pc', instr_neg_pre, instr_uncond_pre, e_goto,
          h_lookup_pre, h_at_neg_pre, h_ty_neg_pre, h_tgt_neg_pre, h_guard_neg_pre,
          h_e_goto, h_at_uncond_pre, h_ty_uncond_pre, h_tgt_uncond_pre, h_guard_uncond_pre,
          h_pp_lf, h_pp_lt⟩ :=
    blocksFoldlM_layout_cond_goto_pre_patch functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size) h_distinct
      l blk cond lt lf md h_in_blk h_transfer
  -- pc' = pc.
  have h_pc_eq : pc = pc' := by
    unfold hashMapToLabelMap at h_lookup_l
    rw [h_lookup_pre] at h_lookup_l
    exact (Option.some.inj h_lookup_l).symm
  subst h_pc_eq
  -- Use empty contracts to get trans_post = st_final.trans.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- ans.instructions = patchGotoTargets st_final.trans resolved.instructions.
  have h_ans_instr :
      ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Look up labelMap entries for lf and lt: by patchesFoldlM_success_all_lookups.
  obtain ⟨pc_lf, h_lf_lookup⟩ :=
    patchesFoldlM_success_all_lookups st_final.labelMap _ st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
      (pc + 1 + DetBlockBodyInstrCount blk, lf) h_pp_lf
  obtain ⟨pc_lt, h_lt_lookup⟩ :=
    patchesFoldlM_success_all_lookups st_final.labelMap _ st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
      (pc + 1 + DetBlockBodyInstrCount blk + 1, lt) h_pp_lt
  -- Get (pc + ..., pc_lf) ∈ resolved and (pc + ... + 1, pc_lt) ∈ resolved.
  have h_resolved_lf :
      (pc + 1 + DetBlockBodyInstrCount blk, pc_lf) ∈ resolved := by
    have := patchesFoldlM_no_contracts_resolvedPatches_mem st_final.labelMap
      st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
      h_patches_run (pc + 1 + DetBlockBodyInstrCount blk) lf pc_lf h_pp_lf h_lf_lookup
    exact this
  have h_resolved_lt :
      (pc + 1 + DetBlockBodyInstrCount blk + 1, pc_lt) ∈ resolved := by
    have := patchesFoldlM_no_contracts_resolvedPatches_mem st_final.labelMap
      st_final.pendingPatches ([], st_final.trans) (resolved, trans_post)
      h_patches_run (pc + 1 + DetBlockBodyInstrCount blk + 1) lt pc_lt h_pp_lt h_lt_lookup
    exact this
  -- Resolved's first projections are pairwise distinct.
  have h_pp_distinct :
      List.Pairwise (fun a b => a.1 ≠ b.1) st_final.pendingPatches.toList :=
    blocksFoldlM_pendingPatches_indices_distinct functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size)
      (coreCFGToGotoInitState_pendingPatches_bounded trans₀)
      (coreCFGToGotoInitState_pendingPatches_distinct trans₀)
  -- Index-bound for pendingPatches.
  have h_pp_bound :
      ∀ p ∈ st_final.pendingPatches, p.1 < st_final.trans.instructions.size :=
    blocksFoldlM_pendingPatches_indices_bound functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size)
      (coreCFGToGotoInitState_pendingPatches_bounded trans₀)
  -- Resolved indices are subset of pendingPatches indices, so resolved indices are
  -- bounded and pairwise distinct.
  -- We need: pc + 1 + bodyCount < st_final.trans.instructions.size and
  --         pc + 1 + bodyCount + 1 < st_final.trans.instructions.size.
  have h_neg_lt : pc + 1 + DetBlockBodyInstrCount blk < st_final.trans.instructions.size := by
    rw [Array.getElem?_eq_some_iff] at h_at_neg_pre
    exact h_at_neg_pre.1
  have h_uncond_lt : pc + 1 + DetBlockBodyInstrCount blk + 1 < st_final.trans.instructions.size := by
    rw [Array.getElem?_eq_some_iff] at h_at_uncond_pre
    exact h_at_uncond_pre.1
  -- Resolved indices distinct: a sufficient condition is "every (idx, _) ∈ resolved corresponds
  -- to a unique (idx, _) ∈ pendingPatches" — but we only need distinctness here.
  -- Lemma: under empty contracts, resolved.toList.map fst ⊂ pendingPatches.toList.map fst,
  -- AND each resolved element corresponds to a unique pendingPatches element.
  -- We need more: the map preserves distinctness.
  -- Let's use a workaround: prove distinctness directly via the structural argument.
  have h_resolved_distinct_aux :
      List.Pairwise (fun a b => a.1 ≠ b.1) resolved := by
    have h_patches_run_list :
        st_final.pendingPatches.toList.foldlM
          (Strata.coreCFGToGotoPatchStep st_final.labelMap ∅)
          ([], st_final.trans) = Except.ok (resolved, trans_post) := by
      rw [← Array.foldlM_toList] at h_patches_run
      exact h_patches_run
    apply patchesFoldlM_no_contracts_resolvedPatches_pairwise_distinct
      st_final.labelMap st_final.pendingPatches.toList
      ([], st_final.trans) (resolved, trans_post) h_patches_run_list
    · simp -- acc.1 = [] is trivially Pairwise.
    · exact h_pp_distinct
    · simp -- acc.1 = [] disjoint from anything.
  -- Apply patcher post-condition.
  have h_at_neg_ans :
      ∃ instr, ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr ∧
        instr.target = some pc_lf := by
    rw [h_ans_instr]
    exact patchGotoTargets_target_at_patched_idx st_final.trans resolved
      h_resolved_distinct_aux _ pc_lf h_resolved_lf h_neg_lt
  have h_at_uncond_ans :
      ∃ instr, ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr ∧
        instr.target = some pc_lt := by
    rw [h_ans_instr]
    exact patchGotoTargets_target_at_patched_idx st_final.trans resolved
      h_resolved_distinct_aux _ pc_lt h_resolved_lt h_uncond_lt
  obtain ⟨instr_neg, h_at_neg, h_tgt_neg⟩ := h_at_neg_ans
  obtain ⟨instr_uncond, h_at_uncond, h_tgt_uncond⟩ := h_at_uncond_ans
  -- The .GOTO type is preserved by the patcher.
  have h_ty_neg : instr_neg.type = .GOTO := by
    have h_at_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg := by
      rw [← h_ans_instr]; exact h_at_neg
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved _ _ h_at_post
    rw [h_at_pre] at h_at_neg_pre
    injection h_at_neg_pre with h_eq
    rw [h_ty_eq, h_eq]; exact h_ty_neg_pre
  have h_ty_uncond : instr_uncond.type = .GOTO := by
    have h_at_post : (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond := by
      rw [← h_ans_instr]; exact h_at_uncond
    obtain ⟨instr_pre, h_at_pre, h_ty_eq⟩ :=
      patchGotoTargets_preserves_type st_final.trans resolved _ _ h_at_post
    rw [h_at_pre] at h_at_uncond_pre
    injection h_at_uncond_pre with h_eq
    rw [h_ty_eq, h_eq]; exact h_ty_uncond_pre
  -- Convert HashMap lookups to hashMapToLabelMap.
  have h_lf_lookup' : hashMapToLabelMap st_final.labelMap lf = some pc_lf := h_lf_lookup
  have h_lt_lookup' : hashMapToLabelMap st_final.labelMap lt = some pc_lt := h_lt_lookup
  -- Combine.
  exact ⟨pc + 1 + DetBlockBodyInstrCount blk, pc + 1 + DetBlockBodyInstrCount blk + 1,
         pc_lf, pc_lt, instr_neg, instr_uncond, rfl, rfl, h_at_neg, h_ty_neg, h_tgt_neg,
         h_lf_lookup', h_at_uncond, h_ty_uncond, h_tgt_uncond, h_lt_lookup'⟩

/-! ### Patcher preserves the guard field

The patcher only edits the `target` field, so `guard` is preserved.
This is the analogue of `patchGotoTargets_preserves_type`. -/

/-- Single-patch preserves the `guard` field at any index. -/
private theorem patch_one_preserves_guard
    (a : Array CProverGOTO.Instruction) (idx tgt : Nat)
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (a.set! idx { a[idx]! with target := some tgt })[i]? = some instr) :
    ∃ instr_pre,
      a[i]? = some instr_pre ∧
      instr.guard = instr_pre.guard := by
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

/-- `patchGotoTargets` preserves the guard field at any index — the
patcher only writes the `target` field. -/
theorem patchGotoTargets_preserves_guard
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (i : Nat) (instr : CProverGOTO.Instruction)
    (h : (Imperative.patchGotoTargets trans patches).instructions[i]? = some instr) :
    ∃ instr_pre,
      trans.instructions[i]? = some instr_pre ∧
      instr.guard = instr_pre.guard := by
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
        ∃ instr_pre, a[i]? = some instr_pre ∧ instr.guard = instr_pre.guard := by
    intro a ps i instr h
    induction ps generalizing a with
    | nil =>
      simp at h
      exact ⟨instr, h, rfl⟩
    | cons p ps ih =>
      simp only [List.foldl] at h
      obtain ⟨instr_after_first, h_after_first, h_g_after_first⟩ := ih _ h
      obtain ⟨instr_pre, h_pre, h_g_pre⟩ :=
        patch_one_preserves_guard a p.1 p.2 i instr_after_first h_after_first
      exact ⟨instr_pre, h_pre, h_g_after_first.trans h_g_pre⟩
  exact hgen _ _ _ _ h

/-! ### Top-level closure for `layout_cond_goto_guards`

Uses the per-block-step's guard shape (`e_goto.not` and `Expr.true`)
plus the patcher's preservation of guards. -/

/-- Closure for `layout_cond_goto_guards`: every `.condGoto` block
produces two GOTO instructions with the expected guards `e_goto.not`
and `Expr.true` (after patching, which preserves guards). -/
theorem layout_cond_goto_guards_of_translator
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto) :
    ∀ (st_final : Strata.CoreCFGTransLoopState),
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀) = Except.ok st_final →
    ∀ l blk pc cond lt lf md instr_neg instr_uncond,
      (l, blk) ∈ cfg.blocks →
      hashMapToLabelMap st_final.labelMap l = some pc →
      blk.transfer = .condGoto cond lt lf md →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk]? = some instr_neg →
      ans.instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]? = some instr_uncond →
      ∃ e_goto,
        instr_neg.guard = e_goto.not ∧
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto ∧
        instr_uncond.guard = CProverGOTO.Expr.true := by
  intro st_final h_blocks_run l blk pc cond lt lf md instr_neg instr_uncond
        h_in_blk h_lookup_l h_transfer h_at_neg h_at_uncond
  -- Decompose ans.
  obtain ⟨st_final', resolved, trans_post, h_blocks_run', h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  have h_st_eq : st_final = st_final' := by
    rw [h_blocks_run] at h_blocks_run'
    injection h_blocks_run'
  subst h_st_eq
  -- Extract pre-patch guards from the lifted condGoto layout.
  obtain ⟨pc', instr_neg_pre, instr_uncond_pre, e_goto,
          h_lookup_pre, h_at_neg_pre, h_ty_neg_pre, h_tgt_neg_pre, h_guard_neg_pre,
          h_e_goto, h_at_uncond_pre, h_ty_uncond_pre, h_tgt_uncond_pre, h_guard_uncond_pre,
          _, _⟩ :=
    blocksFoldlM_layout_cond_goto_pre_patch functionName cfg.blocks
      (coreCFGToGotoInitState trans₀) st_final
      (fun lblBlk h_lb => h_admitted_blocks lblBlk.1 lblBlk.2 h_lb)
      h_blocks_run (by simp [coreCFGToGotoInitState]; exact h_init_size) h_distinct
      l blk cond lt lf md h_in_blk h_transfer
  have h_pc_eq : pc = pc' := by
    unfold hashMapToLabelMap at h_lookup_l
    rw [h_lookup_pre] at h_lookup_l
    exact (Option.some.inj h_lookup_l).symm
  subst h_pc_eq
  -- Use empty contracts.
  have h_lc_empty := h_loopContracts_empty_post st_final h_blocks_run
  rw [h_lc_empty] at h_patches_run
  have h_trans_post_eq : trans_post = st_final.trans :=
    patchesFoldlM_no_contracts_trans_eq st_final.labelMap st_final.pendingPatches
      ([], st_final.trans) (resolved, trans_post) h_patches_run
  -- ans.instructions = patchGotoTargets st_final.trans resolved.instructions.
  have h_ans_instr :
      ans.instructions = (Imperative.patchGotoTargets st_final.trans resolved).instructions := by
    rw [h_ans_eq, h_trans_post_eq]
  -- Apply patchGotoTargets_preserves_guard.
  have h_at_neg_post :
      (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk]?
        = some instr_neg := by
    rw [← h_ans_instr]; exact h_at_neg
  have h_at_uncond_post :
      (Imperative.patchGotoTargets st_final.trans resolved).instructions[pc + 1 + DetBlockBodyInstrCount blk + 1]?
        = some instr_uncond := by
    rw [← h_ans_instr]; exact h_at_uncond
  obtain ⟨instr_neg_pre', h_at_neg_pre', h_g_neg_eq⟩ :=
    patchGotoTargets_preserves_guard st_final.trans resolved _ _ h_at_neg_post
  obtain ⟨instr_uncond_pre', h_at_uncond_pre', h_g_uncond_eq⟩ :=
    patchGotoTargets_preserves_guard st_final.trans resolved _ _ h_at_uncond_post
  -- Match instr_neg_pre' with instr_neg_pre and similar.
  rw [h_at_neg_pre] at h_at_neg_pre'
  rw [h_at_uncond_pre] at h_at_uncond_pre'
  injection h_at_neg_pre' with h_neg_eq
  injection h_at_uncond_pre' with h_uncond_eq
  -- The guards match. h_neg_eq : instr_neg_pre = instr_neg_pre'.
  -- h_g_neg_eq : instr_neg.guard = instr_neg_pre'.guard.
  -- h_guard_neg_pre : instr_neg_pre.guard = e_goto.not.
  refine ⟨e_goto, ?_, h_expr_translated_witness cond e_goto h_e_goto, ?_⟩
  · rw [h_g_neg_eq, ← h_neg_eq]; exact h_guard_neg_pre
  · rw [h_g_uncond_eq, ← h_uncond_eq]; exact h_guard_uncond_pre

/-! ## Strengthened top-level theorem

`coreCFGToGotoTransform_wellFormed_strengthened` composes the
`layout_*_of_translator` and `{labelMap_inj,entry_in_map}_of_translator`
closures with `coreCFGToGotoTransform_wellFormed_nonempty`, internalising
its five hypothesis parameters covering layout and labelMap fields.

External hypotheses still required from callers:

* `h_entry_first` — `cfg.blocks.head?.map Prod.fst = some cfg.entry`.
  The translator already checks this and rejects on violation.
* `h_expr_corr` — `ExprTranslationPreservesEval` (caller-supplied).
* `h_tx_eq` — technical equality between
  `Imperative.ToGoto.toGotoExpr` and `h_expr_corr.tx`.
* `h_expr_translated_witness` — finer-grained version of
  `h_expr_corr` for the cond-goto layout proof. -/

theorem coreCFGToGotoTransform_wellFormed_strengthened
    (cfg : Core.DetCFG)
    (Env : Core.Expression.TyEnv) (functionName : String)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_size : trans₀.instructions.size = trans₀.nextLoc)
    (h_init_loc :
      ∀ (i : Nat) (instr : CProverGOTO.Instruction),
        trans₀.instructions[i]? = some instr → instr.locationNum = i)
    (h_distinct : BlockLabelsDistinct cfg.blocks)
    (h_admitted_blocks :
      ∀ (l : String) blk, (l, blk) ∈ cfg.blocks →
      ∀ c ∈ blk.cmds, Core.CmdExt.isAdmittedCmd c = true)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (h_entry_first : cfg.blocks.head?.map Prod.fst = some cfg.entry)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
    (δ : Imperative.SemanticEval Core.Expression)
    (δ_goto : SemanticEvalGoto Core.Expression)
    (δ_goto_bool : SemanticEvalGotoBool Core.Expression)
    (h_expr_corr : ExprTranslationPreservesEval δ δ_goto δ_goto_bool)
    (h_tx_eq :
      ∀ e : Core.Expression.Expr,
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e
          = Except.ok (h_expr_corr.tx e))
    (h_expr_translated_witness :
      ∀ (cond : Core.Expression.Expr) (e_goto : CProverGOTO.Expr),
        Lambda.LExpr.toGotoExprCtx (TBase := ⟨Core.ExpressionMetadata, Unit⟩) [] cond
          = .ok e_goto →
        ExprTranslated δ δ_goto δ_goto_bool cond e_goto) :
    Nonempty (WellFormedTranslation cfg
      { name := "", parameterIdentifiers := #[],
        instructions := ans.instructions }
      δ δ_goto δ_goto_bool) := by
  -- Discharge each of `_wellFormed_nonempty`'s five hypothesis
  -- parameters via the closure theorems, then plug into it.
  have h_layout_cond_goto :=
    layout_cond_goto_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
  have h_layout_cond_goto_guards :=
    layout_cond_goto_guards_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_translated_witness
  have h_layout_block_body :=
    layout_block_body_of_translator cfg Env functionName trans₀
      h_init_size h_distinct h_admitted_blocks
      h_loopContracts_empty_post ans h_run
      δ δ_goto δ_goto_bool h_expr_corr h_tx_eq
  have h_labelMap_inj :=
    labelMap_inj_of_translator cfg functionName trans₀
      h_admitted_blocks
  have h_entry_in_map :=
    entry_in_map_of_translator cfg functionName trans₀
      h_init_size h_distinct h_admitted_blocks h_entry_first
  exact coreCFGToGotoTransform_wellFormed_nonempty
    cfg Env functionName trans₀
    h_init_size h_init_loc h_distinct h_admitted_blocks
    h_loopContracts_empty_post ans h_run
    δ δ_goto δ_goto_bool
    h_layout_cond_goto h_layout_cond_goto_guards h_layout_block_body
    h_labelMap_inj h_entry_in_map

end -- public section

end CProverGOTO
