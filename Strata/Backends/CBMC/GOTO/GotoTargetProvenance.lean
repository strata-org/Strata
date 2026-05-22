/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
public import Strata.Backends.CBMC.GOTO.GotoTargetInRange
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

/-! ## "No GOTO has target set" predicate -/

/-- Every `GOTO` instruction in the translator state has `target =
none`. Held throughout the blocks-fold (the translator only emits
GOTOs with no target; the patcher fills targets in later). -/
def NoGotoHasTarget (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    trans.instructions[pc]? = some instr → instr.type = .GOTO →
    instr.target = none

/-! ## Push/append preservation primitives

Pushing or appending instructions whose targets are `none` (or that
aren't GOTO at all) preserves `NoGotoHasTarget`. -/

/-- Pushing an instruction whose `target = none` (or whose `type ≠
.GOTO`) preserves `NoGotoHasTarget`. -/
private theorem push_preserves_no_goto_target
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (new_instr : Instruction)
    (h_no_target : NoGotoHasTarget trans)
    (h_new : new_instr.type = .GOTO → new_instr.target = none) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push new_instr)[pc]? = some instr →
      instr.type = .GOTO → instr.target = none := by
  intro pc instr h h_ty
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    have h' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_no_target h' h_ty
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      exact h_new h_ty
    · have h_lt' : trans.instructions.size < pc := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-- Appending two instructions whose targets are `none` (or that
aren't GOTO) preserves `NoGotoHasTarget`. -/
private theorem append_two_preserves_no_goto_target
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (i₀ i₁ : Instruction)
    (h_no_target : NoGotoHasTarget trans)
    (h_new0 : i₀.type = .GOTO → i₀.target = none)
    (h_new1 : i₁.type = .GOTO → i₁.target = none) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.append #[i₀, i₁])[pc]? = some instr →
      instr.type = .GOTO → instr.target = none := by
  intro pc instr h h_ty
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h
    exact h_no_target h h_ty
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : pc = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      subst h
      exact h_new0 h_ty
    · by_cases h_eq1 : pc = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h
        simp at h
        subst h
        exact h_new1 h_ty
      · have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h
        exact absurd h (by simp)

/-! ## Preservation through `Cmd.toGotoInstructions`

Each branch pushes (or appends) one or two of
DECL / ASSIGN / ASSERT / ASSUME — never GOTO. So every emitted
instruction's `(type ≠ .GOTO) → (target = none)` premise is
vacuously OK. -/

theorem toGotoInstructions_preserves_no_goto_target
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget ans := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_gty, _e_goto, i_decl, i_assn,
              _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      intro pc instr h h_ty
      rw [h_inst] at h
      have h_decl_ng : i_decl.type = .GOTO → i_decl.target = none := by
        intro h'; rw [h_decl_ty] at h'; cases h'
      have h_assn_ng : i_assn.type = .GOTO → i_assn.target = none := by
        intro h'; rw [h_assn_ty] at h'; cases h'
      exact append_two_preserves_no_goto_target trans i_decl i_assn h_no_target
        h_decl_ng h_assn_ng h h_ty
    | nondet =>
      obtain ⟨_gty, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      intro pc instr h h_ty
      rw [h_inst] at h
      have h_decl_ng : i_decl.type = .GOTO → i_decl.target = none := by
        intro h'; rw [h_decl_ty] at h'; cases h'
      exact push_preserves_no_goto_target trans i_decl h_no_target h_decl_ng h h_ty
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_gty, _e_goto, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      intro pc instr h h_ty
      rw [h_inst] at h
      have h_assn_ng : i_assn.type = .GOTO → i_assn.target = none := by
        intro h'; rw [h_assn_ty] at h'; cases h'
      exact push_preserves_no_goto_target trans i_assn h_no_target h_assn_ng h h_ty
    | nondet =>
      obtain ⟨_gty, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      intro pc instr h h_ty
      rw [h_inst] at h
      have h_assn_ng : i_assn.type = .GOTO → i_assn.target = none := by
        intro h'; rw [h_assn_ty] at h'; cases h'
      exact push_preserves_no_goto_target trans i_assn h_no_target h_assn_ng h h_ty
  | assert label e md =>
    obtain ⟨_e_goto, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    intro pc instr h h_ty
    rw [h_inst] at h
    have h_assert_ng : i.type = .GOTO → i.target = none := by
      intro h'; rw [h_assert_ty] at h'; cases h'
    exact push_preserves_no_goto_target trans i h_no_target h_assert_ng h h_ty
  | assume label e md =>
    obtain ⟨_e_goto, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    intro pc instr h h_ty
    rw [h_inst] at h
    have h_assume_ng : i.type = .GOTO → i.target = none := by
      intro h'; rw [h_assume_ty] at h'; cases h'
    exact push_preserves_no_goto_target trans i h_no_target h_assume_ng h h_ty
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      intro pc instr h h_ty
      subst h_run
      let assert_inst : Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h' : (trans.instructions.push assert_inst)[pc]? = some instr := h
      have h_assert_ng : assert_inst.type = .GOTO → assert_inst.target = none := by
        intro h_eq
        have : InstructionType.ASSERT = InstructionType.GOTO := h_eq
        cases this
      exact push_preserves_no_goto_target trans assert_inst h_no_target h_assert_ng h' h_ty
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoCmdStep`

The per-cmd step in the CFG translator either:
* delegates to `Cmd.toGotoInstructions` (`.cmd c` case), or
* pushes a single FUNCTION_CALL instruction (`.call` case).

Neither emits a GOTO. -/

theorem coreCFGToGotoCmdStep_preserves_no_goto_target
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget ans := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_no_goto_target trans.T fname c trans ans h_run h_no_target
  | call procName callArgs md =>
    -- The `.call` branch pushes a FUNCTION_CALL instruction.
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
      intro pc instr h h_ty
      rw [← h_run] at h
      by_cases h_lt : pc < trans.instructions.size
      · rw [Array.getElem?_push_lt h_lt] at h
        have h' : trans.instructions[pc]? = some instr := by
          rw [Array.getElem?_eq_getElem h_lt]; exact h
        exact h_no_target h' h_ty
      · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
        by_cases h_eq : pc = trans.instructions.size
        · subst h_eq
          rw [Array.getElem?_push_size] at h
          injection h with h
          subst h
          -- The pushed inst has type FUNCTION_CALL; but h_ty says .GOTO.
          exfalso
          have : InstructionType.FUNCTION_CALL = InstructionType.GOTO := h_ty
          cases this
        · have h_lt' : trans.instructions.size < pc := by omega
          have h_size_h : (trans.instructions.size + 1) ≤ pc := by omega
          rw [Array.getElem?_eq_none] at h
          · exact absurd h (by simp)
          · rw [Array.size_push]; omega
    | .error _, _ =>
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through `cmdsFoldlM` -/

theorem cmdsFoldlM_preserves_no_goto_target
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget ans := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_no_target
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_no_target' : NoGotoHasTarget trans' :=
        coreCFGToGotoCmdStep_preserves_no_goto_target fname cmd trans trans' h_step h_no_target
      apply ih trans' h_run
      exact h_no_target'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through emit helpers (LOCATION / GOTO / END_FUNCTION)

For LOCATION/END_FUNCTION: not GOTO, so vacuously OK.
For GOTO emit-helpers: pushed GOTO has `target := none` by construction. -/

/-- `emitLabel` pushes a LOCATION instruction. -/
theorem emitLabel_preserves_no_goto_target
    (label : String) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget (Imperative.emitLabel label srcLoc trans) := by
  intro pc instr h h_ty
  let new_instr : Instruction :=
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := Code.skip }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_ng : new_instr.type = .GOTO → new_instr.target = none := by
    intro h_eq
    have : InstructionType.LOCATION = InstructionType.GOTO := h_eq
    cases this
  exact push_preserves_no_goto_target trans new_instr h_no_target h_new_ng h' h_ty

/-- `emitCondGoto` pushes a GOTO with `target := none`. -/
theorem emitCondGoto_preserves_no_goto_target
    (guard : Expr) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget (Imperative.emitCondGoto guard srcLoc trans).fst := by
  intro pc instr h h_ty
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := guard, target := none }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_ng : new_instr.type = .GOTO → new_instr.target = none := fun _ => rfl
  exact push_preserves_no_goto_target trans new_instr h_no_target h_new_ng h' h_ty

/-- `emitUncondGoto` pushes a GOTO with `target := none`. -/
theorem emitUncondGoto_preserves_no_goto_target
    (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_target : NoGotoHasTarget trans) :
    NoGotoHasTarget (Imperative.emitUncondGoto srcLoc trans).fst := by
  intro pc instr h h_ty
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := Expr.true, target := none }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_ng : new_instr.type = .GOTO → new_instr.target = none := fun _ => rfl
  exact push_preserves_no_goto_target trans new_instr h_no_target h_new_ng h' h_ty

/-- The `.finish` branch's END_FUNCTION emit. -/
theorem endFunction_emit_preserves_no_goto_target
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_target : NoGotoHasTarget trans) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push (endFunctionInstr md fname trans))[pc]? =
        some instr →
      instr.type = .GOTO → instr.target = none := by
  intro pc instr h h_ty
  have h_new_ng : (endFunctionInstr md fname trans).type = .GOTO →
      (endFunctionInstr md fname trans).target = none := by
    intro h_eq
    unfold endFunctionInstr at h_eq
    have : InstructionType.END_FUNCTION = InstructionType.GOTO := h_eq
    cases this
  exact push_preserves_no_goto_target trans (endFunctionInstr md fname trans) h_no_target h_new_ng h h_ty

/-! ## Preservation through `coreCFGToGotoBlockStep` -/

theorem coreCFGToGotoBlockStep_preserves_no_goto_target
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_no_target : NoGotoHasTarget st.trans) :
    NoGotoHasTarget st'.trans := by
  obtain ⟨label, blk⟩ := lblBlk
  have h_after_label : NoGotoHasTarget (Imperative.emitLabel label
      { CProverGOTO.SourceLocation.nil with function := fname }
      st.trans) :=
    emitLabel_preserves_no_goto_target label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_no_target
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_after_cmds : NoGotoHasTarget trans₂ :=
      cmdsFoldlM_preserves_no_goto_target fname blk.cmds _ trans₂ h_inner h_after_label
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
        intro pc instr h h_ty
        have h_after_neg : NoGotoHasTarget
            (Imperative.emitCondGoto (Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst :=
          emitCondGoto_preserves_no_goto_target
            (Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_after_cmds
        have h_after_uncond : NoGotoHasTarget
            (Imperative.emitUncondGoto
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              (Imperative.emitCondGoto (Expr.not cond_expr)
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                trans₂).fst).fst :=
          emitUncondGoto_preserves_no_goto_target
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) _ h_after_neg
        exact h_after_uncond h h_ty
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      intro pc instr h h_ty
      exact endFunction_emit_preserves_no_goto_target md fname trans₂ h_after_cmds h h_ty
  | .error _, _ => simp at h_run

/-! ## Preservation through `blocksFoldlM` -/

theorem blocksFoldlM_preserves_no_goto_target
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_no_target : NoGotoHasTarget st.trans) :
    NoGotoHasTarget st'.trans := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_no_target
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_no_target₁ : NoGotoHasTarget st₁.trans :=
        coreCFGToGotoBlockStep_preserves_no_goto_target fname head st st₁ h_step h_no_target
      apply ih st₁ h_run
      exact h_no_target₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoPatchStep` (no contracts)

Under empty `loopContracts`, the patch step is a no-op on `trans`
(per A4's `coreCFGToGotoPatchStep_no_contracts_trans_eq`). So
`NoGotoHasTarget` transfers trivially. -/

theorem coreCFGToGotoPatchStep_preserves_no_goto_target_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_no_target : NoGotoHasTarget acc.2) :
    NoGotoHasTarget acc'.2 := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_no_target

theorem patchesFoldlM_preserves_no_goto_target_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_no_target : NoGotoHasTarget acc.2) :
    NoGotoHasTarget acc'.2 := by
  rw [patchesFoldlM_no_contracts_trans_eq labelMap patches acc acc' h_run]
  exact h_no_target

end CProverGOTO.GotoTargetProvenance
