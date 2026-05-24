/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # `BlocksFoldClosed` — preservation combinator for the blocks-fold portion

This file abstracts the per-translator-step preservation skeleton shared
by `NoDead.lean`, `GotoTargetProvenance.lean` (steps 1–9), and similar
predicates. Predicates of the form
`P : Array CProverGOTO.Instruction → Prop` that are preserved by every
"leaf" emit of the translator (toGotoInstructions, the FUNCTION_CALL
case of cmdStep, emitLabel, emitCondGoto, emitUncondGoto, the
END_FUNCTION emit) are automatically preserved by the full blocks-fold
chain (cmdsFoldlM, blockStep, blocksFoldlM).

The patcher chain (steps 10–12) is handled separately by each consumer
file because the patcher's behaviour on each predicate differs.

## Usage pattern

A consumer file:
1. Defines its predicate `P : Array Instruction → Prop`.
2. Provides a `BlocksFoldClosed P` instance via `ofPushSafe` (the typical
   case: NoDead, NoGotoHasTarget) or by giving the 6 leaf closures
   directly.
3. Reuses the derived theorems (`cmdsFoldlM_preserves`,
   `coreCFGToGotoBlockStep_preserves`, `blocksFoldlM_preserves`) without
   reproving them.
4. Bridges the post-blocks-fold result through its own patcher reasoning
   to the final `ans`.

For predicates that don't fit the unary `P : Array Instruction → Prop`
shape (e.g., binary predicates parameterised by an auxiliary state
that's invariant through the cmds-fold), the standalone helpers
`toGotoInstructions_preserves_of_pushSafe`, `cmdStep_call_preserves_of_pushSafe`,
`coreCFGToGotoCmdStep_preserves_of_pushSafe`, and
`cmdsFoldlM_preserves_of_pushSafe` expose the cmds-fold portion (steps
1–3 of the 9-step matrix) without requiring a typeclass instance.
-/

namespace CProverGOTO

open Imperative
open CProverGOTO

/-! ## The typeclass

The class records the 6 "leaf" closures: each one says that one of the
translator's primitive instruction-pushing operations preserves `P`.
Three derived theorems (`cmdsFoldlM_preserves`,
`coreCFGToGotoBlockStep_preserves`, `blocksFoldlM_preserves`)
automatically lift these to the larger fold pieces. -/

class BlocksFoldClosed (P : Array CProverGOTO.Instruction → Prop) where
  /-- `Cmd.toGotoInstructions` (DECL/ASSIGN/ASSERT/ASSUME pushes)
  preserves `P`. -/
  toGotoInstructions :
    ∀ (T : Core.Expression.TyEnv) (fname : String)
      (c : Imperative.Cmd Core.Expression)
      (trans ans : Imperative.GotoTransform Core.Expression.TyEnv),
      Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans →
      P trans.instructions → P ans.instructions
  /-- The `.call` branch of `coreCFGToGotoCmdStep` (FUNCTION_CALL push)
  preserves `P`. The cmd is constrained to the `.call` constructor; the
  `.cmd c` branch is handled via `toGotoInstructions`. -/
  cmdStep_call :
    ∀ (fname : String) (cmd : Core.Command)
      (trans ans : Imperative.GotoTransform Core.Expression.TyEnv),
      (∃ procName callArgs md, cmd = .call procName callArgs md) →
      Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans →
      P trans.instructions → P ans.instructions
  emitLabel :
    ∀ (label : String) (srcLoc : SourceLocation)
      (trans : Imperative.GotoTransform Core.Expression.TyEnv),
      P trans.instructions →
      P (Imperative.emitLabel label srcLoc trans).instructions
  emitCondGoto :
    ∀ (guard : Expr) (srcLoc : SourceLocation)
      (trans : Imperative.GotoTransform Core.Expression.TyEnv),
      P trans.instructions →
      P (Imperative.emitCondGoto guard srcLoc trans).fst.instructions
  emitUncondGoto :
    ∀ (srcLoc : SourceLocation)
      (trans : Imperative.GotoTransform Core.Expression.TyEnv),
      P trans.instructions →
      P (Imperative.emitUncondGoto srcLoc trans).fst.instructions
  endFunctionEmit :
    ∀ (md : Imperative.MetaData Core.Expression) (fname : String)
      (trans : Imperative.GotoTransform Core.Expression.TyEnv),
      P trans.instructions →
      P (trans.instructions.push (endFunctionInstr md fname trans))

namespace BlocksFoldClosed

variable {P : Array CProverGOTO.Instruction → Prop}

/-! ## Standalone cmds-fold preservation (no typeclass)

These helpers expose the per-cmd / cmds-fold preservation skeleton
without requiring a `BlocksFoldClosed` instance. Useful for binary
predicates `P × Q → Prop` whose `Q`-component is invariant through the
cmds-fold (e.g., `LocationsTrackLabelMap` in `WfLabelMapAgree.lean`,
where the labelMap is unchanged by cmd-emits). -/

/-- Per-`Cmd` preservation: `Imperative.Cmd.toGotoInstructions` preserves
`P` whenever every cmd-emit-pushed instruction is `IsSafe`. -/
theorem toGotoInstructions_preserves_of_pushSafe
    (IsSafe : CProverGOTO.Instruction → Prop)
    (h_push : ∀ a x, P a → IsSafe x → P (a.push x))
    (h_append : ∀ a x y, P a → IsSafe x → IsSafe y → P (a ++ #[x, y]))
    (h_DECL : ∀ instr, instr.type = .DECL → IsSafe instr)
    (h_ASSIGN : ∀ instr, instr.type = .ASSIGN → IsSafe instr)
    (h_ASSERT : ∀ instr, instr.type = .ASSERT → IsSafe instr)
    (h_ASSUME : ∀ instr, instr.type = .ASSUME → IsSafe instr)
    (T : Core.Expression.TyEnv) (fname : String) (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      obtain ⟨_, _, i_decl, i_assn,
              _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      rw [h_inst]
      have h_eq : trans.instructions.append #[i_decl, i_assn]
                = trans.instructions ++ #[i_decl, i_assn] := rfl
      rw [h_eq]
      exact h_append trans.instructions i_decl i_assn h
        (h_DECL i_decl h_decl_ty) (h_ASSIGN i_assn h_assn_ty)
    | nondet =>
      obtain ⟨_, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      rw [h_inst]
      exact h_push trans.instructions i_decl h (h_DECL i_decl h_decl_ty)
  | set v src md =>
    cases src with
    | det e =>
      obtain ⟨_, _, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      rw [h_inst]
      exact h_push trans.instructions i_assn h (h_ASSIGN i_assn h_assn_ty)
    | nondet =>
      obtain ⟨_, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      rw [h_inst]
      exact h_push trans.instructions i_assn h (h_ASSIGN i_assn h_assn_ty)
  | assert label e md =>
    obtain ⟨_, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact h_push trans.instructions i h (h_ASSERT i h_assert_ty)
  | assume label e md =>
    obtain ⟨_, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    rw [h_inst]
    exact h_push trans.instructions i h (h_ASSUME i h_assume_ty)
  | cover label e md =>
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr : Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      subst h_run
      let assert_inst : CProverGOTO.Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      show P (trans.instructions.push assert_inst)
      exact h_push trans.instructions assert_inst h (h_ASSERT assert_inst rfl)
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-- The `.call` case of `coreCFGToGotoCmdStep` pushes a single
FUNCTION_CALL instruction. -/
theorem cmdStep_call_preserves_of_pushSafe
    (IsSafe : CProverGOTO.Instruction → Prop)
    (h_push : ∀ a x, P a → IsSafe x → P (a.push x))
    (h_FUNCTION_CALL : ∀ instr, instr.type = .FUNCTION_CALL → IsSafe instr)
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_call : ∃ procName callArgs md, cmd = .call procName callArgs md)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  obtain ⟨procName, callArgs, md, h_eq⟩ := h_call
  subst h_eq
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
    exact h_push _ _ h (h_FUNCTION_CALL _ rfl)
  | .error _, _ =>
    simp [Bind.bind, Except.bind] at h_run

/-- Per-cmd preservation: dispatches between
`toGotoInstructions_preserves_of_pushSafe` and
`cmdStep_call_preserves_of_pushSafe`. -/
theorem coreCFGToGotoCmdStep_preserves_of_pushSafe
    (IsSafe : CProverGOTO.Instruction → Prop)
    (h_push : ∀ a x, P a → IsSafe x → P (a.push x))
    (h_append : ∀ a x y, P a → IsSafe x → IsSafe y → P (a ++ #[x, y]))
    (h_DECL : ∀ instr, instr.type = .DECL → IsSafe instr)
    (h_ASSIGN : ∀ instr, instr.type = .ASSIGN → IsSafe instr)
    (h_ASSERT : ∀ instr, instr.type = .ASSERT → IsSafe instr)
    (h_ASSUME : ∀ instr, instr.type = .ASSUME → IsSafe instr)
    (h_FUNCTION_CALL : ∀ instr, instr.type = .FUNCTION_CALL → IsSafe instr)
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_of_pushSafe IsSafe h_push h_append
      h_DECL h_ASSIGN h_ASSERT h_ASSUME trans.T fname c trans ans h_run h
  | call procName callArgs md =>
    exact cmdStep_call_preserves_of_pushSafe IsSafe h_push h_FUNCTION_CALL
      fname _ trans ans ⟨procName, callArgs, md, rfl⟩ h_run h

/-- Cmds-fold preservation: applies `coreCFGToGotoCmdStep_preserves_of_pushSafe`
inductively over the cmds list. -/
theorem cmdsFoldlM_preserves_of_pushSafe
    (IsSafe : CProverGOTO.Instruction → Prop)
    (h_push : ∀ a x, P a → IsSafe x → P (a.push x))
    (h_append : ∀ a x y, P a → IsSafe x → IsSafe y → P (a ++ #[x, y]))
    (h_DECL : ∀ instr, instr.type = .DECL → IsSafe instr)
    (h_ASSIGN : ∀ instr, instr.type = .ASSIGN → IsSafe instr)
    (h_ASSERT : ∀ instr, instr.type = .ASSERT → IsSafe instr)
    (h_ASSUME : ∀ instr, instr.type = .ASSUME → IsSafe instr)
    (h_FUNCTION_CALL : ∀ instr, instr.type = .FUNCTION_CALL → IsSafe instr)
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      exact ih trans' h_run
        (coreCFGToGotoCmdStep_preserves_of_pushSafe IsSafe h_push h_append
          h_DECL h_ASSIGN h_ASSERT h_ASSUME h_FUNCTION_CALL
          fname cmd trans trans' h_step h)
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Derived: per-typeclass-instance preservation theorems -/

/-- The per-cmd step preserves `P`: dispatches to either
`toGotoInstructions` (for `.cmd c`) or `cmdStep_call` (for `.call`). -/
theorem coreCFGToGotoCmdStep_preserves
    [inst : BlocksFoldClosed P]
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact inst.toGotoInstructions trans.T fname c trans ans h_run h
  | call procName callArgs md =>
    exact inst.cmdStep_call fname _ trans ans
      ⟨procName, callArgs, md, rfl⟩ h_run h

theorem cmdsFoldlM_preserves
    [BlocksFoldClosed P]
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h : P trans.instructions) :
    P ans.instructions := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      exact ih trans' h_run (coreCFGToGotoCmdStep_preserves fname cmd trans trans' h_step h)
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- A block step is `emitLabel`, then `cmds.foldlM coreCFGToGotoCmdStep`,
then either `(emitCondGoto, emitUncondGoto)` or the END_FUNCTION push.
Each piece preserves `P`. -/
theorem coreCFGToGotoBlockStep_preserves
    [inst : BlocksFoldClosed P]
    (fname : String)
    (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h : P st.trans.instructions) :
    P st'.trans.instructions := by
  obtain ⟨label, blk⟩ := lblBlk
  have h_after_label : P (Imperative.emitLabel label
      { CProverGOTO.SourceLocation.nil with function := fname }
      st.trans).instructions :=
    inst.emitLabel label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_after_cmds : P trans₂.instructions :=
      cmdsFoldlM_preserves fname blk.cmds _ trans₂ h_inner h_after_label
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
        have h_after_neg : P
            (Imperative.emitCondGoto (Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst.instructions :=
          inst.emitCondGoto (Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_after_cmds
        exact inst.emitUncondGoto
          (Imperative.metadataToSourceLoc md fname trans₂.sourceText) _ h_after_neg
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      exact inst.endFunctionEmit md fname trans₂ h_after_cmds
  | .error _, _ => simp at h_run

theorem blocksFoldlM_preserves
    [BlocksFoldClosed P]
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h : P st.trans.instructions) :
    P st'.trans.instructions := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      exact ih st₁ h_run (coreCFGToGotoBlockStep_preserves fname head st st₁ h_step h)
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-- Given `P trans₀.instructions` and a successful blocks-fold, expose
`P st_final.trans.instructions`. The patcher chain is left to the
consumer. -/
theorem of_blocks_run
    [BlocksFoldClosed P]
    (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init : P trans₀.instructions)
    (st_final : Strata.CoreCFGTransLoopState)
    (h_blocks_run :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        (coreCFGToGotoInitState trans₀)
      = Except.ok st_final) :
    P st_final.trans.instructions := by
  have h_init_st : P (coreCFGToGotoInitState trans₀).trans.instructions := by
    show P trans₀.instructions; exact h_init
  exact blocksFoldlM_preserves functionName cfg.blocks _ st_final h_blocks_run h_init_st

/-! ## Helper: `ofPushSafe`

Assembles a `BlocksFoldClosed` instance from per-instruction-type
safety vocabulary, using the standalone helpers above for the cmds-
fold portion. -/
@[reducible] def ofPushSafe
    (IsSafe : CProverGOTO.Instruction → Prop)
    (h_push : ∀ (a : Array CProverGOTO.Instruction) (x : CProverGOTO.Instruction),
      P a → IsSafe x → P (a.push x))
    (h_append : ∀ (a : Array CProverGOTO.Instruction)
      (x y : CProverGOTO.Instruction),
      P a → IsSafe x → IsSafe y → P (a ++ #[x, y]))
    (h_DECL : ∀ instr, instr.type = .DECL → IsSafe instr)
    (h_ASSIGN : ∀ instr, instr.type = .ASSIGN → IsSafe instr)
    (h_ASSERT : ∀ instr, instr.type = .ASSERT → IsSafe instr)
    (h_ASSUME : ∀ instr, instr.type = .ASSUME → IsSafe instr)
    (h_FUNCTION_CALL : ∀ instr, instr.type = .FUNCTION_CALL → IsSafe instr)
    (h_LOCATION : ∀ instr, instr.type = .LOCATION → IsSafe instr)
    (h_GOTO : ∀ instr, instr.type = .GOTO → IsSafe instr)
    (h_END_FUNCTION : ∀ instr, instr.type = .END_FUNCTION → IsSafe instr) :
    BlocksFoldClosed P where
  toGotoInstructions T fname c trans ans h_run h :=
    toGotoInstructions_preserves_of_pushSafe IsSafe h_push h_append
      h_DECL h_ASSIGN h_ASSERT h_ASSUME T fname c trans ans h_run h
  cmdStep_call fname cmd trans ans h_call h_run h :=
    cmdStep_call_preserves_of_pushSafe IsSafe h_push h_FUNCTION_CALL
      fname cmd trans ans h_call h_run h
  emitLabel label srcLoc trans h := by
    let new_instr : CProverGOTO.Instruction :=
      { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        labels := [label], code := Code.skip }
    show P (trans.instructions.push new_instr)
    exact h_push trans.instructions new_instr h (h_LOCATION new_instr rfl)
  emitCondGoto guard srcLoc trans h := by
    let new_instr : CProverGOTO.Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := guard, target := none }
    show P (trans.instructions.push new_instr)
    exact h_push trans.instructions new_instr h (h_GOTO new_instr rfl)
  emitUncondGoto srcLoc trans h := by
    let new_instr : CProverGOTO.Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
        guard := Expr.true, target := none }
    show P (trans.instructions.push new_instr)
    exact h_push trans.instructions new_instr h (h_GOTO new_instr rfl)
  endFunctionEmit md fname trans h := by
    apply h_push _ _ h
    exact h_END_FUNCTION _ (by unfold endFunctionInstr; rfl)

end BlocksFoldClosed

end CProverGOTO
