/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.CoreCFGToGotoTransformWF
import all Strata.DL.Imperative.ToCProverGOTO
import all Strata.Backends.CBMC.GOTO.CoreCFGToGOTOPipeline

public section

/-! # `coreCFGToGotoTransform` never emits DEAD instructions

Round-7b deliverable: discharge R6a's `h_no_dead` side hypothesis. R6a
left this fact as a metaproperty of the translator, orthogonal to
`WellFormedTranslation`'s structural facts. Here we close it directly
by induction on the translator's structure.

## Why this is needed

`TranslatorBridgeHyps.dead_lookup` is universally quantified over PCs,
demanding a per-PC fact about DEAD instructions. The translator never
emits DEAD: every emit-helper produces one of
DECL / ASSIGN / ASSERT / ASSUME / GOTO / LOCATION / END_FUNCTION /
FUNCTION_CALL. R6a uses `h_no_dead` to make `dead_lookup` vacuously
true, but punted on closing it.

## What we prove

```
theorem no_dead_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead :
      ∀ {pc instr},
        trans₀.instructions[pc]? = some instr → instr.type ≠ .DEAD)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∀ {pc instr},
      ({ name := "", parameterIdentifiers := #[],
         instructions := ans.instructions } : Program).instrAt pc
        = some instr →
      instr.type ≠ .DEAD
```

Callers using a typical empty-instructions initial state get
`h_init_no_dead` trivially because `#[][pc]? = none`.

## Proof structure

Inductively, with a "no-DEAD" predicate
`HasNoDead trans := ∀ pc instr, trans.instructions[pc]? = some instr →
  instr.type ≠ .DEAD`:

1. `HasNoDead` is preserved by `Cmd.toGotoInstructions` (every
   `Imperative.Cmd` constructor pushes DECL / ASSIGN / ASSERT / ASSUME).
2. `HasNoDead` is preserved by `coreCFGToGotoCmdStep` (lifts (1); the
   `.call` branch pushes FUNCTION_CALL, not DEAD).
3. `HasNoDead` lifts through `cmds.foldlM coreCFGToGotoCmdStep`.
4. `HasNoDead` is preserved by `coreCFGToGotoBlockStep` (LOCATION
   from `emitLabel`, then cmds, then GOTO/END_FUNCTION transfer).
5. `HasNoDead` lifts through `cfg.blocks.foldlM coreCFGToGotoBlockStep`.
6. `HasNoDead` is preserved by the patch step (only mutates `target`).
7. `HasNoDead` lifts through `pendingPatches.foldlM ...`.
8. `HasNoDead` is preserved by `patchGotoTargets` (Worker A4's
   `patchGotoTargets_preserves_type`).

Step 8 is direct from existing infrastructure; the rest are local
inductions in this file. -/

namespace CProverGOTO.NoDead

open Imperative
open CProverGOTO

/-! ## The `HasNoDead` predicate -/

/-- Every instruction in `trans.instructions` has a non-DEAD type. -/
def HasNoDead (trans : Imperative.GotoTransform Core.Expression.TyEnv) : Prop :=
  ∀ {pc : Nat} {instr : Instruction},
    trans.instructions[pc]? = some instr → instr.type ≠ .DEAD

/-! ## Push/append preservation primitives

These are generic: pushing an instruction whose type is non-DEAD onto
a non-DEAD-prefix preserves the predicate. Appending two non-DEAD
instructions also preserves it. -/

/-- Pushing one non-DEAD instruction preserves `HasNoDead`. -/
private theorem push_preserves_no_dead
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (new_instr : Instruction)
    (h_no_dead : HasNoDead trans)
    (h_new : new_instr.type ≠ .DEAD) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push new_instr)[pc]? = some instr →
      instr.type ≠ .DEAD := by
  intro pc instr h
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_push_lt h_lt] at h
    have h' : trans.instructions[pc]? = some instr := by
      rw [Array.getElem?_eq_getElem h_lt]; exact h
    exact h_no_dead h'
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq : pc = trans.instructions.size
    · subst h_eq
      rw [Array.getElem?_push_size] at h
      injection h with h
      subst h
      exact h_new
    · have h_lt' : trans.instructions.size < pc := by omega
      have h_oor : (trans.instructions.push new_instr).size ≤ pc := by
        rw [Array.size_push]; omega
      rw [Array.getElem?_eq_none h_oor] at h
      exact absurd h (by simp)

/-- Appending two non-DEAD instructions preserves `HasNoDead`. -/
private theorem append_two_preserves_no_dead
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (i₀ i₁ : Instruction)
    (h_no_dead : HasNoDead trans)
    (h_new0 : i₀.type ≠ .DEAD)
    (h_new1 : i₁.type ≠ .DEAD) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.append #[i₀, i₁])[pc]? = some instr →
      instr.type ≠ .DEAD := by
  intro pc instr h
  have h_eq : trans.instructions.append #[i₀, i₁]
      = trans.instructions ++ #[i₀, i₁] := rfl
  rw [h_eq] at h
  by_cases h_lt : pc < trans.instructions.size
  · rw [Array.getElem?_append_left h_lt] at h
    exact h_no_dead h
  · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
    by_cases h_eq0 : pc = trans.instructions.size
    · subst h_eq0
      rw [Array.getElem?_append_right (Nat.le_refl _)] at h
      simp at h
      subst h
      exact h_new0
    · by_cases h_eq1 : pc = trans.instructions.size + 1
      · subst h_eq1
        rw [Array.getElem?_append_right (Nat.le_add_right _ _)] at h
        simp at h
        subst h
        exact h_new1
      · have h_oor : (trans.instructions ++ #[i₀, i₁]).size ≤ pc := by
          rw [Array.size_append]
          simp; omega
        rw [Array.getElem?_eq_none h_oor] at h
        exact absurd h (by simp)

/-! ## Preservation through `Cmd.toGotoInstructions`

Each branch pushes (or appends) one or two of
DECL / ASSIGN / ASSERT / ASSUME — never DEAD. Reuses the per-shape
"_ok" lemmas from `CoreCFGToGotoTransformWF.lean`. -/

theorem toGotoInstructions_preserves_no_dead
    (T : Core.Expression.TyEnv) (fname : String)
    (c : Imperative.Cmd Core.Expression)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Imperative.Cmd.toGotoInstructions T fname c trans = Except.ok ans)
    (h_no_dead : HasNoDead trans) :
    HasNoDead ans := by
  cases c with
  | init v ty initVal md =>
    cases initVal with
    | det e =>
      -- Cmd_toGotoInstructions_init_det_ok layout (12 conjuncts past gty, e_goto, i_decl, i_assn):
      -- toGotoType, toGotoExpr, decl_ty, decl_code, decl_loc,
      -- assn_ty, assn_code, assn_loc, inst, next, T_eq.
      obtain ⟨_gty, _e_goto, i_decl, i_assn,
              _, _, h_decl_ty, _, _, h_assn_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_det_ok T fname v ty e md trans ans h_run
      intro pc instr h
      rw [h_inst] at h
      have h_decl_nd : i_decl.type ≠ .DEAD := by rw [h_decl_ty]; decide
      have h_assn_nd : i_assn.type ≠ .DEAD := by rw [h_assn_ty]; decide
      exact append_two_preserves_no_dead trans i_decl i_assn h_no_dead
        h_decl_nd h_assn_nd h
    | nondet =>
      -- _ok layout (7 conjuncts past gty, i_decl):
      -- toGotoType, decl_ty, decl_code, decl_loc, inst, next, T_eq.
      obtain ⟨_gty, i_decl, _, h_decl_ty, _, _, h_inst, _, _⟩ :=
        Cmd_toGotoInstructions_init_nondet_ok T fname v ty md trans ans h_run
      intro pc instr h
      rw [h_inst] at h
      have h_decl_nd : i_decl.type ≠ .DEAD := by rw [h_decl_ty]; decide
      exact push_preserves_no_dead trans i_decl h_no_dead h_decl_nd h
  | set v src md =>
    cases src with
    | det e =>
      -- _ok layout: lookupType, toGotoExpr, assn_ty, assn_code,
      -- assn_loc, inst, next.
      obtain ⟨_gty, _e_goto, i_assn, _, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_det_ok T fname v e md trans ans h_run
      intro pc instr h
      rw [h_inst] at h
      have h_assn_nd : i_assn.type ≠ .DEAD := by rw [h_assn_ty]; decide
      exact push_preserves_no_dead trans i_assn h_no_dead h_assn_nd h
    | nondet =>
      -- _ok layout: lookupType, assn_ty, assn_code, assn_loc, inst, next.
      obtain ⟨_gty, i_assn, _, h_assn_ty, _, _, h_inst, _⟩ :=
        Cmd_toGotoInstructions_set_nondet_ok T fname v md trans ans h_run
      intro pc instr h
      rw [h_inst] at h
      have h_assn_nd : i_assn.type ≠ .DEAD := by rw [h_assn_ty]; decide
      exact push_preserves_no_dead trans i_assn h_no_dead h_assn_nd h
  | assert label e md =>
    -- _ok layout: toGotoExpr, ty, guard, loc, inst, next.
    obtain ⟨_e_goto, i, _, h_assert_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assert_ok T fname label e md trans ans h_run
    intro pc instr h
    rw [h_inst] at h
    have h_assert_nd : i.type ≠ .DEAD := by rw [h_assert_ty]; decide
    exact push_preserves_no_dead trans i h_no_dead h_assert_nd h
  | assume label e md =>
    -- _ok layout: toGotoExpr, ty, guard, loc, inst, next.
    obtain ⟨_e_goto, i, _, h_assume_ty, _, _, h_inst, _⟩ :=
      Cmd_toGotoInstructions_assume_ok T fname label e md trans ans h_run
    intro pc instr h
    rw [h_inst] at h
    have h_assume_nd : i.type ≠ .DEAD := by rw [h_assume_ty]; decide
    exact push_preserves_no_dead trans i h_no_dead h_assume_nd h
  | cover label e md =>
    -- `cover` is structurally similar to `assert` but emits an ASSERT
    -- with a different comment. We directly unfold (mirroring
    -- `toGotoInstructions_preserves_size_eq` for the `.cover` branch).
    unfold Imperative.Cmd.toGotoInstructions at h_run
    simp only at h_run
    match h_expr :
        Imperative.ToGoto.toGotoExpr (P := Core.Expression) e with
    | .ok e_goto =>
      simp only [h_expr, Bind.bind, Except.bind, pure, Except.pure] at h_run
      injection h_run with h_run
      intro pc instr h
      subst h_run
      -- After subst, `ans.instructions = trans.instructions.push assert_inst`.
      let assert_inst : Instruction :=
        { type := .ASSERT, locationNum := trans.nextLoc,
          sourceLoc := metadataToSourceLoc md fname trans.sourceText
            (comment := md.getPropertySummary.getD s!"cover {label}"),
          guard := e_goto }
      have h' : (trans.instructions.push assert_inst)[pc]? = some instr := h
      have h_assert_nd : assert_inst.type ≠ .DEAD := by
        show InstructionType.ASSERT ≠ InstructionType.DEAD
        decide
      exact push_preserves_no_dead trans assert_inst h_no_dead h_assert_nd h'
    | .error _ =>
      simp [h_expr, Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoCmdStep`

The per-cmd step in the CFG translator either:

* delegates to `Cmd.toGotoInstructions` (`.cmd c` case), or
* pushes a single FUNCTION_CALL instruction (`.call` case).

Both preserve `HasNoDead`. -/

theorem coreCFGToGotoCmdStep_preserves_no_dead
    (fname : String) (cmd : Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoCmdStep fname trans cmd = Except.ok ans)
    (h_no_dead : HasNoDead trans) :
    HasNoDead ans := by
  cases cmd with
  | cmd c =>
    rw [coreCFGToGotoCmdStep_cmd] at h_run
    exact toGotoInstructions_preserves_no_dead trans.T fname c trans ans h_run h_no_dead
  | call procName callArgs md =>
    -- The `.call` branch pushes a FUNCTION_CALL instruction. We
    -- expose the push by unfolding the cmd-step's body.
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
      intro pc instr h
      rw [← h_run] at h
      -- After `rw`, `h` says ans.instructions = trans.instructions.push <inst>
      -- where <inst>.type = .FUNCTION_CALL. Use a generic push-based
      -- argument. We don't need to name the inst — only need
      -- `_.type ≠ .DEAD`, which holds regardless of the body.
      by_cases h_lt : pc < trans.instructions.size
      · rw [Array.getElem?_push_lt h_lt] at h
        have h' : trans.instructions[pc]? = some instr := by
          rw [Array.getElem?_eq_getElem h_lt]; exact h
        exact h_no_dead h'
      · have h_ge : trans.instructions.size ≤ pc := Nat.le_of_not_lt h_lt
        by_cases h_eq : pc = trans.instructions.size
        · subst h_eq
          rw [Array.getElem?_push_size] at h
          injection h with h
          subst h
          show InstructionType.FUNCTION_CALL ≠ InstructionType.DEAD
          decide
        · have h_lt' : trans.instructions.size < pc := by omega
          -- Out of bounds: the push grows by 1.
          have h_size_push : ∀ (a : Array Instruction) (x : Instruction),
              (a.push x).size = a.size + 1 := fun _ _ => Array.size_push ..
          have h_size_h : (trans.instructions.size + 1) ≤ pc := by omega
          -- We rewrite `h` to use `(push x).size = size + 1`, then close.
          rw [Array.getElem?_eq_none] at h
          · exact absurd h (by simp)
          · rw [h_size_push]; omega
    | .error _, _ =>
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through `cmdsFoldlM` -/

theorem cmdsFoldlM_preserves_no_dead
    (fname : String) (cmds : List Core.Command)
    (trans ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : cmds.foldlM (Strata.coreCFGToGotoCmdStep fname) trans = Except.ok ans)
    (h_no_dead : HasNoDead trans) :
    HasNoDead ans := by
  induction cmds generalizing trans with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_no_dead
  | cons cmd rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoCmdStep fname trans cmd with
    | .ok trans' =>
      rw [h_step] at h_run
      simp at h_run
      have h_no_dead' : HasNoDead trans' :=
        coreCFGToGotoCmdStep_preserves_no_dead fname cmd trans trans' h_step h_no_dead
      apply ih trans' h_run
      exact h_no_dead'
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through emit helpers (LOCATION / GOTO / END_FUNCTION) -/

/-- `emitLabel` pushes a LOCATION instruction; `LOCATION ≠ .DEAD`. -/
theorem emitLabel_preserves_no_dead
    (label : String) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_dead : HasNoDead trans) :
    HasNoDead (Imperative.emitLabel label srcLoc trans) := by
  -- `(emitLabel ...).instructions` is definitionally
  -- `trans.instructions.push <LOCATION inst>`.
  intro pc instr h
  let new_instr : Instruction :=
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := Code.skip }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_nd : new_instr.type ≠ .DEAD := by
    show InstructionType.LOCATION ≠ InstructionType.DEAD
    decide
  exact push_preserves_no_dead trans new_instr h_no_dead h_new_nd h'

/-- `emitCondGoto` pushes a GOTO instruction; `GOTO ≠ .DEAD`. -/
theorem emitCondGoto_preserves_no_dead
    (guard : Expr) (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_dead : HasNoDead trans) :
    HasNoDead (Imperative.emitCondGoto guard srcLoc trans).fst := by
  intro pc instr h
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := guard, target := none }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_nd : new_instr.type ≠ .DEAD := by
    show InstructionType.GOTO ≠ InstructionType.DEAD
    decide
  exact push_preserves_no_dead trans new_instr h_no_dead h_new_nd h'

/-- `emitUncondGoto` pushes a GOTO instruction; `GOTO ≠ .DEAD`. -/
theorem emitUncondGoto_preserves_no_dead
    (srcLoc : SourceLocation)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_dead : HasNoDead trans) :
    HasNoDead (Imperative.emitUncondGoto srcLoc trans).fst := by
  intro pc instr h
  let new_instr : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := Expr.true, target := none }
  have h' : (trans.instructions.push new_instr)[pc]? = some instr := h
  have h_new_nd : new_instr.type ≠ .DEAD := by
    show InstructionType.GOTO ≠ InstructionType.DEAD
    decide
  exact push_preserves_no_dead trans new_instr h_no_dead h_new_nd h'

/-- The `.finish` branch's END_FUNCTION emit preserves `HasNoDead`. -/
theorem endFunction_emit_preserves_no_dead
    (md : Imperative.MetaData Core.Expression) (fname : String)
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_no_dead : HasNoDead trans) :
    ∀ {pc : Nat} {instr : Instruction},
      (trans.instructions.push (endFunctionInstr md fname trans))[pc]? =
        some instr →
      instr.type ≠ .DEAD := by
  intro pc instr h
  have h_new_nd : (endFunctionInstr md fname trans).type ≠ .DEAD := by
    unfold endFunctionInstr
    show InstructionType.END_FUNCTION ≠ InstructionType.DEAD
    decide
  exact push_preserves_no_dead trans (endFunctionInstr md fname trans) h_no_dead h_new_nd h

/-! ## Preservation through `coreCFGToGotoBlockStep`

The block step is an `emitLabel`, then an inner cmds-fold, then the
transfer (either `.condGoto` emitting two GOTOs, or `.finish`
emitting an END_FUNCTION). Each piece preserves `HasNoDead`. -/

theorem coreCFGToGotoBlockStep_preserves_no_dead
    (fname : String) (lblBlk : String × Imperative.DetBlock String Core.Command Core.Expression)
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : Strata.coreCFGToGotoBlockStep fname st lblBlk = Except.ok st')
    (h_no_dead : HasNoDead st.trans) :
    HasNoDead st'.trans := by
  obtain ⟨label, blk⟩ := lblBlk
  -- Step 1: emitLabel preserves no-DEAD.
  have h_after_label : HasNoDead (Imperative.emitLabel label
      { CProverGOTO.SourceLocation.nil with function := fname }
      st.trans) :=
    emitLabel_preserves_no_dead label
      { CProverGOTO.SourceLocation.nil with function := fname } st.trans h_no_dead
  unfold Strata.coreCFGToGotoBlockStep at h_run
  simp only [Bind.bind, Except.bind, pure, Except.pure] at h_run
  generalize h_inner :
    blk.cmds.foldlM (Strata.coreCFGToGotoCmdStep fname)
      (Imperative.emitLabel label
        { CProverGOTO.SourceLocation.nil with function := fname } st.trans) = inner at h_run
  match inner, h_inner with
  | .ok trans₂, h_inner =>
    have h_after_cmds : HasNoDead trans₂ :=
      cmdsFoldlM_preserves_no_dead fname blk.cmds _ trans₂ h_inner h_after_label
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
        -- After two emitGoto pushes (emitCondGoto then emitUncondGoto), we
        -- have to show the resulting array is no-DEAD.
        intro pc instr h
        have h_after_neg : HasNoDead
            (Imperative.emitCondGoto (Expr.not cond_expr)
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              trans₂).fst :=
          emitCondGoto_preserves_no_dead
            (Expr.not cond_expr)
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) trans₂ h_after_cmds
        have h_after_uncond : HasNoDead
            (Imperative.emitUncondGoto
              (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
              (Imperative.emitCondGoto (Expr.not cond_expr)
                (Imperative.metadataToSourceLoc md fname trans₂.sourceText)
                trans₂).fst).fst :=
          emitUncondGoto_preserves_no_dead
            (Imperative.metadataToSourceLoc md fname trans₂.sourceText) _ h_after_neg
        exact h_after_uncond h
      | .error _, _ => simp at h_run
    | finish md =>
      rw [h_t] at h_run
      simp only at h_run
      injection h_run with h_run
      rw [← h_run]
      intro pc instr h
      -- ans.trans.instructions = trans₂.instructions.push endFunctionInstr.
      -- The unfolded form here uses an inline construction that matches
      -- endFunctionInstr definitionally.
      exact endFunction_emit_preserves_no_dead md fname trans₂ h_after_cmds h
  | .error _, _ => simp at h_run

/-! ## Preservation through `blocksFoldlM` -/

theorem blocksFoldlM_preserves_no_dead
    (fname : String)
    (blocks : List (String × Imperative.DetBlock String Core.Command Core.Expression))
    (st st' : Strata.CoreCFGTransLoopState)
    (h_run : blocks.foldlM (Strata.coreCFGToGotoBlockStep fname) st = Except.ok st')
    (h_no_dead : HasNoDead st.trans) :
    HasNoDead st'.trans := by
  induction blocks generalizing st with
  | nil =>
    simp [List.foldlM, pure, Except.pure] at h_run
    subst h_run; exact h_no_dead
  | cons head rest ih =>
    rw [List.foldlM_cons] at h_run
    match h_step : Strata.coreCFGToGotoBlockStep fname st head with
    | .ok st₁ =>
      rw [h_step] at h_run
      simp only [Bind.bind, Except.bind] at h_run
      have h_no_dead₁ : HasNoDead st₁.trans :=
        coreCFGToGotoBlockStep_preserves_no_dead fname head st st₁ h_step h_no_dead
      apply ih st₁ h_run
      exact h_no_dead₁
    | .error _ =>
      rw [h_step] at h_run
      simp [Bind.bind, Except.bind] at h_run

/-! ## Preservation through `coreCFGToGotoPatchStep` and `patchesFoldlM`

The patcher's per-step function in the no-loop-contracts case is a
no-op on `trans` (per A4's
`coreCFGToGotoPatchStep_no_contracts_trans_eq`). So `HasNoDead`
transfers trivially. -/

theorem coreCFGToGotoPatchStep_preserves_no_dead_no_contracts
    (labelMap : Std.HashMap String Nat)
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (idxLabel : Nat × String)
    (h_run : Strata.coreCFGToGotoPatchStep labelMap ∅ acc idxLabel = Except.ok acc')
    (h_no_dead : HasNoDead acc.2) :
    HasNoDead acc'.2 := by
  rw [coreCFGToGotoPatchStep_no_contracts_trans_eq labelMap acc acc' idxLabel h_run]
  exact h_no_dead

theorem patchesFoldlM_preserves_no_dead_no_contracts
    (labelMap : Std.HashMap String Nat)
    (patches : Array (Nat × String))
    (acc acc' : List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : patches.foldlM (Strata.coreCFGToGotoPatchStep labelMap ∅) acc = Except.ok acc')
    (h_no_dead : HasNoDead acc.2) :
    HasNoDead acc'.2 := by
  rw [patchesFoldlM_no_contracts_trans_eq labelMap patches acc acc' h_run]
  exact h_no_dead

/-! ## Preservation through `patchGotoTargets`

The patcher only mutates `target` — A4's `patchGotoTargets_preserves_type`
says every instruction's type after patching is the type of some
pre-existing instruction. Combined with the input being no-DEAD, the
output is no-DEAD. -/

theorem patchGotoTargets_preserves_no_dead
    (trans : Imperative.GotoTransform Core.Expression.TyEnv)
    (patches : List (Nat × Nat))
    (h_no_dead : HasNoDead trans) :
    HasNoDead (Imperative.patchGotoTargets trans patches) := by
  intro pc instr h
  obtain ⟨instr_pre, h_pre, h_ty⟩ :=
    patchGotoTargets_preserves_type trans patches pc instr h
  rw [h_ty]
  exact h_no_dead h_pre

/-! ## Final composition

Assemble the per-step preservation lemmas to get:

> `Strata.coreCFGToGotoTransform Env functionName cfg trans₀ = .ok ans` ⊢
> if `trans₀.instructions` has no DEAD, neither does `ans.instructions`.

`coreCFGToGotoTransform` decomposes as:

1. The entry-block check (a `pure ()` or `throw`; doesn't touch the
   transform).
2. `cfg.blocks.foldlM (coreCFGToGotoBlockStep ...) initSt` — applies
   `blocksFoldlM_preserves_no_dead`.
3. `st.pendingPatches.foldlM (coreCFGToGotoPatchStep ...) ([], st.trans)`
   — applies `patchesFoldlM_preserves_no_dead_no_contracts` *if* the
   loopContracts is `∅`.
4. Wrap with `patchGotoTargets`.

Step (3) requires `loopContracts = ∅`. Without that hypothesis the
patcher might mutate `guard` fields (it never mutates `type` though),
so we'd have to prove a more direct lemma about the patcher's effect
on `type`. In the meantime we expose this hypothesis.

(R6a's pipeline already only invokes the bridge with no-contract
inputs, so requiring `loopContracts = ∅` is consistent with the
existing call sites.) -/

/-- **Translator never emits DEAD instructions.**

Under the assumption that the initial transform has no DEAD
instructions and the no-loop-contracts assumption (consistent with
R6a's call sites), the translator's output also has no DEAD.

This `_explicit` form takes the decomposition pieces as inputs.
For the version that takes only `h_run`, see `no_dead_of_translator`
below. -/
theorem no_dead_of_translator_no_contracts_explicit
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (_h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans)
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
    HasNoDead ans := by
  -- Step 1: the blocks-fold preserves no-DEAD (initial state has no
  -- DEAD because trans₀ has no DEAD).
  have h_init_st : HasNoDead
      ({ trans := trans₀, pendingPatches := #[], labelMap := {},
         loopContracts := {} } : Strata.CoreCFGTransLoopState).trans :=
    h_init_no_dead
  have h_after_blocks : HasNoDead st_final.trans :=
    blocksFoldlM_preserves_no_dead functionName cfg.blocks _ st_final
      h_blocks_run h_init_st
  -- Step 2: the patches-fold preserves no-DEAD under empty loop contracts.
  rw [h_loopContracts_empty] at h_patches_run
  have h_init_acc : HasNoDead (([], st_final.trans) :
      List (Nat × Nat) × Imperative.GotoTransform Core.Expression.TyEnv).2 :=
    h_after_blocks
  have h_after_patches : HasNoDead trans_post :=
    patchesFoldlM_preserves_no_dead_no_contracts st_final.labelMap _
      ([], st_final.trans) (resolved, trans_post) h_patches_run h_init_acc
  -- Step 3: patchGotoTargets preserves no-DEAD.
  rw [h_ans_eq]
  apply patchGotoTargets_preserves_no_dead trans_post resolved
  exact h_after_patches

/-- **Translator never emits DEAD instructions** — direct form.

Takes only `h_run` plus the no-loop-contracts side condition.
Internally invokes `coreCFGToGotoTransform_decompose` to extract
the per-stage results. The no-loop-contracts side condition is the
analog of A4's `h_loopContracts_empty_post` — it's true for any CFG
without `LoopInvariant` / `Decreases` metadata, which is the case
for the round-6 / round-7 forward-simulation pipeline. -/
theorem no_dead_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    HasNoDead ans := by
  obtain ⟨st_final, resolved, trans_post, h_blocks_run, h_patches_run, h_ans_eq⟩ :=
    coreCFGToGotoTransform_decompose Env functionName cfg trans₀ ans h_run
  -- `coreCFGToGotoInitState trans₀` unfolds to the literal initial
  -- state we need.
  have h_blocks_run' :
      cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState)
      = Except.ok st_final := by
    have : coreCFGToGotoInitState trans₀ =
        ({ trans := trans₀, pendingPatches := #[], labelMap := {},
           loopContracts := {} } : Strata.CoreCFGTransLoopState) := by
      simp [coreCFGToGotoInitState]
    rw [this] at h_blocks_run
    exact h_blocks_run
  intro pc instr h
  exact no_dead_of_translator_no_contracts_explicit Env functionName cfg trans₀
    h_init_no_dead ans h_run st_final h_blocks_run'
    (h_loopContracts_empty_post st_final h_blocks_run)
    resolved trans_post h_patches_run h_ans_eq h

/-! ## Wrapper at the `Program` level

R6a's `h_no_dead` field works at the `Program.instrAt` level, not
directly on `trans.instructions[pc]?`. The two are interconvertible:
`Program.instrAt pgm pc` unfolds to `pgm.instructions[pc]?`. -/

/-- The translator never emits DEAD — at the `Program` level.

This is the precise shape of R6a's `h_no_dead` side hypothesis. -/
theorem no_dead_program_of_translator
    (Env : Core.Expression.TyEnv) (functionName : String)
    (cfg : Core.DetCFG)
    (trans₀ : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_init_no_dead : HasNoDead trans₀)
    (h_loopContracts_empty_post :
      ∀ (st_final : Strata.CoreCFGTransLoopState),
        cfg.blocks.foldlM (Strata.coreCFGToGotoBlockStep functionName)
          (coreCFGToGotoInitState trans₀)
        = Except.ok st_final → st_final.loopContracts = ∅)
    (ans : Imperative.GotoTransform Core.Expression.TyEnv)
    (h_run : Strata.coreCFGToGotoTransform Env functionName cfg trans₀
              = Except.ok ans) :
    ∀ {pc : Nat} {instr : Instruction},
      ({ name := "", parameterIdentifiers := #[],
         instructions := ans.instructions } : Program).instrAt pc =
        some instr →
      instr.type ≠ .DEAD := by
  intro pc instr h
  -- Program.instrAt pgm pc = pgm.instructions[pc]?.
  unfold Program.instrAt at h
  exact no_dead_of_translator Env functionName cfg trans₀ h_init_no_dead
    h_loopContracts_empty_post ans h_run h

end CProverGOTO.NoDead
