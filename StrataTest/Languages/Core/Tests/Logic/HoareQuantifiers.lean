/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.ContractToHoareTriple
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteProps
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LStateProps
import Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Languages.Core.IntEvalProps

set_option linter.unusedVariables false

/-! # Core procedure contracts over quantifier/branch bodies, via `Procedure.contractTriple`

Three small Core procedures are declared together in surface syntax, translated, and
annotated by the type-inference phase used in Core verification. Each has a structured
body `if x then assert (∀ y : bool, y = y) else assert false`, guarded differently:

* `pAssume` prefixes the conditional with `assume x`;
* `pNoAssume` drops the guard entirely;
* `pReq` guards it with a `requires x` precondition.

The results are stated directly as `Core.Logic.Hoare.Procedure.contractTriple`, read over
the denotational interpretation `Core.Logic.DenoteBasedInterp model`.  Every assumption
is the model-indexed semantic contract clause (`Procedure.preAsPredicate`,
`Procedure.contractPre`, `Procedure.contractPost`). The `assume`/`requires` guard is
threaded through the trace's own assumption/precondition, so the `assert false` branch
becomes vacuous; the tautological branch is discharged by the `∀`-quantifier being true
in every world
(`Lambda.denote_quant_all_true`), since a condition holds when it evaluates to `true`.
`pNoAssume`, lacking any guard, cannot meet its contract, and its reading is refuted on a
concrete `false`-valued entry environment.

The triples are proved directly from the event small-step semantics `StepStmtStarE`,
without appealing to a structural Hoare rule: the assume/requires gating needs the whole
trace (with its assumptions threaded), which the structural `seq` rule cannot carry
across a command boundary.

Key results:
- `pAssume_meets_contract` proves the explicitly assumed guard;
- `pNoAssume_contract_refuted` refutes the unguarded body;
- `pReq_meets_contract` proves the contract-precondition guard.
-/

namespace CoreHoareQuantifiersTest

open Imperative
open Core (Expression Command Statement Statements)

open CoreHoareTestSupport

/-! ## Typed Core syntax fixtures

The declarations below parse one Core source program, run Core verification's
type-inference phase, and project the inferred procedures and bodies used by the
operational and denotational proofs. -/

private def examplePgm : StrataDDM.Program :=
#strata
program Core;

procedure pAssume(x : bool)
{
  assume [a]: x;
  if (x) {
    assert [t]: forall y : bool :: y == y;
  } else {
    assert [f]: false;
  }
};

procedure pNoAssume(x : bool)
{
  if (x) {
    assert [t]: forall y : bool :: y == y;
  } else {
    assert [f]: false;
  }
};

procedure pReq(x : bool)
spec {
  requires [requires_x]: x;
}
{
  if (x) {
    assert [t]: forall y : bool :: y == y;
  } else {
    assert [f]: false;
  }
};
#end

private def examplePgmASTUntyped : Core.Program :=
  (Strata.TransM.run Inhabited.default
    (Strata.translateProgram examplePgm)).fst.stripMetaData

/-- The syntax program after Core verification's type-inference phase. -/
private def examplePgmAST : Core.Program :=
  match _root_.Core.typeCheck .quiet examplePgmASTUntyped with
  | .ok program => program
  | .error _ => default

/-- The inferred program's `pAssume` procedure. -/
private def pAssumeProc : Core.Procedure :=
  (examplePgmAST.findProcByString? "pAssume").get!

/-- The inferred program's `pNoAssume` procedure. -/
private def pNoAssumeProc : Core.Procedure :=
  (examplePgmAST.findProcByString? "pNoAssume").get!

/-- The inferred program's `pReq` procedure. -/
private def pReqProc : Core.Procedure :=
  (examplePgmAST.findProcByString? "pReq").get!

/-- The inferred (metadata-carrying) structured body of `pAssume`. -/
private def pAssumeBody : Core.Statements :=
  match pAssumeProc.body with | .structured b => b | _ => []

/-- The inferred (metadata-carrying) structured body of `pNoAssume`. -/
private def pNoAssumeBody : Core.Statements :=
  match pNoAssumeProc.body with | .structured b => b | _ => []

/-- The inferred (metadata-carrying) structured body of `pReq`. -/
private def pReqBody : Core.Statements :=
  match pReqProc.body with | .structured b => b | _ => []

/-- The expected inferred identifier and expression shapes used by the
operational and denotational proofs. -/
private abbrev xIdent : Core.Expression.Ident := ⟨"x", ()⟩
private abbrev xExpr : Core.Expression.Expr := .fvar () xIdent (some Lambda.LMonoTy.bool)
private abbrev ff0 : Core.Expression.Expr :=
  Lambda.LExpr.const () (Lambda.LConst.boolConst false)
private abbrev forallExpr : Core.Expression.Expr :=
  .quant () .all "y" (some Lambda.LMonoTy.bool) (.bvar () 0)
    (.eq () (.bvar () 0) (.bvar () 0))

/-! ### Metadata projections

Type inference annotates each command with source metadata.  These helpers read that
metadata back out of a projected body so the structured shapes below mention the real
metadata rather than `#[]`.  `holds` ignores metadata, so the denotational facts do not
depend on which metadata flows through. -/

/-- Metadata on the leading `assume` of a body (if any). -/
private def assumeMdOf (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | (Core.Statement.assume _ _ md :: _) => md
  | _ => #[]

/-- Metadata on the body's conditional. -/
private def iteMdOf (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | [Stmt.ite _ _ _ md] => md
  | [_, Stmt.ite _ _ _ md] => md
  | _ => #[]

/-- Metadata on the conditional's then-branch assertion. -/
private def thenMdOf (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | [Stmt.ite _ (Core.Statement.assert _ _ md :: _) _ _] => md
  | [_, Stmt.ite _ (Core.Statement.assert _ _ md :: _) _ _] => md
  | _ => #[]

/-- Metadata on the conditional's else-branch assertion. -/
private def elseMdOf (ss : Core.Statements) : Imperative.MetaData Core.Expression :=
  match ss with
  | [Stmt.ite _ _ (Core.Statement.assert _ _ md :: _) _] => md
  | [_, Stmt.ite _ _ (Core.Statement.assert _ _ md :: _) _] => md
  | _ => #[]

/-- `pAssume`'s body is `assume x; if x then assert (∀ y, y = y) else assert false`. -/
private theorem pAssumeBody_eq :
    pAssumeBody =
      [Core.Statement.assume "a" xExpr (assumeMdOf pAssumeBody),
       Stmt.ite (.det xExpr)
         [Core.Statement.assert "t" forallExpr (thenMdOf pAssumeBody)]
         [Core.Statement.assert "f" ff0 (elseMdOf pAssumeBody)]
         (iteMdOf pAssumeBody)] := by native_decide

/-- `pNoAssume`'s body is `if x then assert (∀ y, y = y) else assert false`. -/
private theorem pNoAssumeBody_eq :
    pNoAssumeBody =
      [Stmt.ite (.det xExpr)
         [Core.Statement.assert "t" forallExpr (thenMdOf pNoAssumeBody)]
         [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)]
         (iteMdOf pNoAssumeBody)] := by native_decide

/-- `pReq`'s body is `if x then assert (∀ y, y = y) else assert false`. -/
private theorem pReqBody_eq :
    pReqBody =
      [Stmt.ite (.det xExpr)
         [Core.Statement.assert "t" forallExpr (thenMdOf pReqBody)]
         [Core.Statement.assert "f" ff0 (elseMdOf pReqBody)]
         (iteMdOf pReqBody)] := by native_decide

/-- The inferred `pAssume` body is `.structured pAssumeBody`. -/
private theorem pAssumeProc_body : pAssumeProc.body = .structured pAssumeBody := by
  native_decide

/-- The inferred `pNoAssume` body is `.structured pNoAssumeBody`. -/
private theorem pNoAssumeProc_body : pNoAssumeProc.body = .structured pNoAssumeBody := by
  native_decide

/-- The inferred `pReq` body is `.structured pReqBody`. -/
private theorem pReqProc_body : pReqProc.body = .structured pReqBody := by
  native_decide

/-- Procedure lookup resolves `pAssume`. -/
private theorem pAssumeProc_named :
    examplePgmAST.findProcByString? "pAssume" = some pAssumeProc := by native_decide

/-- Procedure lookup resolves `pNoAssume`. -/
private theorem pNoAssumeProc_named :
    examplePgmAST.findProcByString? "pNoAssume" = some pNoAssumeProc := by native_decide

/-- Procedure lookup resolves `pReq`. -/
private theorem pReqProc_named :
    examplePgmAST.findProcByString? "pReq" = some pReqProc := by native_decide

/-- The inferred requires check, including its source metadata. -/
private def pReqCheck : Core.Procedure.Check :=
  match pReqProc.spec.preconditions.toList with
  | [("requires_x", check)] => check
  | _ => default

/-- `pReq` has exactly the projected requires check. -/
private theorem pReqPreconditions_eq :
    pReqProc.spec.preconditions.toList = [("requires_x", pReqCheck)] := by native_decide

/-- Type inference annotates the requires expression as Boolean `x`. -/
private theorem pReqCheck_expr_eq : pReqCheck.expr = xExpr := by native_decide

/-- `∀ y : bool, y = y` is well-typed at `bool`. -/
private theorem forallExpr_ty : Lambda.LExpr.HasTypeA [] forallExpr .bool :=
  Lambda.LExpr.typeCheck_to_HasTypeA (by rfl)

/-- Gate parameters: no reserved prefixes, every operator counts as declared. -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-! ## Operational run inversions over the event semantics -/

section
variable (π : String → Option Core.Procedure)

/-- Invert a finished traced run of the quantifier conditional
    `if x then [assert (∀ y, y = y)] else [assert false]` (with arbitrary metadata):
    the guard `x` evaluated to `tt` (then the then-branch ran) or to `ff` (then the
    else-branch ran).  Either branch is a single assert, so the trace is the
    corresponding singleton assert event. -/
private theorem ite_run_inv
    {mdT mdF mdIte : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression}
    {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Stmt.ite (.det xExpr)
          [Core.Statement.assert "t" forallExpr mdT]
          [Core.Statement.assert "f" ff0 mdF] mdIte) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Stmt.ite (.det xExpr)
          [Core.Statement.assert "t" forallExpr mdT]
          [Core.Statement.assert "f" ff0 mdF] mdIte) ρ) tr (.exiting lbl ρ')) :
    (Core.Expression.eval ρ.factory ρ.store xExpr = some (HasBool.ttVal ρ.factory) ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "t", forallExpr, mdT⟩]) ∨
    (Core.Expression.eval ρ.factory ρ.store xExpr = some (HasBool.ffVal ρ.factory) ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "f", ff0, mdF⟩]) := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_ite_true hc =>
        obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inl hrest)
        have ⟨htr, _⟩ := assert_run_inv π (l := "t") (e := forallExpr) (md := mdT) (ρ := ρ)
          (ρ' := ρi) (singleton_run_inv π hin)
        exact .inl ⟨hc, by simpa using htr⟩
      | step_ite_false hc =>
        obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inl hrest)
        have ⟨htr, _⟩ := assert_run_inv π (l := "f") (e := ff0) (md := mdF) (ρ := ρ)
          (ρ' := ρi) (singleton_run_inv π hin)
        exact .inr ⟨hc, by simpa using htr⟩
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_ite_true hc =>
        obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inr ⟨lbl, hrest⟩)
        have ⟨htr, _⟩ := assert_run_inv π (l := "t") (e := forallExpr) (md := mdT) (ρ := ρ)
          (ρ' := ρi) (singleton_run_inv π hin)
        exact .inl ⟨hc, by simpa using htr⟩
      | step_ite_false hc =>
        obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inr ⟨lbl, hrest⟩)
        have ⟨htr, _⟩ := assert_run_inv π (l := "f") (e := ff0) (md := mdF) (ρ := ρ)
          (ρ' := ρi) (singleton_run_inv π hin)
        exact .inr ⟨hc, by simpa using htr⟩

end

/-! ## Facts about the two captured assertions -/

/-- `∀ y : bool, y = y` evaluates to `true` in every runtime factory and store: it is
    closed and denotes `true`. -/
private theorem forallExpr_eval (f : Core.Expression.Factory) (σ : SemanticStore Core.Expression) :
    Core.Expression.eval f σ forallExpr = some (HasBool.ttVal f) := by
  refine Lambda.LExpr.denoteEval_eq_ofBool_iff (T := Core.CoreLParams) |>.mpr
    ⟨fun x hx => by simp [Lambda.LExpr.LExpr.getVars] at hx, forallExpr_ty, ?_⟩
  have hbody : Lambda.LExpr.HasTypeA [Lambda.LMonoTy.bool]
      ((.eq () (.bvar () 0) (.bvar () 0) : Core.Expression.Expr)) .bool :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  apply Lambda.denote_quant_all_true .nil hbody forallExpr_ty
  intro x
  exact Lambda.denote_eq_true (.cons x .nil) (.bvar (by rfl)) (.bvar (by rfl)) hbody rfl

/-- `∀ y : bool, y = y` holds in every world when captured under a runtime factory over
    `factory` (independent of the store and the metadata carried by the event). -/
private theorem forall_holds (factory : Lambda.Factory Core.CoreLParams)
    (world : Core.Logic.DenoteValuation factory)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory)
    (md : Imperative.MetaData Core.Expression) (hf : f.factory = factory) :
    (Core.Logic.DenoteBasedInterp factory).holds world ⟨f, σ, "t", forallExpr, md⟩ :=
  .inl ⟨hf, forallExpr_eval f σ⟩

/-- The `false` literal captured under a runtime factory over `factory` never holds: it
    evaluates to `false`, whatever metadata the event carries. -/
private theorem false_not_holds (factory : Lambda.Factory Core.CoreLParams)
    (world : Core.Logic.DenoteValuation factory)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory)
    (md : Imperative.MetaData Core.Expression) (hf : f.factory = factory) :
    ¬ (Core.Logic.DenoteBasedInterp factory).holds world ⟨f, σ, "f", ff0, md⟩ := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · exact HasBool.ttVal_ne_ffVal f
      (Option.some.inj (hex.symm.trans (Core.eval_boolConst f σ false)))
  · exact hne hf

/-- A condition `x` that evaluates to `false` does not hold in any world over `factory`.
    This is the shared kernel of the "assume/requires gates the false branch" argument. -/
private theorem xFalse_notHolds (factory : Lambda.Factory Core.CoreLParams)
    (ρ : Imperative.Env Core.Expression) (world : Core.Logic.DenoteValuation factory)
    (lbl : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (hfac : ρ.factory.factory = factory)
    (hc : Core.Expression.eval ρ.factory ρ.store xExpr = some (HasBool.ffVal ρ.factory)) :
    ¬ (Core.Logic.DenoteBasedInterp factory).holds world ⟨ρ.factory, ρ.store, lbl, xExpr, md⟩ := by
  rintro (⟨_hfac, hex⟩ | ⟨hne, _⟩)
  · exact HasBool.ttVal_ne_ffVal ρ.factory (Option.some.inj (hex.symm.trans hc))
  · exact hne hfac

/-! ## Example 1 — `pAssume` meets its (trivial) contract -/

/-- **`pAssume` meets its contract.** The `assume x` gates the false branch, so the only
    assertion reached is the quantifier tautology. -/
theorem pAssume_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pAssume" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    examplePgmAST testParams "pAssume" pAssumeProc pAssumeBody
    pAssumeProc_named pAssumeProc_body (by native_decide) ?_
  intro ρ₀ ρ' trace hpre hwf hrun
  obtain ⟨_hpreP, hfac, _hold, _hin⟩ := hpre
  obtain ⟨ρ_inner, hinner, _hρ'⟩ :=
    stmt_block_reaches_doneE (singleton_run_inv examplePgmAST.findProcByString? hrun)
  refine ⟨?_, fun _ => ?_⟩
  ·
    rw [pAssumeBody_eq] at hinner
    rcases stmts_append_doneE (Core.EvalCommandE examplePgmAST.findProcByString?)
      [Core.Statement.assume "a" xExpr (assumeMdOf pAssumeBody)]
      [Stmt.ite (.det xExpr)
        [Core.Statement.assert "t" forallExpr (thenMdOf pAssumeBody)]
        [Core.Statement.assert "f" ff0 (elseMdOf pAssumeBody)]
        (iteMdOf pAssumeBody)] ρ₀ ρ_inner hinner with
      ⟨lbl, hexit₁⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm₁, hfin₂⟩
    · exact absurd hexit₁ (stmts_exitsCoveredByBlocks_noEscapeE
        (Core.EvalCommandE examplePgmAST.findProcByString?)
        [Core.Statement.assume "a" xExpr (assumeMdOf pAssumeBody)]
        (by simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks]) ρ₀ lbl ρ_inner)
    ·
      obtain ⟨htr₁, hρ₁⟩ := assume_run_inv examplePgmAST.findProcByString?
        (l := "a") (e := xExpr) (md := assumeMdOf pAssumeBody) (ρ := ρ₀) (ρ' := ρ₁)
        (singleton_run_inv examplePgmAST.findProcByString? (.inl hterm₁))
      subst ρ₁; subst htr; subst htr₁
      rcases ite_run_inv examplePgmAST.findProcByString? (ρ := ρ₀) (ρ' := ρ_inner)
        (singleton_run_inv examplePgmAST.findProcByString? hfin₂) with
        ⟨_hc, htr₂⟩ | ⟨hc, htr₂⟩
      ·
        subst htr₂
        exact ⟨fun _ world _ => forall_holds _ world ρ₀.store ρ₀.factory _ hfac, trivial⟩
      ·
        subst htr₂
        refine ⟨fun _ world hassum => absurd
          (hassum ⟨ρ₀.factory, ρ₀.store, "a", xExpr, assumeMdOf pAssumeBody⟩ (by simp))
          (xFalse_notHolds _ ρ₀ world "a" (assumeMdOf pAssumeBody) hfac hc), trivial⟩
  ·
    intro label check hmem _hattr
    rw [show pAssumeProc.spec.postconditions.toList = [] from by native_decide] at hmem
    simp at hmem

/-! ## Example 2 — dropping the guard makes the contract unmeetable -/

/-- A total `false`-valued environment over the runtime factory of `model`. -/
private def xFalseEnv (model : Lambda.Interp Core.Factory) : Imperative.Env Core.Expression :=
  { store := fun _ =>
      some (HasBool.ffVal (boolFactory model)),
    factory := boolFactory model }

/-- `xFalseEnv` holds only values of its factory. -/
private theorem xFalseEnv_storeWellDefined (model : Lambda.Interp Core.Factory) :
    Imperative.WellFormedStore (xFalseEnv model).store (xFalseEnv model).factory := by
  intro n v hn
  simp only [xFalseEnv, Option.some.injEq] at hn
  subst hn
  rfl

/-- Reading `x` from `xFalseEnv` yields `false`. -/
private theorem xFalseEnv_eval_x (model : Lambda.Interp Core.Factory) :
    Core.Expression.eval (xFalseEnv model).factory (xFalseEnv model).store xExpr =
      some (HasBool.ffVal (xFalseEnv model).factory) :=
  Core.eval_fvar _ rfl rfl

/-- The completed event run of the procedure-block-wrapped assumeless body on
    `xFalseEnv`: it enters the procedure block, takes the else branch, and emits exactly
    the `assert false` event, leaving the store unchanged. -/
private theorem xFalseEnv_blockrun (model : Lambda.Interp Core.Factory)
    (π : String → Option Core.Procedure) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts [Stmt.block "" pNoAssumeBody #[]] (xFalseEnv model))
      [Event.assert
          ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal (xFalseEnv model)) := by
  have hbody : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts pNoAssumeBody (xFalseEnv model))
      [Event.assert
          ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal (xFalseEnv model)) := by
    rw [pNoAssumeBody_eq]
    have hassert : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] (xFalseEnv model))
        [Event.assert
            ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.terminal (xFalseEnv model)) := by
      refine .step _ [] _ _ _ .step_stmts_cons ?_
      refine .step _ _ _ _ _
        (StepStmtE.step_seq_inner (.step_cmd (Core.EvalCommandE.cmd_sem
          Imperative.EvalCmdE.eval_assert))) ?_
      refine .step _ [] _ _ _ .step_seq_done ?_
      exact .step _ [] _ _ _ .step_stmts_nil (.refl _)
    have hblock : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.block .none (xFalseEnv model).store
          (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] (xFalseEnv model)))
        [Event.assert
            ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.block .none (xFalseEnv model).store (.terminal (xFalseEnv model))) :=
      block_inner_starE hassert
    have heq : ({ (xFalseEnv model) with
        store := projectStore (xFalseEnv model).store (xFalseEnv model).store }
        : Imperative.Env Core.Expression) = (xFalseEnv model) := by
      simp [projectStore_self]
    have hblock_done : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.block .none (xFalseEnv model).store
          (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] (xFalseEnv model)))
        [Event.assert
            ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.terminal (xFalseEnv model)) := by
      refine ReflTransTrace.trans _ hblock ?_
      rw [← heq]
      exact .step _ [] _ _ _ .step_block_done (.refl _)
    refine .step _ [] _ _ _ .step_stmts_cons ?_
    refine .step _ [] _ _ _
      (.step_seq_inner (.step_ite_false (xFalseEnv_eval_x model))) ?_
    refine ReflTransTrace.trans _ (seq_inner_starE (Core.EvalCommandE π)
      (ss := []) hblock_done) ?_
    refine .step _ [] _ _ _ .step_seq_done ?_
    exact .step _ [] _ _ _ .step_stmts_nil (.refl _)
  have hblock : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.block (.some "") (xFalseEnv model).store (.stmts pNoAssumeBody (xFalseEnv model)))
      [Event.assert
          ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.block (.some "") (xFalseEnv model).store (.terminal (xFalseEnv model))) :=
    block_inner_starE hbody
  have heq : ({ (xFalseEnv model) with
      store := projectStore (xFalseEnv model).store (xFalseEnv model).store }
      : Imperative.Env Core.Expression) = (xFalseEnv model) := by
    simp [projectStore_self]
  have hblock_done : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.block (.some "") (xFalseEnv model).store (.stmts pNoAssumeBody (xFalseEnv model)))
      [Event.assert
          ⟨(xFalseEnv model).factory, (xFalseEnv model).store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal (xFalseEnv model)) := by
    refine ReflTransTrace.trans _ hblock ?_
    rw [← heq]
    exact .step _ [] _ _ _ .step_block_done (.refl _)
  refine .step _ [] _ _ _ .step_stmts_cons ?_
  refine .step _ [] _ _ _ (.step_seq_inner .step_block) ?_
  refine ReflTransTrace.trans _ (seq_inner_starE (Core.EvalCommandE π)
    (ss := []) hblock_done) ?_
  refine .step _ [] _ _ _ .step_seq_done ?_
  exact .step _ [] _ _ _ .step_stmts_nil (.refl _)

/-- The typing that gives every variable the Boolean type annotates every list of Boolean
    occurrences. -/
private theorem annotates_boolTy {occs : List (Core.Expression.Ident × Core.Expression.Ty)}
    (h : ∀ p ∈ occs, p.2 = HasBool.boolTy (P := Core.Expression)) :
    VarTyping.annotates (fun _ => some (HasBool.boolTy (P := Core.Expression))) occs :=
  fun _ _ hm => congrArg some (h _ hm).symm

/-- Block-level well-formedness for the procedure-block-wrapped assumeless body on
    `(xFalseEnv model)`, via `of_defUseOk` (which re-derives `readWritesDefined`).  The block
    scopes every variable, reserved-prefix fields are vacuous for `testParams`, and
    `defUseOk` holds since every variable is defined. -/
private theorem xFalseEnv_blockWF (model : Lambda.Interp Core.Factory) :
    Core.Logic.BlockInitEnvWF testParams [Stmt.block "" pNoAssumeBody #[]] (xFalseEnv model) :=
  Core.Logic.BlockInitEnvWF.of_defUseOk
    (Core.coreFactory_WellFormedSemanticEval _ rfl)
    (xFalseEnv_storeWellDefined model)
    (by intro n hn
        rw [show Block.definedVars (P := Core.Expression) (C := Core.Command)
          [Stmt.block "" pNoAssumeBody #[]] false = [] from by native_decide] at hn
        simp at hn)
    (by intro n hn p hp; simp [testParams] at hp)
    (by intro n hn p hp; simp [testParams] at hp)
    (by
      have hdef : (fun n => ((xFalseEnv model).store n).isSome) =
          (fun _ : Core.Expression.Ident => true) := by funext n; simp [xFalseEnv]
      show Block.defUseWellFormed (fun n => ((xFalseEnv model).store n).isSome)
        testParams.declaredFuncs [Stmt.block "" pNoAssumeBody #[]] = true
      rw [hdef]
      native_decide)
    (by intro nm _; rfl)
    (by
      intro ty hty
      rw [show Block.initTypes (P := Core.Expression) (C := Core.Command)
        [Stmt.block "" pNoAssumeBody #[]] = [] from by native_decide] at hty
      simp at hty)
    ⟨fun _ => some (HasBool.boolTy (P := Core.Expression)), fun _ ty hty => by
        obtain rfl := Option.some.inj hty
        exact ⟨_, rfl, (HasBool.boolIsValOfTy _).2⟩, by
      rw [pNoAssumeBody_eq]
      simp only [Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, and_true]
      exact ⟨annotates_boolTy (by decide +kernel), annotates_boolTy (by decide +kernel),
        annotates_boolTy (by decide +kernel)⟩⟩

/-- **`pNoAssume` cannot meet its contract.** With no guard on the conditional, a
    well-typed `false`-valued entry runs the `assert false` with no discharging
    assumption, refuting the structured triple its contract names. -/
theorem pNoAssume_contract_refuted :
    ¬ Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pNoAssume" := by
  have hfactory : examplePgmAST.factoryBeforeProcedure "pNoAssume" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory] at h
  obtain ⟨proc, hfind, _htyped, htriple⟩ := h
  obtain rfl : proc = pNoAssumeProc :=
    Option.some.inj (hfind.symm.trans pNoAssumeProc_named)
  rw [pNoAssumeProc_body] at htriple
  have hpre : Core.Logic.Hoare.Procedure.contractPre Core.Factory pNoAssumeProc
      (xFalseEnv model) := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · intro label check hmem
      rw [show pNoAssumeProc.spec.preconditions.toList = [] from by native_decide] at hmem
      simp at hmem
    · intro id hid; rfl
    · intro id ty hmem
      rw [show pNoAssumeProc.header.inputs.toList = [(xIdent, Lambda.LMonoTy.bool)]
        from by native_decide] at hmem
      simp only [List.mem_singleton] at hmem
      obtain ⟨rfl, rfl⟩ := hmem
      exact ⟨_, rfl, rfl⟩
  have hres := htriple (xFalseEnv model) (xFalseEnv model) _ hpre (xFalseEnv_blockWF model)
    (.inl (xFalseEnv_blockrun model examplePgmAST.findProcByString?))
  have hfalse := hres.1.1 trivial (someValuation _)
    (by intro condition hmem; simp at hmem)
  exact false_not_holds _ (someValuation _) (xFalseEnv model).store
    (xFalseEnv model).factory (elseMdOf pNoAssumeBody) rfl hfalse

/-! ## Example 3 — a `requires x` precondition makes the assumeless contract meetable -/

/-- **`pReq` meets its contract.** Reading `requires x` as the semantic
    `Procedure.preAsPredicate` forces the then branch, so only the quantifier tautology is
    asserted. -/
theorem pReq_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pReq" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    examplePgmAST testParams "pReq" pReqProc pReqBody
    pReqProc_named pReqProc_body (by native_decide) ?_
  intro ρ₀ ρ' trace hpre hwf hrun
  obtain ⟨hpreP, hfac, _hold, _hin⟩ := hpre
  obtain ⟨ρ_inner, hinner, _hρ'⟩ :=
    stmt_block_reaches_doneE (singleton_run_inv examplePgmAST.findProcByString? hrun)
  refine ⟨?_, fun _ => ?_⟩
  ·
    rw [pReqBody_eq] at hinner
    rcases ite_run_inv examplePgmAST.findProcByString? (ρ := ρ₀) (ρ' := ρ_inner)
      (singleton_run_inv examplePgmAST.findProcByString? hinner) with
      ⟨_hc, htr⟩ | ⟨hc, htr⟩
    ·
      subst htr
      exact ⟨fun _ world _ => forall_holds _ world ρ₀.store ρ₀.factory _ hfac, trivial⟩
    ·
      subst htr
      refine ⟨fun _ world _ => ?_, trivial⟩
      exfalso
      have hmem : ("requires_x", pReqCheck) ∈ pReqProc.spec.preconditions.toList := by
        rw [pReqPreconditions_eq]; exact List.mem_cons_self
      have hcheck := hpreP "requires_x" pReqCheck hmem (someValuation _)
      rw [pReqCheck_expr_eq] at hcheck
      exact xFalse_notHolds _ ρ₀ (someValuation _) "requires_x" pReqCheck.md
        hfac hc hcheck
  ·
    intro label check hmem _hattr
    rw [show pReqProc.spec.postconditions.toList = [] from by native_decide] at hmem
    simp at hmem

end CoreHoareQuantifiersTest
