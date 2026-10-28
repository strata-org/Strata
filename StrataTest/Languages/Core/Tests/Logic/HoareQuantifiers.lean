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

set_option linter.unusedSimpArgs false
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
(`Lambda.denote_quant_all_true`).  `pNoAssume`, lacking any guard, cannot meet its
contract, and its reading is refuted on a concrete `false`-valued entry environment.

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
    (Core.Expression.eval ρ.factory ρ.store xExpr = some HasBool.tt ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "t", forallExpr, mdT⟩]) ∨
    (Core.Expression.eval ρ.factory ρ.store xExpr = some HasBool.ff ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "f", ff0, mdF⟩]) := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
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
      | step_admin hadmin => cases hadmin with
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

/-! ## Denotational facts about the two captured assertions -/

/-- `∀ y : bool, y = y` denotes `true` in every world (independent of model, valuation,
    and the metadata carried by the event). -/
private theorem forall_holds (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory)
    (md : Imperative.MetaData Core.Expression) (hf : f = Core.Factory) :
    (Core.Logic.DenoteBasedInterp model).holds world ⟨f, σ, "t", forallExpr, md⟩ := by
  refine .inl ⟨hf, ?_⟩
  have hcap : Core.Logic.capturedExpr
      (⟨f, σ, "t", forallExpr, md⟩ : Imperative.EventArg Core.Expression) = forallExpr := by
    apply Lambda.LExpr.substFvarsFromEnv_closed_identity; rfl
  rw [hcap]
  refine ⟨forallExpr_ty, ?_⟩
  have hbody : Lambda.LExpr.HasTypeA [Lambda.LMonoTy.bool]
      ((.eq () (.bvar () 0) (.bvar () 0) : Core.Expression.Expr)) .bool :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  apply Lambda.denote_quant_all_true .nil hbody forallExpr_ty
  intro x
  exact Lambda.denote_eq_true (.cons x .nil) (.bvar (by rfl)) (.bvar (by rfl)) hbody rfl

/-- The `false` literal captured under the ambient factory never holds: its closed
captured form denotes `false`, whatever metadata the event carries. -/
private theorem false_not_holds (model : Lambda.Interp Core.Factory)
    (world : Core.Logic.DenoteValuation model)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory)
    (md : Imperative.MetaData Core.Expression) (hf : f = Core.Factory) :
    ¬ (Core.Logic.DenoteBasedInterp model).holds world ⟨f, σ, "f", ff0, md⟩ := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · have hcap : Core.Logic.capturedExpr
        (⟨f, σ, "f", ff0, md⟩ : Imperative.EventArg Core.Expression) = ff0 := rfl
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    exact Bool.false_ne_true ((Lambda.denote_boolConst _ _ _ _ _ _hty).symm.trans hd)
  · exact hne hf

/-- A `bool` variable `x` bound to `false` refutes the captured condition `x`: its closed
captured form `false` denotes `false`, so `x` cannot hold in any world of any model.
This is the shared kernel of the "assume/requires gates the false branch" argument. -/
private theorem xFalse_notHolds (model : Lambda.Interp Core.Factory)
    (ρ : Imperative.Env Core.Expression) (world : Core.Logic.DenoteValuation model)
    (lbl : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (hsem : Imperative.WellFormedSemanticEval (P := Core.Expression) ρ.factory)
    (hwfs : Imperative.WellFormedStore ρ.store ρ.factory)
    (hfac : ρ.factory = Core.Factory)
    (hc : Core.Expression.eval ρ.factory ρ.store xExpr = some HasBool.ff) :
    ¬ (Core.Logic.DenoteBasedInterp model).holds world ⟨ρ.factory, ρ.store, lbl, xExpr, md⟩ := by
  rintro (⟨_hfac, hex⟩ | ⟨hne, _⟩)
  · have hvar := hsem.var xExpr xIdent ρ.store hwfs rfl
    have hstore : ρ.store xIdent = some ff0 := by rw [← hvar]; exact hc
    have hcap : Core.Logic.capturedExpr
        (⟨ρ.factory, ρ.store, lbl, xExpr, md⟩ : Imperative.EventArg Core.Expression) = ff0 := by
      simp only [Core.Logic.capturedExpr, xExpr, Lambda.LExpr.substFvarsFromEnv,
        Lambda.Env.mk, hstore]
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    exact Bool.false_ne_true ((Lambda.denote_boolConst _ _ _ _ _ _hty).symm.trans hd)
  · exact hne hfac

/-! ## Example 1 — `pAssume` meets its (trivial) contract -/

/-- **`pAssume` meets its contract.** The `assume x` gates the false branch, so the only
    assertion reached is the quantifier tautology. -/
theorem pAssume_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pAssume" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    examplePgmAST testParams "pAssume" pAssumeProc pAssumeBody
    pAssumeProc_named pAssumeProc_body (by native_decide) ?_
  intro model ρ₀ ρ' trace hpre hwf hrun
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
        exact ⟨fun _ world _ => forall_holds model world ρ₀.store ρ₀.factory _ hfac, trivial⟩
      ·
        subst htr₂
        refine ⟨fun _ world hassum => absurd
          (hassum ⟨ρ₀.factory, ρ₀.store, "a", xExpr, assumeMdOf pAssumeBody⟩ (by simp))
          (xFalse_notHolds model ρ₀ world "a" (assumeMdOf pAssumeBody)
            hwf.toWellFormedSemanticEval hwf.storeWellDefined hfac hc), trivial⟩
  ·
    intro label check hmem _hattr
    rw [show pAssumeProc.spec.postconditions.toList = [] from by native_decide] at hmem
    simp at hmem

/-! ## Example 2 — dropping the guard makes the contract unmeetable -/

/-- A total `false`-valued environment over `Core.Factory`. -/
private def xFalseEnv : Imperative.Env Core.Expression :=
  { store := fun _ => some ff0, factory := Core.Factory, hasFailure := false }

/-- `xFalseEnv` holds only values (every binding is the `false` literal). -/
private theorem xFalseEnv_storeWellDefined :
    Imperative.WellFormedStore xFalseEnv.store Core.Factory := by
  intro n v hn
  simp only [xFalseEnv] at hn
  injection hn with hv; subst hv
  show Lambda.LExpr.isValue _ ff0 = true
  exact Lambda.isValue_const_true _ _ _

/-- Reading `x` from `xFalseEnv` yields `false`. -/
private theorem xFalseEnv_eval_x :
    Core.Expression.eval Core.Factory xFalseEnv.store xExpr = some HasBool.ff := by
  have hvar := Core.coreFactory_WellFormedSemanticEval.var xExpr xIdent xFalseEnv.store
    xFalseEnv_storeWellDefined rfl
  exact hvar.trans rfl

/-- The completed event run of the procedure-block-wrapped assumeless body on
    `xFalseEnv`: it enters the procedure block, takes the else branch, and emits exactly
    the `assert false` event, leaving the store unchanged. -/
private theorem xFalseEnv_blockrun (π : String → Option Core.Procedure) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts [Stmt.block "" pNoAssumeBody #[]] xFalseEnv)
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal xFalseEnv) := by
  have hbody : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.stmts pNoAssumeBody xFalseEnv)
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal xFalseEnv) := by
    rw [pNoAssumeBody_eq]
    have hassert : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] xFalseEnv)
        [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.terminal xFalseEnv) := by
      refine .step _ [] _ _ _ (.step_admin .step_stmts_cons) ?_
      refine .step _ _ _ _ _
        (StepStmtE.step_seq_inner (.step_cmd (Core.EvalCommandE.cmd_sem
          Imperative.EvalCmdE.eval_assert))) ?_
      refine .step _ [] _ _ _ (.step_admin .step_seq_done) ?_
      exact .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)
    have hblock : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.block .none xFalseEnv.store
          (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] xFalseEnv))
        [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.block .none xFalseEnv.store (.terminal xFalseEnv)) :=
      block_inner_starE hassert
    have heq : ({ xFalseEnv with
        store := projectStore xFalseEnv.store xFalseEnv.store }
        : Imperative.Env Core.Expression) = xFalseEnv := by
      simp [projectStore_self]
    have hblock_done : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.block .none xFalseEnv.store
          (.stmts [Core.Statement.assert "f" ff0 (elseMdOf pNoAssumeBody)] xFalseEnv))
        [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
        (.terminal xFalseEnv) := by
      refine ReflTransTrace.trans _ hblock ?_
      rw [← heq]
      exact .step _ [] _ _ _ (.step_admin .step_block_done) (.refl _)
    refine .step _ [] _ _ _ (.step_admin .step_stmts_cons) ?_
    refine .step _ [] _ _ _
      (.step_admin (.step_seq_inner (.step_ite_false xFalseEnv_eval_x))) ?_
    refine ReflTransTrace.trans _ (seq_inner_starE (Core.EvalCommandE π)
      (ss := []) hblock_done) ?_
    refine .step _ [] _ _ _ (.step_admin .step_seq_done) ?_
    exact .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)
  have hblock : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.block (.some "") xFalseEnv.store (.stmts pNoAssumeBody xFalseEnv))
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.block (.some "") xFalseEnv.store (.terminal xFalseEnv)) :=
    block_inner_starE hbody
  have heq : ({ xFalseEnv with
      store := projectStore xFalseEnv.store xFalseEnv.store }
      : Imperative.Env Core.Expression) = xFalseEnv := by
    simp [projectStore_self]
  have hblock_done : StepStmtStarE Core.Expression (Core.EvalCommandE π)
      (.block (.some "") xFalseEnv.store (.stmts pNoAssumeBody xFalseEnv))
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, elseMdOf pNoAssumeBody⟩]
      (.terminal xFalseEnv) := by
    refine ReflTransTrace.trans _ hblock ?_
    rw [← heq]
    exact .step _ [] _ _ _ (.step_admin .step_block_done) (.refl _)
  refine .step _ [] _ _ _ (.step_admin .step_stmts_cons) ?_
  refine .step _ [] _ _ _ (.step_admin (.step_seq_inner .step_block)) ?_
  refine ReflTransTrace.trans _ (seq_inner_starE (Core.EvalCommandE π)
    (ss := []) hblock_done) ?_
  refine .step _ [] _ _ _ (.step_admin .step_seq_done) ?_
  exact .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)

/-- Block-level well-formedness for the procedure-block-wrapped assumeless body on
    `xFalseEnv`, via `of_defUseOk` (which re-derives `readWritesDefined`).  The block
    scopes every variable, reserved-prefix fields are vacuous for `testParams`, and
    `defUseOk` holds since every variable is defined. -/
private theorem xFalseEnv_blockWF :
    Core.Logic.BlockInitEnvWF testParams [Stmt.block "" pNoAssumeBody #[]] xFalseEnv :=
  Core.Logic.BlockInitEnvWF.of_defUseOk
    Core.coreFactory_WellFormedSemanticEval
    xFalseEnv_storeWellDefined
    (by intro n hn
        rw [show Block.definedVars (P := Core.Expression) (C := Core.Command)
          [Stmt.block "" pNoAssumeBody #[]] false = [] from by native_decide] at hn
        simp at hn)
    (by intro n hn p hp; simp [testParams] at hp)
    (by intro n hn p hp; simp [testParams] at hp)
    (by
      have hdef : (fun n => (xFalseEnv.store n).isSome) =
          (fun _ : Core.Expression.Ident => true) := by funext n; simp [xFalseEnv]
      show Block.defUseWellFormed (fun n => (xFalseEnv.store n).isSome)
        testParams.declaredFuncs [Stmt.block "" pNoAssumeBody #[]] = true
      rw [hdef]
      native_decide)
    (by intro nm _; rfl)
    (by
      intro ty hty
      rw [show Block.initTypes (P := Core.Expression) (C := Core.Command)
        [Stmt.block "" pNoAssumeBody #[]] = [] from by native_decide] at hty
      simp at hty)

/-- **`pNoAssume` cannot meet its contract.** With no guard on the conditional, a
    well-typed `false`-valued entry runs the `assert false` with no discharging
    assumption, refuting the structured triple its contract names. -/
theorem pNoAssume_contract_refuted :
    ¬ Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pNoAssume" := by
  obtain ⟨model⟩ := Core.factoryInterp_nonempty
  intro h
  obtain ⟨proc, hfind, _htyped, htriple⟩ := h
  obtain rfl : proc = pNoAssumeProc :=
    Option.some.inj (hfind.symm.trans pNoAssumeProc_named)
  rw [pNoAssumeProc_body] at htriple
  have hpre : Core.Logic.Hoare.Procedure.contractPre model pNoAssumeProc xFalseEnv := by
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
      exact ⟨ff0, rfl,
        show Lambda.LExpr.typeCheck [] ff0 = some Lambda.LMonoTy.bool from by native_decide⟩
  have hres := htriple model xFalseEnv xFalseEnv _ hpre xFalseEnv_blockWF
    (.inl (xFalseEnv_blockrun examplePgmAST.findProcByString?))
  have hfalse := hres.1.1 trivial (someValuation model)
    (by intro condition hmem; simp at hmem)
  exact false_not_holds model (someValuation model) xFalseEnv.store Core.Factory
    (elseMdOf pNoAssumeBody) rfl hfalse

/-! ## Example 3 — a `requires x` precondition makes the assumeless contract meetable -/

/-- **`pReq` meets its contract.** Reading `requires x` as the semantic
    `Procedure.preAsPredicate` forces the then branch, so only the quantifier tautology is
    asserted. -/
theorem pReq_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple examplePgmAST testParams "pReq" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    examplePgmAST testParams "pReq" pReqProc pReqBody
    pReqProc_named pReqProc_body (by native_decide) ?_
  intro model ρ₀ ρ' trace hpre hwf hrun
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
      exact ⟨fun _ world _ => forall_holds model world ρ₀.store ρ₀.factory _ hfac, trivial⟩
    ·
      subst htr
      refine ⟨fun _ world _ => ?_, trivial⟩
      exfalso
      have hmem : ("requires_x", pReqCheck) ∈ pReqProc.spec.preconditions.toList := by
        rw [pReqPreconditions_eq]; exact List.mem_cons_self
      have hcheck := hpreP "requires_x" pReqCheck hmem (someValuation model)
      rw [pReqCheck_expr_eq] at hcheck
      exact xFalse_notHolds model ρ₀ (someValuation model) "requires_x" pReqCheck.md
        hwf.toWellFormedSemanticEval hwf.storeWellDefined hfac hc hcheck
  ·
    intro label check hmem _hattr
    rw [show pReqProc.spec.postconditions.toList = [] from by native_decide] at hmem
    simp at hmem

end CoreHoareQuantifiersTest
