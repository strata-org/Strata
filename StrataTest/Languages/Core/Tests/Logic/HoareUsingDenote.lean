/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.Logic.Hoare
import Strata.Languages.Core.Logic.ContractToHoareTriple
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

/-! # Core Hoare `TripleWith` over the denotational interpretation, from `StepStmtStarE`

Three small Core procedures are declared together in surface syntax, translated,
and annotated by the type-inference phase used in Core verification. Their inferred
bodies instantiate `Core.Logic.Hoare.TripleWith` under
`Core.Logic.DenoteBasedInterp model`, proved or refuted directly from the event
small-step semantics `StepStmtStarE`, without appealing to a Hoare rule.
-/

namespace CoreHoareUsingDenoteTest

open Imperative
open Core (Expression Command Statement Statements)

/-! ## Typed Core syntax fixtures

The declarations below parse one Core source program, run Core verification's
type-inference phase, and project the inferred procedures and normalized bodies
used by the operational and denotational proofs. -/

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

/-- Erase source metadata from an inferred Core command without changing its
identifiers, types, expressions, or call arguments. -/
private def eraseCommandMetadata : Core.Command → Core.Command
  | .cmd (.init name ty value _) => .cmd (.init name ty value #[])
  | .cmd (.set name value _) => .cmd (.set name value #[])
  | .cmd (.assert label condition _) => .cmd (.assert label condition #[])
  | .cmd (.assume label condition _) => .cmd (.assume label condition #[])
  | .cmd (.cover label condition _) => .cmd (.cover label condition #[])
  | .call procName args _ => .call procName args #[]

/-- Project a structured inferred body and normalize its source metadata. -/
private def structuredBody (proc : Core.Procedure) : Core.Statements :=
  match proc.body with
  | .structured body =>
      Imperative.Block.mapExpr id eraseCommandMetadata
        (Imperative.Block.stripMetaData body)
  | _ => []

/-- The inferred body of `pAssume`. -/
private def pAssumeBody : Core.Statements := structuredBody pAssumeProc

/-- The inferred body of `pNoAssume`. -/
private def pNoAssumeBody : Core.Statements := structuredBody pNoAssumeProc

/-- The inferred body of `pReq`. -/
private def pReqBody : Core.Statements := structuredBody pReqProc

/-- Procedure lookup in the inferred program. -/
private def procEnv : String → Option Core.Procedure :=
  examplePgmAST.findProcByString?

/-- The expected inferred identifier and expression shapes used by the
operational and denotational proofs. -/
private abbrev xIdent : Core.Expression.Ident := ⟨"x", ()⟩
private abbrev xExpr : Core.Expression.Expr := .fvar () xIdent (some Lambda.LMonoTy.bool)
private abbrev ff0 : Core.Expression.Expr :=
  Lambda.LExpr.const () (Lambda.LConst.boolConst false)
private abbrev forallExpr : Core.Expression.Expr :=
  .quant () .all "y" (some Lambda.LMonoTy.bool) (.bvar () 0)
    (.eq () (.bvar () 0) (.bvar () 0))
private abbrev assumeXStmt : Core.Statement := Core.Statement.assume "a" xExpr #[]
private abbrev assertTrueStmt : Core.Statement := Core.Statement.assert "t" forallExpr #[]
private abbrev assertFalseStmt : Core.Statement := Core.Statement.assert "f" ff0 #[]
private abbrev iteStmt : Core.Statement :=
  Stmt.ite (.det xExpr) [assertTrueStmt] [assertFalseStmt] #[]

/-- The inferred `pAssume` body has the expected assume/conditional shape. -/
private theorem pAssumeBody_eq : pAssumeBody = [assumeXStmt, iteStmt] := by
  native_decide

/-- The inferred `pNoAssume` body is the expected conditional. -/
private theorem pNoAssumeBody_eq : pNoAssumeBody = [iteStmt] := by
  native_decide

/-- The inferred `pReq` body is the expected conditional. -/
private theorem pReqBody_eq : pReqBody = [iteStmt] := by
  native_decide

/-- The inferred requires check, including its source metadata. -/
private def pReqCheck : Core.Procedure.Check :=
  match pReqProc.spec.preconditions.toList with
  | [("requires_x", check)] => check
  | _ => default

/-- The inferred procedure environment contains `pAssume`. -/
private theorem pAssumeProc_named : procEnv "pAssume" = some pAssumeProc := by
  native_decide

/-- The inferred procedure environment contains `pNoAssume`. -/
private theorem pNoAssumeProc_named : procEnv "pNoAssume" = some pNoAssumeProc := by
  native_decide

/-- The inferred procedure environment contains `pReq`. -/
private theorem pReqProc_named : procEnv "pReq" = some pReqProc := by
  native_decide

/-- `pReq` has exactly the projected requires check. -/
private theorem pReqPreconditions_eq :
    pReqProc.spec.preconditions.toList = [("requires_x", pReqCheck)] := by
  native_decide

/-- Type inference annotates the requires expression as Boolean `x`. -/
private theorem pReqCheck_expr_eq : pReqCheck.expr = xExpr := by
  native_decide


/-- `∀ y : bool, y = y` is well-typed at `bool`. -/
private theorem forallExpr_ty : Lambda.LExpr.HasTypeA [] forallExpr .bool :=
  Lambda.LExpr.typeCheck_to_HasTypeA (by rfl)

/-! ## Operational run inversions over the event semantics -/

section
variable (π : String → Option Core.Procedure)
variable (φ : Core.Expression.Factory → PureFunc Core.Expression → Core.Expression.Factory)

/-- Invert a singleton statement-list run: a finished traced run of `.stmts [s] ρ` is a
    finished traced run of `.stmt s ρ` with the same trace. -/
private theorem singleton_run_inv {s : Core.Statement} {ρ ρ' : Imperative.Env Core.Expression}
    {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmts [s] ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmts [s] ρ) tr (.exiting lbl ρ')) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt s ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt s ρ) tr (.exiting lbl ρ') := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · rcases stmts_cons_headE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) hterm with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · obtain ⟨ρ₁, tr₁, tr₂, htr, hhead, htail⟩ :=
        seq_reaches_terminalE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) hseq
      obtain ⟨htr₂, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) htail
      subst htr₂
      rcases hcfg with hcfg | hcfg
      · simp at hcfg
      · injection hcfg with hρ; subst hρ
        rw [htr, List.append_nil]; exact .inl hhead
  · rcases stmts_cons_headE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) hexit with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · rcases seq_reaches_exitingE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) hseq with
        hhead | ⟨ρ₁, tr₁, tr₂, _, _, htail⟩
      · exact .inr ⟨lbl, hhead⟩
      · obtain ⟨_, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ) htail
        rcases hcfg with hcfg | hcfg <;> simp at hcfg

/-- An `assert l e md` statement's traced run emits exactly the captured assertion. -/
private theorem assert_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assert ⟨ρ.factory, ρ.store, l, e, md⟩] := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        simp only [Core.EvalCommandE] at hcmd
        cases hcmd with
        | eval_assert =>
          obtain ⟨_, hnil⟩ := stepStmtStarE_from_terminal hrest
          subst hnil; rfl
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        simp only [Core.EvalCommandE] at hcmd
        cases hcmd with
        | eval_assert =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

/-- An `assume l e md` statement's traced run emits the captured assumption and leaves the
    environment unchanged. -/
private theorem assume_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assume ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        simp only [Core.EvalCommandE] at hcmd
        cases hcmd with
        | eval_assume =>
          obtain ⟨hcfg, hnil⟩ := stepStmtStarE_from_terminal hrest
          subst hnil
          injection hcfg with hρ
          subst hρ
          exact ⟨by simp, rfl⟩
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        simp only [Core.EvalCommandE] at hcmd
        cases hcmd with
        | eval_assume =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

/-- Invert a finished traced run of `iteStmt`: the guard `x` evaluated to `tt` (then the
    then-branch `[assert (∀ y, y = y)]` ran) or to `ff` (then the else-branch
    `[assert false]` ran).  Either branch is a single assert, so the trace is the
    corresponding singleton assert event. -/
private theorem ite_run_inv {ρ ρ' : Imperative.Env Core.Expression}
    {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt iteStmt ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
        (.stmt iteStmt ρ) tr (.exiting lbl ρ')) :
    (Core.Expression.eval ρ.factory ρ.store xExpr = some HasBool.tt ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "t", forallExpr, #[]⟩]) ∨
    (Core.Expression.eval ρ.factory ρ.store xExpr = some HasBool.ff ∧
      tr = [Event.assert ⟨ρ.factory, ρ.store, "f", ff0, #[]⟩]) := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc _ =>
          obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inl hrest)
          have htr := assert_run_inv π φ (l := "t") (e := forallExpr) (md := #[]) (ρ := ρ)
            (ρ' := ρi) (singleton_run_inv π φ hin)
          exact .inl ⟨hc, by simpa using htr⟩
        | step_ite_false hc _ =>
          obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inl hrest)
          have htr := assert_run_inv π φ (l := "f") (e := ff0) (md := #[]) (ρ := ρ)
            (ρ' := ρi) (singleton_run_inv π φ hin)
          exact .inr ⟨hc, by simpa using htr⟩
  · cases hexit with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_admin hadmin => cases hadmin with
        | step_ite_true hc _ =>
          obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inr ⟨lbl, hrest⟩)
          have htr := assert_run_inv π φ (l := "t") (e := forallExpr) (md := #[]) (ρ := ρ)
            (ρ' := ρi) (singleton_run_inv π φ hin)
          exact .inl ⟨hc, by simpa using htr⟩
        | step_ite_false hc _ =>
          obtain ⟨ρi, hin, _⟩ := block_reaches_doneE (.inr ⟨lbl, hrest⟩)
          have htr := assert_run_inv π φ (l := "f") (e := ff0) (md := #[]) (ρ := ρ)
            (ρ' := ρi) (singleton_run_inv π φ hin)
          exact .inr ⟨hc, by simpa using htr⟩

end

/-! ## Denotational facts about the two captured assertions -/

section
variable {F : Core.Expression.Factory} (model : Lambda.Interp F)

/-- `∀ y : bool, y = y` denotes `true` in every world (independent of model and
    valuation). -/
private theorem forall_holds (world : Core.Logic.DenoteValuation model)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory) (hf : f = F) :
    (Core.Logic.DenoteBasedInterp model).holds world ⟨f, σ, "t", forallExpr, #[]⟩ := by
  refine .inl ⟨hf, ?_⟩
  have hcap : Core.Logic.capturedExpr
      (⟨f, σ, "t", forallExpr, (#[] : Imperative.MetaData Core.Expression)⟩ :
        Imperative.EventArg Core.Expression) = forallExpr := by
    apply Lambda.LExpr.substFvarsFromEnv_closed_identity; rfl
  rw [hcap]
  refine ⟨forallExpr_ty, ?_⟩
  have hbody : Lambda.LExpr.HasTypeA [Lambda.LMonoTy.bool]
      ((.eq () (.bvar () 0) (.bvar () 0) : Core.Expression.Expr)) .bool :=
    .eq (.bvar (by rfl)) (.bvar (by rfl))
  apply Lambda.denote_quant_all_true .nil hbody forallExpr_ty
  intro x
  exact Lambda.denote_eq_true (.cons x .nil) (.bvar (by rfl)) (.bvar (by rfl)) hbody rfl

/-- The `false` literal captured under the ambient factory never holds: its
closed captured form denotes `false`. -/
private theorem false_not_holds (world : Core.Logic.DenoteValuation model)
    (σ : SemanticStore Core.Expression) (f : Core.Expression.Factory) (hf : f = F) :
    ¬ (Core.Logic.DenoteBasedInterp model).holds world ⟨f, σ, "f", ff0, #[]⟩ := by
  rintro (⟨_, hex⟩ | ⟨hne, _⟩)
  · have hcap : Core.Logic.capturedExpr
        (⟨f, σ, "f", ff0, (#[] : Imperative.MetaData Core.Expression)⟩ :
          Imperative.EventArg Core.Expression) = ff0 := rfl
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    simp [ff0, Lambda.LMonoTy.bool, Lambda.denote_boolConst] at hd
  · exact hne hf

end

/-! ## Example 1 — `{True} pAssume {True}` is valid -/

/-- **Valid.**  `{ρ.factory = Core.Factory}
    (assume x; if x then assert (∀ y, y = y) else assert false) {True}` under the
    denotational interpretation, proved directly from `StepStmtStarE`. -/
theorem pAssume_triple_valid
    (model : Lambda.Interp Core.Factory)
    (π : String → Option Core.Procedure)
    (φ : Core.Expression.Factory → PureFunc Core.Expression → Core.Expression.Factory)
    (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.TripleWith π φ (Core.Logic.DenoteBasedInterp model) params
      (fun ρ => ρ.factory = Core.Factory) pAssumeBody (fun _ => True) := by
  intro ρ₀ ρ' trace hfac hwf hrun
  rw [pAssumeBody_eq] at hrun
  refine ⟨?_, fun _ => trivial⟩
  rcases stmts_append_doneE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
    [assumeXStmt] [iteStmt] ρ₀ ρ' hrun with
    ⟨lbl, hexit₁⟩ | ⟨ρ₁, tr₁, tr₂, htr, hterm₁, hfin₂⟩
  · exact absurd hexit₁ (stmts_exitsCoveredByBlocks_noEscapeE (Core.EvalCommandE π φ)
      (Core.EvalPureFunc φ) [assumeXStmt]
      (by simp [Block.exitsCoveredByBlocks, Stmt.exitsCoveredByBlocks]) ρ₀ lbl ρ')
  · -- the prefix is a single `assume x`, so `tr₁ = [assume x]` and `ρ₁ = ρ₀`
    obtain ⟨htr₁, hρ₁⟩ := assume_run_inv π φ (l := "a") (e := xExpr) (md := #[]) (ρ := ρ₀)
      (ρ' := ρ₁) (singleton_run_inv π φ (.inl hterm₁))
    subst ρ₁; subst htr; subst htr₁
    rcases ite_run_inv π φ (ρ := ρ₀) (ρ' := ρ') (singleton_run_inv π φ hfin₂) with
      ⟨_hc, htr₂⟩ | ⟨hc, htr₂⟩
    · -- then branch: `∀ y, y = y` is discharged by the model tautology
      subst htr₂
      refine ⟨fun _ world hassum => ?_, trivial⟩
      exact forall_holds model world ρ₀.store ρ₀.factory hfac
    · -- else branch: the captured `assume x` is false, so the assertion is vacuous
      subst htr₂
      refine ⟨fun _ world hassum => ?_, trivial⟩
      exfalso
      rcases hassum ⟨ρ₀.factory, ρ₀.store, "a", xExpr, #[]⟩ (by simp) with
        ⟨_hfac, hex⟩ | ⟨hne, _⟩
      · have hvar := hwf.toWellFormedSemanticEval.var xExpr xIdent ρ₀.store
          hwf.storeWellDefined rfl
        have hstore : ρ₀.store xIdent = some ff0 := by rw [← hvar]; exact hc
        have hcap : Core.Logic.capturedExpr
            (⟨ρ₀.factory, ρ₀.store, "a", xExpr, (#[] : Imperative.MetaData Core.Expression)⟩ :
              Imperative.EventArg Core.Expression) = ff0 := by
          simp only [Core.Logic.capturedExpr, xExpr, Lambda.LExpr.substFvarsFromEnv,
            Lambda.Env.mk, hstore]
        rw [hcap] at hex
        obtain ⟨_hty, hd⟩ := hex
        simp [ff0, Lambda.LMonoTy.bool, Lambda.denote_boolConst] at hd
      · exact hne hfac

/-! ## Example 2 — dropping the `assume` makes the triple invalid -/

/-- Gate parameters: no reserved prefixes, every operator counts as declared. -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-- A total `false`-valued environment over `Core.Factory`. -/
private def xFalseEnv : Imperative.Env Core.Expression :=
  { store := fun _ => some ff0, factory := Core.Factory, hasFailure := false }

/-- `xFalseEnv` holds only values (every binding is the `false` literal). -/
private theorem xFalseEnv_storeWellDefined :
    Imperative.WellFormedStore xFalseEnv.store xFalseEnv.factory := by
  intro n v hn
  simp only [xFalseEnv] at hn
  injection hn with hv; subst hv
  show Lambda.LExpr.isCanonicalValue _ ff0 = true
  exact Lambda.isCanonicalValue_const_true _ _ _

/-- Reading `x` from `xFalseEnv` yields `false`. -/
private theorem xFalseEnv_eval_x :
    Core.Expression.eval xFalseEnv.factory xFalseEnv.store xExpr = some HasBool.ff := by
  have hvar := Core.coreFactory_WellFormedSemanticEval.var xExpr xIdent xFalseEnv.store
    xFalseEnv_storeWellDefined rfl
  exact hvar.trans rfl

/-- `Core.Factory` well-formedness for boolean evaluation. -/
private theorem coreFactory_wfBool :
    Imperative.WellFormedSemanticEvalBool (P := Core.Expression) Core.Factory :=
  Core.coreFactory_WellFormedSemanticEval.bool

/-- The completed event run of the assumeless body on `xFalseEnv`: it takes the else
    branch and emits exactly the `assert false` event. -/
private theorem xFalseEnv_run (π : String → Option Core.Procedure)
    (φ : Core.Expression.Factory → PureFunc Core.Expression → Core.Expression.Factory) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
      (.stmts pNoAssumeBody xFalseEnv)
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, #[]⟩]
      (.terminal xFalseEnv) := by
  rw [pNoAssumeBody_eq]
  -- inner: `[assert false]` emits the assert event and stays put
  have hassert : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
      (.stmts [assertFalseStmt] xFalseEnv)
      [Event.assert ⟨xFalseEnv.factory, xFalseEnv.store, "f", ff0, #[]⟩]
      (.terminal xFalseEnv) := by
    refine .step _ [] _ _ _ (.step_admin .step_stmts_cons) ?_
    refine .step _ [Event.assert ⟨xFalseEnv.factory, xFalseEnv.store, "f", ff0, #[]⟩] _ _ _
      (.step_seq_inner (.step_cmd Imperative.EvalCmdE.eval_assert)) ?_
    refine .step _ [] _ _ _ (.step_admin .step_seq_done) ?_
    exact .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)
  -- lift through the anonymous block wrapper and take `step_block_done`
  have hblock := block_inner_starE (EvalCmd := Core.EvalCommandE π φ)
    (extendFactory := Core.EvalPureFunc φ) (label := .none)
    (σ_parent := xFalseEnv.store) (f_parent := xFalseEnv.factory) hassert
  have heq : ({ xFalseEnv with
      store := projectStore xFalseEnv.store xFalseEnv.store, factory := xFalseEnv.factory }
      : Imperative.Env Core.Expression) = xFalseEnv := by
    simp [projectStore_self]
  have hblock_done : StepStmtStarE Core.Expression (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
      (.block .none xFalseEnv.store xFalseEnv.factory (.stmts [assertFalseStmt] xFalseEnv))
      [Event.assert ⟨Core.Factory, xFalseEnv.store, "f", ff0, #[]⟩]
      (.terminal xFalseEnv) := by
    refine ReflTransTrace.trans _ hblock ?_
    rw [← heq]
    exact .step _ [] _ _ _ (.step_admin .step_block_done) (.refl _)
  refine .step _ [] _ _ _ (.step_admin .step_stmts_cons) ?_
  refine .step _ [] _ _ _
    (.step_admin (.step_seq_inner (.step_ite_false xFalseEnv_eval_x coreFactory_wfBool))) ?_
  refine ReflTransTrace.trans _ (seq_inner_starE (Core.EvalCommandE π φ) (Core.EvalPureFunc φ)
    (ss := []) hblock_done) ?_
  refine .step _ [] _ _ _ (.step_admin .step_seq_done) ?_
  exact .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)

/-- Block-level well-formedness for the assumeless body on `xFalseEnv`, via `of_defUseOk`
    (which re-derives `readWritesDefined`).  Reserved-prefix fields are vacuous for
    `testParams`, and `defUseOk` holds since every variable is defined. -/
private theorem xFalseEnv_blockWF :
    Core.Logic.BlockInitEnvWF testParams pNoAssumeBody xFalseEnv :=
  Core.Logic.BlockInitEnvWF.of_defUseOk
    Core.coreFactory_WellFormedSemanticEval
    xFalseEnv_storeWellDefined
    (by intro n hn
        have hd : Block.definedVars pNoAssumeBody false = [] := by
          rw [pNoAssumeBody_eq]
          simp [iteStmt, assertTrueStmt, assertFalseStmt, Block.definedVars,
            Stmt.definedVars, Command.definedVars, Imperative.Cmd.definedVars,
            Imperative.HasVarsImp.definedVars]
        rw [hd] at hn; simp at hn)
    (by intro n hn p hp; simp [testParams] at hp)
    (by intro n hn p hp; simp [testParams] at hp)
    (by intro n hn p hp; simp [testParams] at hp)
    (by
      have hdef : (fun n => (xFalseEnv.store n).isSome) =
          (fun _ : Core.Expression.Ident => true) := by funext n; simp [xFalseEnv]
      show Block.defUseWellFormed (fun n => (xFalseEnv.store n).isSome) (fun _ => true)
        pNoAssumeBody = true
      rw [hdef, pNoAssumeBody_eq]
      simp [iteStmt, assertTrueStmt, assertFalseStmt, Block.defUseWellFormed,
        Stmt.defUseWellFormed, Command.definedVars, Imperative.HasVarsImp.definedVars,
        Imperative.Cmd.definedVars])
    (by intro s hs; simp [testParams])

/-- Arbitrary valuation in a model over `Core.Factory`. -/
private def someValuation (model : Lambda.Interp Core.Factory) :
    Core.Logic.DenoteValuation model where
  tyVarVal := fun _ => .tcons "bool" []
  freeVarVal := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  offFactoryHolds := fun _ => False

/-- **Invalid.**  Dropping the `assume x`, `{True} (if x then … else assert false) {True}`
    is *false*: run from `x = false` the `assert false` is emitted with no discharging
    assumption, so `AssertionsValid` fails. -/
theorem pNoAssume_triple_invalid
    (model : Lambda.Interp Core.Factory)
    (π : String → Option Core.Procedure)
    (φ : Core.Expression.Factory → PureFunc Core.Expression → Core.Expression.Factory) :
    ¬ Core.Logic.Hoare.TripleWith π φ (Core.Logic.DenoteBasedInterp model) testParams
      (fun _ => True) pNoAssumeBody (fun _ => True) := by
  intro htriple
  have hres := htriple xFalseEnv xFalseEnv _ trivial xFalseEnv_blockWF
    (.inl (xFalseEnv_run π φ))
  have hfalse := hres.1.1 trivial (someValuation model)
    (by intro condition hmem; simp at hmem)
  exact false_not_holds model (someValuation model) xFalseEnv.store Core.Factory rfl hfalse

/-! ## Example 3 — a `requires x` precondition makes the assumeless triple valid -/

/-- **Valid.**  Reading `requires x` through `Procedure.preAsPredicate` forces the
    then branch of `(if x then assert (∀ y, y = y) else assert false)`, so only the
    tautology is emitted and the triple holds. -/
theorem pReq_triple_valid
    (model : Lambda.Interp Core.Factory)
    (π : String → Option Core.Procedure)
    (φ : Core.Expression.Factory → PureFunc Core.Expression → Core.Expression.Factory)
    (params : Core.Logic.InitEnvWFParams) :
    Core.Logic.Hoare.TripleWith π φ (Core.Logic.DenoteBasedInterp model) params
      (fun ρ => Core.Logic.Hoare.Procedure.preAsPredicate pReqProc ρ ∧
        ρ.factory = Core.Factory)
      pReqBody (fun _ => True) := by
  intro ρ₀ ρ' trace hpre hwf hrun
  rw [pReqBody_eq] at hrun
  refine ⟨?_, fun _ => trivial⟩
  obtain ⟨hrequires, hfac⟩ := hpre
  have hreqmem :
      ("requires_x", pReqCheck) ∈ pReqProc.spec.preconditions.toList := by
    rw [pReqPreconditions_eq]
    exact List.mem_cons_self
  have hxtt : Core.Expression.eval ρ₀.factory ρ₀.store xExpr = some HasBool.tt := by
    have h := hrequires "requires_x" pReqCheck hreqmem
    rw [pReqCheck_expr_eq] at h
    exact h
  rcases ite_run_inv π φ (ρ := ρ₀) (ρ' := ρ') (singleton_run_inv π φ hrun) with
    ⟨_hc, htr⟩ | ⟨hc, _⟩
  · subst htr
    refine ⟨fun _ world _ => ?_, trivial⟩
    exact forall_holds model world ρ₀.store ρ₀.factory hfac
  · exact absurd (hxtt.symm.trans hc)
      (by intro heq; exact Imperative.HasBool.tt_is_not_ff (Option.some.inj heq))

end CoreHoareUsingDenoteTest
