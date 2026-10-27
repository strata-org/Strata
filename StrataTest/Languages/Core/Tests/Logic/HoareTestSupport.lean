/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

public import Strata.Languages.Core
public import Strata.Languages.Core.StatementSemantics
public import Strata.Languages.Core.Logic.TraceInterpUsingDenote
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst

/-! # Core Hoare test run inversion support

Key results:
- `someValuation` supplies a valuation for any Core model;
- `factory_push_get?`, `factory_call_mkApp`, and the finite-fuel evaluator
  helpers support tests over program-extended factories;
- `isValue_binary_call_false` discharges the evaluator's fully-applied-call gate;
- `singleton_run_inv` extracts a statement run from a singleton statement-list run;
- `assume_run_inv` characterizes an `assume` run;
- `assert_run_inv` characterizes an `assert` run.
-/

public section

namespace CoreHoareTestSupport

open Imperative

/-- An arbitrary valuation for a model over any Core expression factory. -/
def someValuation {factory : Core.Expression.Factory}
    (model : Lambda.Interp factory) :
    Core.Logic.DenoteValuation model where
  tyVarVal := fun _ => .tcons "bool" []
  freeVarVal := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  offFactoryHolds := fun _ => False

/-- Override `fv` with two integer arguments. -/
def withTwoIntArgs
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int) :
    Lambda.FreeVarVal T tcInterp :=
  Lambda.IdentInterp.withArgs fv [(x, .int), (y, .int)] (.cons a (.cons b .nil))

/-- The first identifier in `withTwoIntArgs` maps to its supplied value. -/
theorem withTwoIntArgs_left
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int) :
    withTwoIntArgs fv x y a b x .int = a := by
  exact Lambda.IdentInterp.withArgs_get tcInterp fv
    [(x, Lambda.LSort.int), (y, Lambda.LSort.int)]
    (.cons a (.cons b .nil)) x Lambda.LSort.int 0 (by rfl) (by rfl) (by intro j hj; omega)

/-- If the identifiers differ, the second identifier in `withTwoIntArgs` maps
    to its supplied value. -/
theorem withTwoIntArgs_right
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    {tcInterp : Lambda.TyConstrInterp}
    (fv : Lambda.FreeVarVal T tcInterp) (x y : T.Identifier) (a b : Int)
    (hne : y ≠ x) : withTwoIntArgs fv x y a b y .int = b := by
  exact Lambda.IdentInterp.withArgs_get tcInterp fv
    [(x, Lambda.LSort.int), (y, Lambda.LSort.int)]
    (.cons a (.cons b .nil)) y Lambda.LSort.int 1 (by rfl) (by rfl) (by
      intro j hj
      have : j = 0 := by omega
      subst j
      simpa using (fun hxy : x = y => hne hxy.symm))

/-- Test-visible wrapper for the module-private `Factory.push_mem_match`:
    looking up `name` after pushing `fn` returns `fn` when the names match;
    otherwise it returns the original factory lookup. -/
theorem factory_push_get?
    {T : Lambda.LExprParams} (factory : Lambda.Factory T) (fn : Lambda.LFunc T)
    (hnew : fn.name.name ∉ factory) (name : String) :
    (factory.push fn hnew)[name]? =
      if name = fn.name.name then some fn else factory[name]? :=
  Lambda.Factory.push_mem_match factory fn hnew name

/-- Test-visible wrapper deriving factory membership from a successful lookup. -/
theorem factory_mem_of_get?
    {T : Lambda.LExprParams} {factory : Lambda.Factory T}
    {name : String} {fn : Lambda.LFunc T}
    (hget : factory[name]? = some fn) : name ∈ factory :=
  Lambda.Factory.getElem?_some_implies_mem hget

/-- Test-visible wrapper identifying membership-indexed lookup after a
    successful optional lookup. -/
theorem factory_get_of_get?
    {T : Lambda.LExprParams} {factory : Lambda.Factory T}
    {name : String} {fn : Lambda.LFunc T}
    (hget : factory[name]? = some fn) :
    factory[name]'(factory_mem_of_get? hget) = fn :=
  Lambda.Factory.getElem?_some_getElem hget

/-- A fully applied function operator resolves to its factory entry. -/
theorem factory_call_mkApp
    {T : Lambda.LExprParams} [Inhabited T.Metadata]
    (factory : Lambda.Factory T) (fn : Lambda.LFunc T)
    (args : List (Lambda.LExpr T.mono))
    (hget : factory[fn.name.name]? = some fn)
    (hlen : args.length = fn.inputs.length)
    (allowPartial : Bool := false) :
    Lambda.Factory.callOfLFunc factory
      (Lambda.LExpr.mkApp default fn.opExpr args) allowPartial =
      some (fn.opExpr, args, fn) := by
  simp only [Lambda.Factory.callOfLFunc, Lambda.LFunc.opExpr,
    Lambda.LFuncDefined.opExpr, Lambda.getLFuncCall_mkApp_op, hget]
  cases allowPartial with
  | false => simp [hlen]
  | true =>
      have hble : ∀ n : Nat, n.ble n = true := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => exact ih
      simp only [↓reduceIte]
      rw [hlen, hble]

/-- A free variable bound to a value evaluates to that value at positive fuel. -/
theorem eval_fvar_of_value
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta] [Inhabited T.IDMeta]
    [Lambda.Traceable Lambda.LExpr.EvalProvenance T.Metadata]
    (fuel : Nat) (factory : Lambda.Factory T) (env : Lambda.Env T)
    (md : T.Metadata) (x : T.Identifier) (ty : Option Lambda.LMonoTy)
    (v : Lambda.LExpr T.mono) (hget : env x = some v)
    (hvalue : Lambda.LExpr.isValue factory v = true) :
    Lambda.LExpr.eval (fuel + 1) factory env (.fvar md x ty) =
      (v, Lambda.LExpr.EvalResult.value true) := by
  have hnot : Lambda.LExpr.isValue factory
      (.fvar md x ty : Lambda.LExpr T.mono) = false := by
    rw [Lambda.LExpr.isValue.eq_def]
    simp only [Lambda.Factory.callOfLFunc, Lambda.getLFuncCall,
      Lambda.getLFuncCall.go]
  rw [Lambda.LExpr.eval.eq_def (TBase := T)]
  simp [hnot, Lambda.callOfLFunc_fvar_none, Lambda.LExpr.evalCore, hget, hvalue]

/-- Test-visible wrapper for the module-private evaluator fact that a value
    evaluates to itself at every fuel. -/
theorem eval_value_identity
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta] [Inhabited T.IDMeta]
    [Lambda.Traceable Lambda.LExpr.EvalProvenance T.Metadata]
    (fuel : Nat) (factory : Lambda.Factory T) (env : Lambda.Env T)
    (e : Lambda.LExpr T.mono) (hvalue : Lambda.LExpr.isValue factory e = true) :
    Lambda.LExpr.eval fuel factory env e =
      (e, Lambda.LExpr.EvalResult.value true) :=
  Lambda.eval_value_identity fuel factory env e hvalue

/-- Test-visible wrapper for closing a finite-fuel value result into an
    `evalFully` result. -/
theorem evalFully_of_value_true
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta] [Inhabited T.IDMeta]
    [Lambda.Traceable Lambda.LExpr.EvalProvenance T.Metadata]
    (factory : Lambda.Factory T) (env : Lambda.Env T) (e : Lambda.LExpr T.mono)
    (fuel : Nat) (v : Lambda.LExpr T.mono)
    (h : Lambda.LExpr.eval fuel factory env e = (v, .value true)) :
    Lambda.LExpr.evalFully factory env e = some v :=
  Lambda.evalFully_of_value_true factory env e fuel v h

/-- A fully applied binary function call is not itself a value when the
    function is not a constructor. -/
theorem isValue_binary_call_false
    {T : Lambda.LExprParams} [DecidableEq T.IDMeta]
    (factory : Lambda.Factory T) (fn : Lambda.LFunc T)
    (m : T.Metadata) (op a b : Lambda.LExpr T.mono)
    (hcall : Lambda.Factory.callOfLFunc factory
      (.app m (.app m op a) b) true = some (op, [a, b], fn))
    (hconstr : fn.isConstr = false) (harity : fn.inputs.length = 2) :
    Lambda.LExpr.isValue factory (.app m (.app m op a) b) = false := by
  rw [Lambda.LExpr.isValue.eq_def]
  split <;> simp_all
  all_goals split <;> simp_all

variable (π : String → Option Core.Procedure)

/-- A completed singleton statement-list run yields the corresponding statement run. -/
theorem singleton_run_inv {s : Core.Statement}
    {ρ ρ' : Imperative.Env Core.Expression}
    {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [s] ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmts [s] ρ) tr (.exiting lbl ρ')) :
    StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt s ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt s ρ) tr (.exiting lbl ρ') := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · rcases stmts_cons_headE (Core.EvalCommandE π) hterm with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · obtain ⟨ρ₁, tr₁, tr₂, htr, hhead, htail⟩ :=
        seq_reaches_terminalE (Core.EvalCommandE π) hseq
      obtain ⟨htr₂, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π) htail
      subst htr₂
      rcases hcfg with hcfg | hcfg
      · simp at hcfg
      · injection hcfg with hρ; subst hρ
        rw [htr, List.append_nil]; exact .inl hhead
  · rcases stmts_cons_headE (Core.EvalCommandE π) hexit with ⟨hcfg, _⟩ | hseq
    · simp at hcfg
    · rcases seq_reaches_exitingE (Core.EvalCommandE π) hseq with
        hhead | ⟨ρ₁, tr₁, tr₂, _, _, htail⟩
      · exact .inr ⟨lbl, hhead⟩
      · obtain ⟨_, hcfg⟩ := stmts_nil_runE (Core.EvalCommandE π) htail
        rcases hcfg with hcfg | hcfg <;> simp at hcfg

/-- An `assume` statement emits its captured condition and preserves its environment. -/
theorem assume_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assume l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assume ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
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
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assume =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

/-- An `assert` statement emits its captured condition and preserves its environment. -/
theorem assert_run_inv {l : String} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {ρ ρ' : Imperative.Env Core.Expression} {tr : List (Event Core.Expression)}
    (h : StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.terminal ρ') ∨
      ∃ lbl, StepStmtStarE Core.Expression (Core.EvalCommandE π)
        (.stmt (Core.Statement.assert l e md) ρ) tr (.exiting lbl ρ')) :
    tr = [Event.assert ⟨ρ.factory, ρ.store, l, e, md⟩] ∧ ρ' = ρ := by
  rcases h with hterm | ⟨lbl, hexit⟩
  · cases hterm with
    | step _ emitted _ restTr _ hstep hrest =>
      cases hstep with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assert =>
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
        cases hcmd with
        | cmd_sem hbase =>
          cases hbase with
          | eval_assert =>
          obtain ⟨hcfg, _⟩ := stepStmtStarE_from_terminal hrest
          simp at hcfg
      | step_admin hadmin => cases hadmin with | step_cmd hf => exact hf.elim

end CoreHoareTestSupport

end -- public section
