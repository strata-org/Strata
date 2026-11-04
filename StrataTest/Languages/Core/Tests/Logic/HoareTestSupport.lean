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
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteSubst

/-! # Core Hoare test run inversion support

Key results:
- `boolFactory` builds a runtime factory from a model;
- `someValuation` supplies a world over any Core factory;
- `factory_push_get?`, `factory_mem_of_get?`, and `factory_get_of_get?`
  support tests over program-extended factories;
- `singleton_run_inv` extracts a statement run from a singleton statement-list run;
- `assume_run_inv` characterizes an `assume` run;
- `assert_run_inv` characterizes an `assert` run.
-/

public section

namespace CoreHoareTestSupport

open Imperative

/-- The runtime factory of the model `model`, reading every residual type variable at
`bool`. -/
abbrev boolFactory {F : Lambda.Factory Core.CoreLParams} (model : Lambda.Interp F) :
    Core.Expression.Factory :=
  { factory := F, model := model, tyVarVal := fun _ => .bool }

/-- A world over any Core expression factory: off-factory conditions never hold. -/
def someValuation (factory : Lambda.Factory Core.CoreLParams) :
    Core.Logic.DenoteValuation factory where
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

end CoreHoareTestSupport

end -- public section
