/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ConstantPropagation
import all Strata.Transform.ConstantPropagation
public import Strata.Languages.Core.StatementSemantics
import all Strata.Languages.Core.StatementSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Util.Map
public import Strata.DL.Imperative.StmtSemanticsProps

/-! # Constant Propagation Correctness

Constant propagation replaces variable references with their known constant
values. It is semantics-preserving because we only propagate ground values
(no free variables), substituting such a value is equivalent to evaluating the
original program where the variable holds it, and propagated values are
conservatively killed at control-flow joins (loops reset the environment).

## Scope

This file proves the transform correct for **straight-line commands**, stated
against the small-step `Core.EvalStatements` relation (`StepStmtStar` to a
terminal) — consistent with the other transform-correctness proofs such as
`DetToKleeneCorrect`. Concretely it establishes:

- the substitution bridge `substFvars_eval_eq` (substituting a sound environment
  preserves evaluation; ground values cannot capture);
- the `ConstEnvSound` / `ConstEnvGround` invariant and its preservation across
  each per-command store update;
- the capstone `propagateConstants_sim_cmds`, with
  `propagateConstants_sim_cmds_entry` discharging the invariant for the empty
  initial environment (so the entry point is unconditional).

**Not yet proved:** the control-flow cases (`ite`, `loop`, `block`, `call`).
They reuse the same invariant and bridge — `ite` is sound at the join because
`intersectEnv` keeps only the bindings both branches agree on, and `loop`/`call`
reset the environment — so what remains is the per-construct induction. The
intended vehicle is the `Overapproximates` machinery in
`Strata/Transform/Specification.lean` (cf. strata-org/Strata#1325); it is
tracked as a follow-up rather than carried in this change.

The section comments below mark the file layout, and each theorem carries its
own docstring.
-/

namespace Strata

open Core Imperative Lambda

/-- The propagation environment `env` is *sound* with respect to a store `σ`
under the Core evaluator `Core.Expression.eval`: every binding `x ↦ v` records a value the store agrees
with, i.e. reading `x` from `σ` yields the same value the evaluator assigns to `v`.
(Since propagated `v` are ground, `Core.Expression.eval f σ v` does not depend on `σ`.) -/
def ConstEnvSound (f : Core.Expression.Factory)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (σ : SemanticStore Core.Expression) : Prop :=
  ∀ name to, Map.find? env name = some to → σ name = Core.Expression.eval f σ to

/-- **Substitution bridge** (core worker, over `substFvarsAux`). Substituting a
sound environment's bindings preserves evaluation. Proved by structural
induction on the expression, using `WellFormedSemanticEvalVar` at the variable
leaf and the `WellFormedCoreEvalCong` congruences at the compound nodes. -/
theorem substFvarsAux_eval_eq
    (f : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar f)
    (hcong : Core.WellFormedCoreEvalCong f)
    (hstore : WellFormedStore σ f)
    (hsound : ConstEnvSound f env σ) :
    ∀ e, Core.Expression.eval f σ (Lambda.LExpr.substFvars.substFvarsAux e env) = Core.Expression.eval f σ e := by
  intro e
  induction e with
  | const _ _ => simp only [Lambda.LExpr.substFvars.substFvarsAux]
  | bvar _ _ => simp only [Lambda.LExpr.substFvars.substFvarsAux]
  | op _ _ _ => simp only [Lambda.LExpr.substFvars.substFvarsAux]
  | fvar m name ty =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    cases h : Map.find? env name with
    | none => rfl
    | some to =>
      have hv : Core.Expression.eval f σ (Lambda.LExpr.fvar m name ty) = σ name :=
        hvar (Lambda.LExpr.fvar m name ty) name σ hstore rfl
      exact (hv.trans (hsound name to h)).symm
  | abs m n ty b ihb =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    exact hcong.abscongr σ σ _ b ihb m n ty
  | quant m qk name ty tr e ihtr ihe =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    exact hcong.quantcongr σ σ m qk name ty _ tr _ e ihtr ihe
  | app m f a ihf iha =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    exact hcong.appcongr σ σ m _ f _ a ihf iha
  | ite m c t e ihc iht ihe =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    exact hcong.itecongr σ σ m _ t _ e _ c iht ihe ihc
  | eq m e1 e2 ih1 ih2 =>
    simp only [Lambda.LExpr.substFvars.substFvarsAux]
    exact hcong.eqcongr σ σ m _ e1 _ e2 ih1 ih2

/-- **Substitution bridge**. For a sound environment, `substFvars` preserves
evaluation: `Core.Expression.eval f σ (substFvars e env) = Core.Expression.eval f σ e`. This is the key lemma
the constant-propagation simulation rests on. -/
theorem substFvars_eval_eq
    (f : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar f)
    (hcong : Core.WellFormedCoreEvalCong f)
    (hstore : WellFormedStore σ f)
    (hsound : ConstEnvSound f env σ)
    (e : Lambda.LExpr Core.CoreLParams.mono) :
    Core.Expression.eval f σ (Lambda.LExpr.substFvars e env) = Core.Expression.eval f σ e := by
  unfold Lambda.LExpr.substFvars
  split
  · rfl
  · exact substFvarsAux_eval_eq f σ env hvar hcong hstore hsound e

/-- The small-ground-value predicate yields expressions with no free variables.
This is the concrete "propagated ground values are closed" fact the correctness
proofs rely on. It is applied directly wherever a propagated value's freedom
from free variables is needed — previously this obligation was carried as an
abstract `hgnd` hypothesis over a configurable `isGround` predicate; now that
`propagateConstants` uses `defaultSmallGroundValue` directly, this theorem
discharges it outright. -/
theorem ground_no_fvars (e : Lambda.LExpr Core.CoreLParams.mono)
    (hg : defaultSmallGroundValue e = true) :
    Imperative.HasFvars.getFvars (P := Core.Expression) e = [] := by
  unfold defaultSmallGroundValue at hg
  split at hg <;> simp_all [Imperative.HasFvars.getFvars, Lambda.LExpr.LExpr.getVars]

/-- Evaluating an expression with no free variables is independent of the store
(so `WellFormedSemanticEvalExprCongr` applies). A propagated value is closed —
`ground_no_fvars` guarantees `getFvars = []` — which is what
makes an inserted binding store-independent. -/
theorem ground_eval_store_indep
    (f : Core.Expression.Factory)
    (hexpr : WellFormedSemanticEvalExprCongr f)
    (σ σ' : SemanticStore Core.Expression)
    (e : Lambda.LExpr Core.CoreLParams.mono)
    (hnofv : Imperative.HasFvars.getFvars (P := Core.Expression) e = []) :
    Core.Expression.eval f σ e = Core.Expression.eval f σ' e := by
  apply hexpr
  intro x hx
  rw [hnofv] at hx
  simp at hx

/-! ## Command-level substitution invariance

Substituting a sound environment into a command's expressions does not change
its big-step behaviour (`EvalCmd`). These compose the substitution bridge at the
command steps of the statement-level simulation. -/

theorem evalCmd_assert_subst
    (fac : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar fac) (hcong : Core.WellFormedCoreEvalCong fac)
    (hstore : WellFormedStore σ fac) (hsound : ConstEnvSound fac env σ) {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression fac σ (.assert l e md) σ' f) :
    Imperative.EvalCmd Core.Expression fac σ (.assert l (Lambda.LExpr.substFvars e env) md) σ' f := by
  have hb := substFvars_eval_eq fac σ env hvar hcong hstore hsound e
  cases h with
  | eval_assert_pass he hbool => exact .eval_assert_pass (hb.trans he) hbool
  | eval_assert_fail he hbool => exact .eval_assert_fail (hb.trans he) hbool

theorem evalCmd_assume_subst
    (fac : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar fac) (hcong : Core.WellFormedCoreEvalCong fac)
    (hstore : WellFormedStore σ fac) (hsound : ConstEnvSound fac env σ) {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression fac σ (.assume l e md) σ' f) :
    Imperative.EvalCmd Core.Expression fac σ (.assume l (Lambda.LExpr.substFvars e env) md) σ' f := by
  have hb := substFvars_eval_eq fac σ env hvar hcong hstore hsound e
  cases h with
  | eval_assume he hbool => exact .eval_assume (hb.trans he) hbool

theorem evalCmd_cover_subst
    (fac : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression fac σ (.cover l e md) σ' f) :
    Imperative.EvalCmd Core.Expression fac σ (.cover l (Lambda.LExpr.substFvars e env) md) σ' f := by
  cases h with
  | eval_cover hbool => exact .eval_cover hbool

theorem evalCmd_init_det_subst
    (fac : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar fac) (hcong : Core.WellFormedCoreEvalCong fac)
    (hstore : WellFormedStore σ fac) (hsound : ConstEnvSound fac env σ) {x ty e md σ' f}
    (h : Imperative.EvalCmd Core.Expression fac σ (.init x ty (.det e) md) σ' f) :
    Imperative.EvalCmd Core.Expression fac σ
      (.init x ty (.det (Lambda.LExpr.substFvars e env)) md) σ' f := by
  have hb := substFvars_eval_eq fac σ env hvar hcong hstore hsound e
  cases h with
  | eval_init he hinit hwf => exact .eval_init (hb.trans he) hinit hwf

theorem evalCmd_set_det_subst
    (fac : Core.Expression.Factory) (σ : SemanticStore Core.Expression)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (hvar : WellFormedSemanticEvalVar fac) (hcong : Core.WellFormedCoreEvalCong fac)
    (hstore : WellFormedStore σ fac) (hsound : ConstEnvSound fac env σ) {x e md σ' f}
    (h : Imperative.EvalCmd Core.Expression fac σ (.set x (.det e) md) σ' f) :
    Imperative.EvalCmd Core.Expression fac σ
      (.set x (.det (Lambda.LExpr.substFvars e env)) md) σ' f := by
  have hb := substFvars_eval_eq fac σ env hvar hcong hstore hsound e
  cases h with
  | eval_set he hupd hwf => exact .eval_set (hb.trans he) hupd hwf


/-! ## Environment invariants and their preservation under store updates

`ConstEnvGround` records that every propagated value is ground; together with
`ConstEnvSound` it is the invariant maintained by the simulation. -/

/-- Every value bound in the environment is a small ground value, as decided by
the propagation predicate `defaultSmallGroundValue`. -/
def ConstEnvGround
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono)) : Prop :=
  ∀ name to, Map.find? env name = some to → defaultSmallGroundValue to = true

theorem constEnvGround_erase
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono)) (x : Core.CoreIdent)
    (hg : ConstEnvGround env) : ConstEnvGround (eraseVar env x) := by
  intro name to hfind
  unfold eraseVar at hfind
  by_cases h : x = name
  · subst h; rw [Map.find?_erase_self] at hfind; simp at hfind
  · rw [Map.find?_erase_ne env x name (Ne.symm h)] at hfind; exact hg name to hfind

theorem constEnvGround_insert
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono)) (x : Core.CoreIdent)
    (v : Lambda.LExpr Core.CoreLParams.mono)
    (hg : ConstEnvGround env) (hv : defaultSmallGroundValue v = true) :
    ConstEnvGround (Map.insert env x v) := by
  intro name to hfind
  by_cases h : x = name
  · subst h; rw [Map.find?_insert_self] at hfind; injection hfind with h2; subst h2; exact hv
  · rw [Map.find?_insert_ne env name x v (Ne.symm h)] at hfind; exact hg name to hfind

/-- Erasing `x` keeps soundness after a store update that touches only `x`.

Any value in the environment is closed (`getFvars = []`, from `ground_no_fvars`
applied to the `ConstEnvGround` invariant), which is exactly what
`ground_eval_store_indep` needs to show the bound value's evaluation is
store-independent. -/
theorem constEnvSound_erase
    (f : Core.Expression.Factory)
    (hexpr : WellFormedSemanticEvalExprCongr f)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (σ σ' : SemanticStore Core.Expression) (x : Core.CoreIdent)
    (hupd : ∀ y, x ≠ y → σ' y = σ y)
    (hg : ConstEnvGround env) (hs : ConstEnvSound f env σ) :
    ConstEnvSound f (eraseVar env x) σ' := by
  intro name to hfind
  unfold eraseVar at hfind
  by_cases h : x = name
  · subst h; rw [Map.find?_erase_self] at hfind; simp at hfind
  · rw [Map.find?_erase_ne env x name (Ne.symm h)] at hfind
    rw [hupd name h, hs name to hfind]
    exact ground_eval_store_indep f hexpr σ σ' to (ground_no_fvars to (hg name to hfind))

/-- Inserting a ground binding `x ↦ v` keeps soundness after a store update that
sets `x` to `v`'s value and touches nothing else. Because propagated values are
closed (`getFvars = []`, from `ground_no_fvars`), both the inserted value and the
pre-existing bindings are store-independent. -/
theorem constEnvSound_insert
    (f : Core.Expression.Factory)
    (hexpr : WellFormedSemanticEvalExprCongr f)
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (σ σ' : SemanticStore Core.Expression) (x : Core.CoreIdent)
    (v : Lambda.LExpr Core.CoreLParams.mono)
    (hupd : ∀ y, x ≠ y → σ' y = σ y)
    (hx : σ' x = Core.Expression.eval f σ v)
    (hvg : defaultSmallGroundValue v = true)
    (hg : ConstEnvGround env) (hs : ConstEnvSound f env σ) :
    ConstEnvSound f (Map.insert env x v) σ' := by
  intro name to hfind
  by_cases h : x = name
  · subst h
    rw [Map.find?_insert_self] at hfind
    injection hfind with h2; subst h2
    rw [hx]
    exact ground_eval_store_indep f hexpr σ σ' _ (ground_no_fvars _ hvg)
  · rw [Map.find?_insert_ne env name x v (Ne.symm h)] at hfind
    rw [hupd name h, hs name to hfind]
    exact ground_eval_store_indep f hexpr σ σ' to (ground_no_fvars to (hg name to hfind))

/-! ## Statement-level small-step simulation (single command)

Lifting each command-level substitution lemma through `StepStmt.step_cmd` and
`Core.EvalCommand.cmd_sem`: executing the substituted command *statement* reaches the
same terminal environment in one small step. These are the command steps of the
statement-list simulation. -/

section StmtSubst
variable {π : String → Option Core.Procedure}
  {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
  (ρ : Imperative.Env Core.Expression)
  (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))

theorem evalStmt_assert_subst
    (hvar : WellFormedSemanticEvalVar ρ.factory) (hcong : Core.WellFormedCoreEvalCong ρ.factory)
    (hstore : WellFormedStore ρ.store ρ.factory) (hsound : ConstEnvSound ρ.factory env ρ.store) {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression ρ.factory ρ.store (.assert l e md) σ' f) :
    Core.EvalStatement π φ ρ
      (.cmd (Core.CmdExt.cmd (.assert l (Lambda.LExpr.substFvars e env) md)))
      { ρ with store := σ', hasFailure := ρ.hasFailure || f } :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (Core.EvalCommand.cmd_sem (evalCmd_assert_subst ρ.factory ρ.store env hvar hcong hstore hsound h)))
    (ReflTrans.refl _)

theorem evalStmt_assume_subst
    (hvar : WellFormedSemanticEvalVar ρ.factory) (hcong : Core.WellFormedCoreEvalCong ρ.factory)
    (hstore : WellFormedStore ρ.store ρ.factory) (hsound : ConstEnvSound ρ.factory env ρ.store) {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression ρ.factory ρ.store (.assume l e md) σ' f) :
    Core.EvalStatement π φ ρ
      (.cmd (Core.CmdExt.cmd (.assume l (Lambda.LExpr.substFvars e env) md)))
      { ρ with store := σ', hasFailure := ρ.hasFailure || f } :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (Core.EvalCommand.cmd_sem (evalCmd_assume_subst ρ.factory ρ.store env hvar hcong hstore hsound h)))
    (ReflTrans.refl _)

theorem evalStmt_cover_subst {l : String} {e md σ' f}
    (h : Imperative.EvalCmd Core.Expression ρ.factory ρ.store (.cover l e md) σ' f) :
    Core.EvalStatement π φ ρ
      (.cmd (Core.CmdExt.cmd (.cover l (Lambda.LExpr.substFvars e env) md)))
      { ρ with store := σ', hasFailure := ρ.hasFailure || f } :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (Core.EvalCommand.cmd_sem (evalCmd_cover_subst ρ.factory ρ.store env h)))
    (ReflTrans.refl _)

theorem evalStmt_init_det_subst
    (hvar : WellFormedSemanticEvalVar ρ.factory) (hcong : Core.WellFormedCoreEvalCong ρ.factory)
    (hstore : WellFormedStore ρ.store ρ.factory) (hsound : ConstEnvSound ρ.factory env ρ.store) {x ty e md σ' f}
    (h : Imperative.EvalCmd Core.Expression ρ.factory ρ.store (.init x ty (.det e) md) σ' f) :
    Core.EvalStatement π φ ρ
      (.cmd (Core.CmdExt.cmd (.init x ty (.det (Lambda.LExpr.substFvars e env)) md)))
      { ρ with store := σ', hasFailure := ρ.hasFailure || f } :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (Core.EvalCommand.cmd_sem (evalCmd_init_det_subst ρ.factory ρ.store env hvar hcong hstore hsound h)))
    (ReflTrans.refl _)

theorem evalStmt_set_det_subst
    (hvar : WellFormedSemanticEvalVar ρ.factory) (hcong : Core.WellFormedCoreEvalCong ρ.factory)
    (hstore : WellFormedStore ρ.store ρ.factory) (hsound : ConstEnvSound ρ.factory env ρ.store) {x e md σ' f}
    (h : Imperative.EvalCmd Core.Expression ρ.factory ρ.store (.set x (.det e) md) σ' f) :
    Core.EvalStatement π φ ρ
      (.cmd (Core.CmdExt.cmd (.set x (.det (Lambda.LExpr.substFvars e env)) md)))
      { ρ with store := σ', hasFailure := ρ.hasFailure || f } :=
  ReflTrans.step _ _ _
    (StepStmt.step_cmd (Core.EvalCommand.cmd_sem (evalCmd_set_det_subst ρ.factory ρ.store env hvar hcong hstore hsound h)))
    (ReflTrans.refl _)

end StmtSubst

/-! ## Statement-list composition (backbone of the list-level induction) -/

/-- Decompose a cons-list execution into the head statement's execution and the
tail's execution. -/
theorem evalStmts_cons_inv
    {π : String → Option Core.Procedure}
    {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
    {s : Core.Statement} {rest : List Core.Statement}
    {ρ ρ' : Imperative.Env Core.Expression}
    (h : Core.EvalStatements π φ ρ (s :: rest) ρ') :
    ∃ ρ₁, Core.EvalStatement π φ ρ s ρ₁ ∧ Core.EvalStatements π φ ρ₁ rest ρ' := by
  obtain ⟨ρ₁, h1, h2, _⟩ := stmtsT_cons_terminal (reflTrans_to_T h)
  exact ⟨ρ₁, reflTransT_to_prop h1, reflTransT_to_prop h2⟩

/-- Build a cons-list execution from the head's and the tail's executions. -/
theorem evalStmts_cons
    {π : String → Option Core.Procedure}
    {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
    {s : Core.Statement} {rest : List Core.Statement}
    {ρ ρ₁ ρ' : Imperative.Env Core.Expression}
    (h1 : Core.EvalStatement π φ ρ s ρ₁)
    (h2 : Core.EvalStatements π φ ρ₁ rest ρ') :
    Core.EvalStatements π φ ρ (s :: rest) ρ' := by
  have hc := stmts_cons_step Core.Expression (Core.EvalCommand π φ) (Core.EvalPureFunc φ)
    s rest ρ ρ₁ h1
  exact ReflTrans_Transitive _ _ _ _ hc h2

/-- Invert a single command-statement execution: it is exactly one `step_cmd`,
exposing the underlying `EvalCmd` and the resulting environment. -/
theorem evalStmt_cmd_inv
    {π : String → Option Core.Procedure}
    {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
    {c : Imperative.Cmd Core.Expression} {ρ ρ' : Imperative.Env Core.Expression}
    (h : Core.EvalStatement π φ ρ (.cmd (Core.CmdExt.cmd c)) ρ') :
    ∃ σ' f, Imperative.EvalCmd Core.Expression ρ.factory ρ.store c σ' f ∧
            ρ' = { ρ with store := σ', hasFailure := ρ.hasFailure || f } := by
  cases h with
  | step _ mid _ hstep hrest =>
    cases hstep with
    | step_cmd hcmd =>
      cases hcmd with
      | cmd_sem hev =>
        cases hrest with
        | refl => exact ⟨_, _, hev, rfl⟩
        | step _ _ _ hstep2 _ => nomatch hstep2

/-- `propagateConstants.go` only ever prepends transformed statements onto its
accumulator, so the accumulator is independent of the processing: the output
list is `acc.reverse ++ (output with empty acc)`. -/
theorem propagateConstants_go_acc_append
    (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
    (stmts : List Core.Statement) :
    ∀ (acc : List Core.Statement),
      (propagateConstants.go env stmts acc).1
        = acc.reverse ++ (propagateConstants.go env stmts []).1 := by
  induction stmts generalizing env with
  | nil => intro acc; simp [propagateConstants.go]
  | cons s rest ih =>
    intro acc
    cases s with
    | cmd c =>
      cases c with
      | cmd ic =>
        cases ic with
        | init name ty eon md =>
          cases eon with
          | det e =>
            simp only [propagateConstants.go]
            conv => lhs; rw [ih]
            conv => rhs; rw [ih]
            simp [List.reverse_cons, List.append_assoc]
          | nondet =>
            simp only [propagateConstants.go]
            conv => lhs; rw [ih]
            conv => rhs; rw [ih]
            simp [List.reverse_cons, List.append_assoc]
        | set name eon md =>
          cases eon with
          | det e =>
            simp only [propagateConstants.go]
            conv => lhs; rw [ih]
            conv => rhs; rw [ih]
            simp [List.reverse_cons, List.append_assoc]
          | nondet =>
            simp only [propagateConstants.go]
            conv => lhs; rw [ih]
            conv => rhs; rw [ih]
            simp [List.reverse_cons, List.append_assoc]
        | assert l b md =>
          simp only [propagateConstants.go]
          conv => lhs; rw [ih]
          conv => rhs; rw [ih]
          simp [List.reverse_cons, List.append_assoc]
        | assume l b md =>
          simp only [propagateConstants.go]
          conv => lhs; rw [ih]
          conv => rhs; rw [ih]
          simp [List.reverse_cons, List.append_assoc]
        | cover l b md =>
          simp only [propagateConstants.go]
          conv => lhs; rw [ih]
          conv => rhs; rw [ih]
          simp [List.reverse_cons, List.append_assoc]
      | call pn args md =>
        simp only [propagateConstants.go]
        conv => lhs; rw [ih]
        conv => rhs; rw [ih]
        simp [List.reverse_cons, List.append_assoc]
    | block l b md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    | ite c tb eb md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    | loop g meas invs b md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    | exit l md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    | funcDecl decl md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]
    | typeDecl tc md =>
      simp only [propagateConstants.go]
      conv => lhs; rw [ih]
      conv => rhs; rw [ih]
      simp [List.reverse_cons, List.append_assoc]

/-- A statement that is an atomic command: a `det` or `nondet` (havoc) init/set
or a pure assert/assume/cover.

Both deterministic and nondeterministic init/set are covered. A nondet (havoc)
write now stores a *value* (per the strengthened havoc semantics: the
`eval_init_unconstrained`/`eval_set_nondet` rules carry a `HasVal.value`
premise), so it preserves the `WellFormedStore` invariant that the substitution
bridge's variable rule relies on. Constant propagation kills the written
variable (erases its binding), keeping `ConstEnvSound`/`ConstEnvGround`. -/
def IsCmdStmt : Core.Statement → Prop
  | .cmd (Core.CmdExt.cmd (.init _ _ (.det _) _)) => True
  | .cmd (Core.CmdExt.cmd (.init _ _ .nondet _)) => True
  | .cmd (Core.CmdExt.cmd (.set _ (.det _) _)) => True
  | .cmd (Core.CmdExt.cmd (.set _ .nondet _)) => True
  | .cmd (Core.CmdExt.cmd (.assert _ _ _)) => True
  | .cmd (Core.CmdExt.cmd (.assume _ _ _)) => True
  | .cmd (Core.CmdExt.cmd (.cover _ _ _)) => True
  | _ => False

/-- **Capstone (straight-line).** For a list consisting solely of atomic commands
(det/nondet init/set and assert/assume/cover), the constant-propagated program
reaches the *same* terminal environment as the original. The propagation
environment evolves per statement (insert a ground binding on a det write,
erase on non-ground or nondet), and `ConstEnvSound`/`ConstEnvGround` are
maintained across each store update via the preservation lemmas.

Requires `WellFormedStore ρ.store` (the substitution bridge's variable rule only
fires on well-formed stores) and `WellFormedSemanticEvalVal ρ.eval` (to show a
det write stores a value, preserving `WellFormedStore` across the step). A nondet
write preserves `WellFormedStore` directly from the `HasVal.value` premise of the
strengthened havoc rules. -/
theorem propagateConstants_sim_cmds
    {π : String → Option Core.Procedure}
    {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
    (ρ' : Imperative.Env Core.Expression) :
    ∀ (stmts : List Core.Statement)
      (env : Map Core.CoreIdent (Lambda.LExpr Core.CoreLParams.mono))
      (ρ : Imperative.Env Core.Expression),
      WellFormedSemanticEvalVar ρ.factory → Core.WellFormedCoreEvalCong ρ.factory →
      WellFormedSemanticEvalExprCongr ρ.factory →
      WellFormedStore ρ.store ρ.factory → WellFormedSemanticEvalVal ρ.factory →
      ConstEnvSound ρ.factory env ρ.store → ConstEnvGround env →
      (∀ s ∈ stmts, IsCmdStmt s) →
      Core.EvalStatements π φ ρ stmts ρ' →
      Core.EvalStatements π φ ρ (propagateConstants.go env stmts []).1 ρ' := by
  intro stmts
  induction stmts with
  | nil =>
    intro env ρ _ _ _ _ _ _ _ _ horig
    simpa [propagateConstants.go] using horig
  | cons s rest ih =>
    intro env ρ hvar hcong hexpr hstore hval hsound hground hcmds horig
    obtain ⟨ρ₁, hstep, htail⟩ := evalStmts_cons_inv horig
    have hmem : s ∈ s :: rest := List.mem_cons_self
    have hrest : ∀ t ∈ rest, IsCmdStmt t := fun t ht => hcmds t (List.mem_cons.mpr (Or.inr ht))
    cases s with
    | cmd c =>
      cases c with
      | cmd ic =>
        cases ic with
        | init name ty eon md =>
          cases eon with
          | det e =>
            obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
            have hhead := evalStmt_init_det_subst (π := π) (φ := φ) ρ env hvar hcong hstore hsound hev
            cases hev with
            | eval_init hδe hinit hwf =>
              cases hinit with
              | init hnone hsome hupd =>
                rw [← hρ₁] at hhead
                have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
                have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
                have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
                have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
                -- The det write stores a value (`outputsAreValues`), so
                -- `WellFormedStore` is preserved across the step.
                have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by
                  have hst : ρ₁.store = σ' := by rw [hρ₁]
                  have hfac : ρ₁.factory = ρ.factory := by rw [hρ₁]
                  rw [hst, hfac]
                  intro y w hyw
                  by_cases hy : name = y
                  · subst hy
                    rw [hsome] at hyw
                    injection hyw with hvw
                    exact hval.outputsAreValues e w ρ.store hstore (by rw [hδe, hvw])
                  · rw [hupd y hy] at hyw; exact hstore y w hyw
                simp only [propagateConstants.go]
                rw [propagateConstants_go_acc_append]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                refine evalStmts_cons hhead ?_
                split
                · rename_i hg
                  refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                  · rw [hρ₁]
                    exact constEnvSound_insert ρ.factory hexpr env ρ.store σ' name _ hupd
                      (by rw [hsome, substFvars_eval_eq ρ.factory ρ.store env hvar hcong hstore hsound e]; exact hδe.symm)
                      hg hground hsound
                  · exact constEnvGround_insert env name _ hground hg
                · rename_i hg
                  refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                  · rw [hρ₁]
                    exact constEnvSound_erase ρ.factory hexpr env ρ.store σ' name hupd hground hsound
                  · exact constEnvGround_erase env name hground
          | nondet =>
            -- Nondet (havoc) init: the strengthened `eval_init_unconstrained`
            -- rule carries a `HasVal.value` premise, so the havoc'd value is a
            -- value and `WellFormedStore` is preserved. The transform leaves the
            -- statement unchanged and erases the env binding for `name`.
            obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
            cases hev with
            | eval_init_unconstrained hinit hvalue hwf =>
              cases hinit with
              | init hnone hsome hupd =>
                have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
                have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
                have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
                have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
                -- The havoc'd value is a value (`hvalue`), so `WellFormedStore`
                -- is preserved across the nondet write.
                have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by
                  have hst : ρ₁.store = σ' := by rw [hρ₁]
                  have hfac : ρ₁.factory = ρ.factory := by rw [hρ₁]
                  rw [hst, hfac]
                  intro y w hyw
                  by_cases hy : name = y
                  · subst hy
                    rw [hsome] at hyw
                    injection hyw with hvw
                    rw [← hvw]; exact hvalue
                  · rw [hupd y hy] at hyw; exact hstore y w hyw
                simp only [propagateConstants.go]
                rw [propagateConstants_go_acc_append]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                refine evalStmts_cons hstep ?_
                refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                · rw [hρ₁]
                  exact constEnvSound_erase ρ.factory hexpr env ρ.store σ' name hupd hground hsound
                · exact constEnvGround_erase env name hground
        | set name eon md =>
          cases eon with
          | det e =>
            obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
            have hhead := evalStmt_set_det_subst (π := π) (φ := φ) ρ env hvar hcong hstore hsound hev
            cases hev with
            | eval_set hδe hupdate hwf =>
              cases hupdate with
              | update hv' hsome hupd =>
                rw [← hρ₁] at hhead
                have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
                have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
                have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
                have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
                -- The det write stores a value (`outputsAreValues`), so
                -- `WellFormedStore` is preserved across the step.
                have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by
                  have hst : ρ₁.store = σ' := by rw [hρ₁]
                  have hfac : ρ₁.factory = ρ.factory := by rw [hρ₁]
                  rw [hst, hfac]
                  intro y w hyw
                  by_cases hy : name = y
                  · subst hy
                    rw [hsome] at hyw
                    injection hyw with hvw
                    exact hval.outputsAreValues e w ρ.store hstore (by rw [hδe, hvw])
                  · rw [hupd y hy] at hyw; exact hstore y w hyw
                simp only [propagateConstants.go]
                rw [propagateConstants_go_acc_append]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                refine evalStmts_cons hhead ?_
                split
                · rename_i hg
                  refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                  · rw [hρ₁]
                    exact constEnvSound_insert ρ.factory hexpr env ρ.store σ' name _ hupd
                      (by rw [hsome, substFvars_eval_eq ρ.factory ρ.store env hvar hcong hstore hsound e]; exact hδe.symm)
                      hg hground hsound
                  · exact constEnvGround_insert env name _ hground hg
                · rename_i hg
                  refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                  · rw [hρ₁]
                    exact constEnvSound_erase ρ.factory hexpr env ρ.store σ' name hupd hground hsound
                  · exact constEnvGround_erase env name hground
          | nondet =>
            -- Nondet (havoc) set: the strengthened `eval_set_nondet` rule carries
            -- a `HasVal.value` premise, so the havoc'd value is a value and
            -- `WellFormedStore` is preserved. The transform leaves the statement
            -- unchanged and erases the env binding for `name`.
            obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
            cases hev with
            | eval_set_nondet hupdate hvalue hwf =>
              cases hupdate with
              | update hv' hsome hupd =>
                have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
                have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
                have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
                have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
                -- The havoc'd value is a value (`hvalue`), so `WellFormedStore`
                -- is preserved across the nondet write.
                have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by
                  have hst : ρ₁.store = σ' := by rw [hρ₁]
                  have hfac : ρ₁.factory = ρ.factory := by rw [hρ₁]
                  rw [hst, hfac]
                  intro y w hyw
                  by_cases hy : name = y
                  · subst hy
                    rw [hsome] at hyw
                    injection hyw with hvw
                    rw [← hvw]; exact hvalue
                  · rw [hupd y hy] at hyw; exact hstore y w hyw
                simp only [propagateConstants.go]
                rw [propagateConstants_go_acc_append]
                simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
                refine evalStmts_cons hstep ?_
                refine ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ ?_ ?_ hrest htail
                · rw [hρ₁]
                  exact constEnvSound_erase ρ.factory hexpr env ρ.store σ' name hupd hground hsound
                · exact constEnvGround_erase env name hground
        | assert l b md =>
          obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
          have hhead := evalStmt_assert_subst (π := π) (φ := φ) ρ env hvar hcong hstore hsound hev
          cases hev <;> (
            rw [← hρ₁] at hhead
            have hsound₁ : ConstEnvSound ρ₁.factory env ρ₁.store := by rw [hρ₁]; exact hsound
            have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
            have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
            have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
            have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by rw [hρ₁]; exact hstore
            have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
            have htailT := ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ hsound₁ hground hrest htail
            simp only [propagateConstants.go]
            rw [propagateConstants_go_acc_append]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            exact evalStmts_cons hhead htailT)
        | assume l b md =>
          obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
          have hhead := evalStmt_assume_subst (π := π) (φ := φ) ρ env hvar hcong hstore hsound hev
          cases hev <;> (
            rw [← hρ₁] at hhead
            have hsound₁ : ConstEnvSound ρ₁.factory env ρ₁.store := by rw [hρ₁]; exact hsound
            have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
            have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
            have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
            have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by rw [hρ₁]; exact hstore
            have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
            have htailT := ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ hsound₁ hground hrest htail
            simp only [propagateConstants.go]
            rw [propagateConstants_go_acc_append]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            exact evalStmts_cons hhead htailT)
        | cover l b md =>
          obtain ⟨σ', f, hev, hρ₁⟩ := evalStmt_cmd_inv hstep
          have hhead := evalStmt_cover_subst (π := π) (φ := φ) ρ env hev
          cases hev <;> (
            rw [← hρ₁] at hhead
            have hsound₁ : ConstEnvSound ρ₁.factory env ρ₁.store := by rw [hρ₁]; exact hsound
            have hvar₁ : WellFormedSemanticEvalVar ρ₁.factory := by rw [hρ₁]; exact hvar
            have hcong₁ : Core.WellFormedCoreEvalCong ρ₁.factory := by rw [hρ₁]; exact hcong
            have hexpr₁ : WellFormedSemanticEvalExprCongr ρ₁.factory := by rw [hρ₁]; exact hexpr
            have hstore₁ : WellFormedStore ρ₁.store ρ₁.factory := by rw [hρ₁]; exact hstore
            have hval₁ : WellFormedSemanticEvalVal ρ₁.factory := by rw [hρ₁]; exact hval
            have htailT := ih _ ρ₁ hvar₁ hcong₁ hexpr₁ hstore₁ hval₁ hsound₁ hground hrest htail
            simp only [propagateConstants.go]
            rw [propagateConstants_go_acc_append]
            simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
            exact evalStmts_cons hhead htailT)
      | call pn args md => exact (hcmds _ hmem).elim
    | block l b md => exact (hcmds _ hmem).elim
    | ite c tb eb md => exact (hcmds _ hmem).elim
    | loop g meas invs b md => exact (hcmds _ hmem).elim
    | exit l md => exact (hcmds _ hmem).elim
    | funcDecl decl md => exact (hcmds _ hmem).elim
    | typeDecl tc md => exact (hcmds _ hmem).elim

/-- **Entry-point corollary.** Specialises the straight-line capstone to the
empty initial environment that `propagateConstants` (and hence
`propagateConstantsInProgram`) actually starts from. For the empty environment
the propagation-soundness preconditions `ConstEnvSound`/`ConstEnvGround` hold
vacuously (`Map.find? [] = none`), so straight-line constant propagation is
sound with no environment assumptions — only the standard evaluator
well-formedness conditions remain. -/
theorem propagateConstants_sim_cmds_entry
    {π : String → Option Core.Procedure}
    {φ : Core.Expression.Factory → Imperative.PureFunc Core.Expression → Core.Expression.Factory}
    (ρ' : Imperative.Env Core.Expression)
    (stmts : List Core.Statement)
    (ρ : Imperative.Env Core.Expression)
    (hvar : WellFormedSemanticEvalVar ρ.factory) (hcong : Core.WellFormedCoreEvalCong ρ.factory)
    (hexpr : WellFormedSemanticEvalExprCongr ρ.factory)
    (hstore : WellFormedStore ρ.store ρ.factory) (hval : WellFormedSemanticEvalVal ρ.factory)
    (hcmds : ∀ s ∈ stmts, IsCmdStmt s)
    (horig : Core.EvalStatements π φ ρ stmts ρ') :
    Core.EvalStatements π φ ρ (propagateConstants.go [] stmts []).1 ρ' :=
  propagateConstants_sim_cmds ρ' stmts [] ρ hvar hcong hexpr hstore hval
    (by intro name to h; simp [Map.find?] at h)
    (by intro name to h; simp [Map.find?] at h)
    hcmds horig

end Strata
