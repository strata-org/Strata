/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Logic.LangDef
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Imperative.Logic.TerminationProps
import Strata.DL.Imperative.Analysis.Verdict
import Strata.DL.Imperative.Logic.ProgramEntries
import Strata.DL.Imperative.StmtSemanticsProps
import Strata.Languages.Core.Logic.TraceInterpUsingDenote
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import StrataDDM.Integration.Lean.HashCommands

/-! # Divergence and termination of Core programs

Each test writes a Core program in DDM syntax, translates it to the Core AST, and
proves a fact about the procedure body under the event semantics
`Core.Logic.EventLang.coreBlock`, for any procedure environment.

## Key results

- `spin_diverges`, `spin_not_terminates`, `star_diverges`, `star_not_terminates`,
  `star_mayTerminate`, `count_terminates`, `count_not_canDiverge`: divergence
  and termination of three loops, with
  divergence given by a sequence `ℕ → CfgT` each of whose configurations steps
  to the next.
- `fail_failed`, `ok_valid`: a `failed` and a `valid` verdict, with conditions
  read by denotation in any model of `Core.Factory`.
- `afterExit_reachable_not_final`, `afterExit_reaches_after`: an exit caught by
  its block does not finish the run.

A loop with an empty body returns to its head after five steps, inside one more
`seq` frame each time (`wrap`). The states at the loop head, at any depth, are
the cycle `EventLang.CanDiverge.of_cycle` needs.

**These tests use `native_decide`** to read the translated AST, as
`Logic/Hoare.lean` does.
-/

open Imperative Strata.Logic
open StrataDDM (Program)

namespace Strata

/-- Translate a DDM concrete-syntax program to the Core AST. -/
private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

namespace TerminationTests

/-! ## Loops with an empty body, in general -/

/-- `n` extra `seq … []` frames around a configuration. -/
private def wrap : Nat → Core.CoreConfig → Core.CoreConfig
  | 0, c => c
  | n + 1, c => wrap n (.seq c [])

section EmptyLoop

variable (π : String → Option Core.Procedure)

/-- A step stays a step under `wrap`. -/
private theorem wrap_step {c c' : Core.CoreConfig} {emitted : Trace Core.Expression}
    (h : Core.CoreStepE π c emitted c') :
    ∀ n, Core.CoreStepE π (wrap n c) emitted (wrap n c') := by
  intro n
  induction n generalizing c c' with
  | zero => exact h
  | succ n ih => exact ih (StepStmtE.step_seq_inner h)

/-- A run stays a run under `wrap`. -/
private theorem wrap_star {c c' : Core.CoreConfig} {trace : Trace Core.Expression}
    (h : Core.CoreStepStarE π c trace c') :
    ∀ n, Core.CoreStepStarE π (wrap n c) trace (wrap n c') := by
  intro n
  induction n generalizing c c' with
  | zero => exact h
  | succ n ih => exact ih (Imperative.seq_inner_starE _ h)

/-- An administrative step as an event step. -/
private theorem admin {c c' : Core.CoreConfig}
    (h : StepStmt Core.Expression (noCommandEvalE Core.Expression Core.Command)
      c c') :
    Core.CoreStepE π c [] c' :=
  .step_admin h

/-- A loop `guard` with an empty body, whose guard lets it enter from every state
    satisfying `Good`, diverges from such states, provided `Good` survives an
    iteration. -/
private theorem emptyLoop_diverges (guard : ExprOrNondet Core.Expression)
    (m : Option Core.Expression.Expr) (inv : List (String × Core.Expression.Expr))
    (md : MetaData Core.Expression) (Good : Env Core.Expression → Prop)
    (henter : ∀ ρ, Good ρ →
      StepStmt Core.Expression (noCommandEvalE Core.Expression Core.Command)
        (.stmt (.loop guard m inv [] md) ρ)
        (.seq (.block .none ρ.store (.stmts [] ρ)) [.loop guard m inv [] md]))
    (hgood : ∀ ρ, Good ρ →
      Good { ρ with store := projectStore ρ.store ρ.store })
    (ρ : Env Core.Expression) (hρ : Good ρ) :
    (Core.Logic.EventLang.coreBlock π).CanDiverge
      ((Core.Logic.EventLang.coreBlock π).stmtCfg [.loop guard m inv [] md] ρ) := by
  let L : Core.Statement := .loop guard m inv [] md
  have hcycle : (Core.Logic.EventLang.coreBlock π).CanDiverge (wrap 1 (.stmt L ρ)) := by
    refine EventLang.CanDiverge.of_cycle
      (fun c => ∃ n ρ, Good ρ ∧ c = wrap (n + 1) (.stmt L ρ)) ?_ ⟨0, ρ, hρ, rfl⟩
    rintro c ⟨n, ρ, hρ, rfl⟩
    have hrun : Core.CoreStepStarE π
        (.seq (.block .none ρ.store (.stmts [] ρ)) [L]) []
        (.seq (.stmt L { ρ with store := projectStore ρ.store ρ.store })
          []) :=
      .step _ [] _ [] _ (admin π (.step_seq_inner (.step_block_body .step_stmts_nil))) <|
      .step _ [] _ [] _ (admin π (.step_seq_inner .step_block_done)) <|
      .step _ [] _ [] _ (admin π .step_seq_done) <|
      .step _ [] _ [] _ (admin π .step_stmts_cons) (.refl _)
    exact ⟨[], _, [], _, wrap_step π (admin π (henter ρ hρ)) (n + 1),
      wrap_star π hrun (n + 1), ⟨n + 1, _, hgood ρ hρ, rfl⟩⟩
  exact EventLang.CanDiverge.step (EL := Core.Logic.EventLang.coreBlock π)
    (admin π .step_stmts_cons) hcycle

end EmptyLoop

/-! ## `while (true) { }` diverges -/

private def spinPgm : Program :=
#strata
program Core;

procedure Spin()
{
  while (true) {
  }
};
#end

private def spinPgmAST : Core.Program := cstToAST spinPgm

private def spinProc : Core.Procedure := (spinPgmAST.findProcByString? "Spin").get!

/-- The guard, measure, invariants and metadata of the translated loop. -/
private def spinParts :
    Core.Expression.Expr × Option Core.Expression.Expr ×
      List (String × Core.Expression.Expr) × MetaData Core.Expression :=
  match spinProc.body with
  | .structured [Stmt.loop (.det g) m inv [] md] => (g, m, inv, md)
  | _ => default

private def spinLoop : Core.Statement :=
  .loop (.det spinParts.1) spinParts.2.1 spinParts.2.2.1 [] spinParts.2.2.2

/-- The translated body really is the single loop. -/
private theorem spin_body_eq : spinProc.body = .structured [spinLoop] := by
  native_decide

/-- The loop guard really is the literal `true`. -/
private theorem spinGuard_eq :
    spinParts.1 = Lambda.LExpr.const () (Lambda.LConst.boolConst true) := by
  native_decide

/-- **`while (true) { }` diverges** from every state: the guard is the literal
    `true`, so the loop enters on every iteration. -/
theorem spin_diverges (π : String → Option Core.Procedure) (ρ : Env Core.Expression) :
    (Core.Logic.EventLang.coreBlock π).CanDiverge
      ((Core.Logic.EventLang.coreBlock π).stmtCfg [spinLoop] ρ) :=
  emptyLoop_diverges π _ _ _ _ (fun _ => True)
    (fun ρ _ => .step_loop_enter (by
      rw [spinGuard_eq]
      exact Lambda.evalFully_const ρ.factory ρ.store () (Lambda.LConst.boolConst true)))
    (fun _ _ => trivial) ρ trivial

/-- `while (true) { }` does not terminate. -/
theorem spin_not_terminates (π : String → Option Core.Procedure) (ρ : Env Core.Expression) :
    ¬ (Core.Logic.EventLang.coreBlock π).Terminates [spinLoop] ρ :=
  fun hterm => hterm.not_canDiverge (spin_diverges π ρ)

/-! ## `while * { }` diverges, yet may terminate -/

private def starPgm : Program :=
#strata
program Core;

procedure Star()
{
  while * {
  }
};
#end

private def starPgmAST : Core.Program := cstToAST starPgm

private def starProc : Core.Procedure := (starPgmAST.findProcByString? "Star").get!

/-- The measure, invariants and metadata of the translated loop. -/
private def starParts :
    Option Core.Expression.Expr × List (String × Core.Expression.Expr) × MetaData Core.Expression :=
  match starProc.body with
  | .structured [Stmt.loop .nondet m inv [] md] => (m, inv, md)
  | _ => default

private def starLoop : Core.Statement :=
  .loop .nondet starParts.1 starParts.2.1 [] starParts.2.2

/-- The translated body really is the single nondeterministic loop. -/
private theorem star_body_eq : starProc.body = .structured [starLoop] := by
  native_decide

/-- **`while * { }` diverges** from every state: the execution that always
    chooses to enter the loop never ends. -/
theorem star_diverges (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) :
    (Core.Logic.EventLang.coreBlock π).CanDiverge
      ((Core.Logic.EventLang.coreBlock π).stmtCfg [starLoop] ρ) :=
  emptyLoop_diverges π _ _ _ _ (fun _ => True) (fun _ _ => .step_loop_nondet_enter)
    (fun _ _ => trivial) ρ trivial

/-- `while * { }` does not terminate: not every execution finishes. -/
theorem star_not_terminates (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) :
    ¬ (Core.Logic.EventLang.coreBlock π).Terminates [starLoop] ρ :=
  fun hterm => hterm.not_canDiverge (star_diverges π ρ)

/-- Yet `while * { }` may terminate: the execution that exits at once finishes. -/
theorem star_mayTerminate (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) :
    ∃ trace ρ', (Core.Logic.EventLang.coreBlock π).TerminatesAt [starLoop] ρ trace ρ' :=
  ⟨_, ρ, .inl <|
    .step _ [] _ _ _ (.step_admin .step_stmts_cons) <|
    .step _ [] _ _ _ (.step_admin (.step_seq_inner .step_loop_nondet_exit)) <|
    .step _ [] _ _ _ (.step_admin .step_seq_done) <|
    .step _ [] _ _ _ (.step_admin .step_stmts_nil) (.refl _)⟩

/-! ## A finite loop with a deterministic step terminates

`var y : int := 0; while (int.le(y, 9)) { y := int.add(y, 1); }` runs ten
iterations and stops, from every state where `y` is not yet declared and the
factory is `Core.Factory`, whose arithmetic the guard and the increment need.

`Terminates` asks that every successor of every reachable configuration must
terminate. The proof builds that up from the statements, using `Finishes`, a
form of must-termination that also records where runs end, so that it carries
through `seq`, `block` and statement lists. -/

section Finishes

variable (π : String → Option Core.Procedure)

/-- Every run from `c` keeps stepping until it ends normally, at an environment
    satisfying `Q`. -/
private inductive Finishes (Q : Env Core.Expression → Prop) : Core.CoreConfig → Prop where
  | done {ρ : Env Core.Expression} : Q ρ → Finishes Q (.terminal ρ)
  | step {c : Core.CoreConfig} :
      (∃ e c', Core.CoreStepE π c e c') →
      (∀ e c', Core.CoreStepE π c e c' → Finishes Q c') → Finishes Q c

/-- Finishing is a form of must-termination. -/
private theorem Finishes.mustTerminate {Q : Env Core.Expression → Prop} {c : Core.CoreConfig}
    (h : Finishes π Q c) : (Core.Logic.EventLang.coreBlock π).MustTerminate c := by
  induction h with
  | done _ => exact .terminal _
  | step prog _ ih => exact .step prog fun e c' hs => ih e c' hs

/-- A terminal configuration takes no step. -/
private theorem no_step_terminal {ρ : Env Core.Expression} {e : Trace Core.Expression}
    {c' : Core.CoreConfig} : ¬ Core.CoreStepE π (.terminal ρ) e c' :=
  (Core.Logic.EventLang.coreBlock π).terminal_no_step ρ e c'

/-- An exiting configuration takes no step. -/
private theorem no_step_exiting {l : String} {ρ : Env Core.Expression}
    {e : Trace Core.Expression} {c' : Core.CoreConfig} :
    ¬ Core.CoreStepE π (.exiting l ρ) e c' :=
  (Core.Logic.EventLang.coreBlock π).exiting_no_step l ρ e c'

/-- The empty statement list finishes at once. -/
private theorem fin_nil {Q : Env Core.Expression → Prop} {ρ : Env Core.Expression}
    (hq : Q ρ) : Finishes π Q (.stmts [] ρ) :=
  .step ⟨[], _, .step_admin .step_stmts_nil⟩ fun e c' hs => by
    cases hs with
    | step_admin ha =>
      cases ha with
      | step_stmts_nil => exact .done hq

/-- A statement list finishes when its head, followed by its tail, does. -/
private theorem fin_cons {Q : Env Core.Expression → Prop} {s : Core.Statement}
    {ss : Core.Statements} {ρ : Env Core.Expression}
    (h : Finishes π Q (.seq (.stmt s ρ) ss)) : Finishes π Q (.stmts (s :: ss) ρ) :=
  .step ⟨[], _, .step_admin .step_stmts_cons⟩ fun e c' hs => by
    cases hs with
    | step_admin ha =>
      cases ha with
      | step_stmts_cons => exact h

/-- A sequence finishes when its head finishes at `Q` and the rest finishes from
    every environment satisfying `Q`. -/
private theorem fin_seq {Q R : Env Core.Expression → Prop} {inner : Core.CoreConfig}
    {ss : Core.Statements} (h : Finishes π Q inner)
    (hk : ∀ ρ, Q ρ → Finishes π R (.stmts ss ρ)) : Finishes π R (.seq inner ss) := by
  induction h with
  | done hq =>
    refine .step ⟨[], _, .step_admin .step_seq_done⟩ fun e c' hs => ?_
    cases hs with
    | step_admin ha =>
      cases ha with
      | step_seq_done => exact hk _ hq
      | step_seq_inner ha' => cases ha'
    | step_seq_inner hs' => exact absurd hs' (no_step_terminal π)
  | step prog _ ih =>
    obtain ⟨e₀, c₀, hs₀⟩ := prog
    refine .step ⟨e₀, _, .step_seq_inner hs₀⟩ fun e c' hs => ?_
    cases hs with
    | step_seq_inner hs' => exact ih _ _ hs'
    | step_admin ha =>
      cases ha with
      | step_seq_inner ha' => exact ih _ _ (.step_admin ha')
      | step_seq_done => exact absurd hs₀ (no_step_terminal π)
      | step_seq_exit => exact absurd hs₀ (no_step_exiting π)

/-- A block finishes when its body does, at the body's environment with the
    block's scope restored. -/
private theorem fin_block {Q : Env Core.Expression → Prop} {inner : Core.CoreConfig}
    {label : Option String} {σ : Core.CoreStore}
    (h : Finishes π Q inner) :
    Finishes π (fun ρ' => ∃ ρ, Q ρ ∧ ρ' = { ρ with store := projectStore σ ρ.store })
      (.block label σ inner) := by
  induction h with
  | done hq =>
    refine .step ⟨[], _, .step_admin .step_block_done⟩ fun e c' hs => ?_
    cases hs with
    | step_admin ha =>
      cases ha with
      | step_block_done => exact .done ⟨_, hq, rfl⟩
      | step_block_body ha' => cases ha'
    | step_block_body hs' => exact absurd hs' (no_step_terminal π)
  | step prog _ ih =>
    obtain ⟨e₀, c₀, hs₀⟩ := prog
    refine .step ⟨e₀, _, .step_block_body hs₀⟩ fun e c' hs => ?_
    cases hs with
    | step_block_body hs' => exact ih _ _ hs'
    | step_admin ha =>
      cases ha with
      | step_block_body ha' => exact ih _ _ (.step_admin ha')
      | step_block_done => exact absurd hs₀ (no_step_terminal π)
      | step_block_exit_match _ => exact absurd hs₀ (no_step_exiting π)
      | step_block_exit_mismatch _ => exact absurd hs₀ (no_step_exiting π)

/-- A command finishes when it can execute, at every store it can produce. -/
private theorem fin_cmd {Q : Env Core.Expression → Prop} {cmd : Core.Command}
    {ρ : Env Core.Expression}
    (hprog : ∃ σ' em, Core.EvalCommandE π ρ.factory ρ.store cmd σ' em)
    (hall : ∀ σ' em, Core.EvalCommandE π ρ.factory ρ.store cmd σ' em →
      Q { ρ with store := σ' }) :
    Finishes π Q (.stmt (.cmd cmd) ρ) := by
  obtain ⟨σ', em, hc⟩ := hprog
  refine .step ⟨em, _, .step_cmd hc⟩ fun e c' hs => ?_
  cases hs with
  | step_cmd hc' => exact .done (hall _ _ hc')
  | step_admin ha =>
    cases ha with
    | step_cmd hfalse => exact hfalse.elim

/-- A loop whose guard is false exits. -/
private theorem fin_loop_exit {Q : Env Core.Expression → Prop} {g : Core.Expression.Expr}
    {m : Option Core.Expression.Expr} {inv : List (String × Core.Expression.Expr)}
    {body : Core.Statements} {md : MetaData Core.Expression} {ρ : Env Core.Expression}
    (hg : Core.Expression.eval ρ.factory ρ.store g = some HasBool.ff) (hq : Q ρ) :
    Finishes π Q (.stmt (.loop (.det g) m inv body md) ρ) := by
  refine .step ⟨[], _, .step_admin (.step_loop_exit hg)⟩ fun e c' hs => ?_
  cases hs with
  | step_admin ha =>
    cases ha with
    | step_loop_exit _ => exact .done hq
    | step_loop_enter hg' =>
      exact absurd (Option.some.inj (hg'.symm.trans hg)) HasBool.tt_is_not_ff

/-- A loop whose guard is true runs its body, then the loop again. -/
private theorem fin_loop_enter {Q : Env Core.Expression → Prop} {g : Core.Expression.Expr}
    {m : Option Core.Expression.Expr} {inv : List (String × Core.Expression.Expr)}
    {body : Core.Statements} {md : MetaData Core.Expression} {ρ : Env Core.Expression}
    (hg : Core.Expression.eval ρ.factory ρ.store g = some HasBool.tt)
    (h : Finishes π Q
      (.seq (.block .none ρ.store (.stmts body ρ)) [.loop (.det g) m inv body md])) :
    Finishes π Q (.stmt (.loop (.det g) m inv body md) ρ) := by
  refine .step ⟨[], _, .step_admin (.step_loop_enter hg)⟩ fun e c' hs => ?_
  cases hs with
  | step_admin ha =>
    cases ha with
    | step_loop_enter _ => exact h
    | step_loop_exit hg' =>
      exact absurd (Option.some.inj (hg.symm.trans hg')) HasBool.tt_is_not_ff

end Finishes

private def countPgm : Program :=
#strata
program Core;

procedure Count()
{
  var y : int := 0;
  while (int.le(y, 9)) {
    y := int.add(y, 1);
  }
};
#end

private def countPgmAST : Core.Program := cstToAST countPgm

private def countProc : Core.Procedure := (countPgmAST.findProcByString? "Count").get!

private def countY : Core.Expression.Ident := ⟨"y", ()⟩

/-- The declared type and metadata of `y`, the loop's guard, measure, invariants
    and metadata, and the increment's right-hand side and metadata. -/
private def countParts :
    (Core.Expression.Ty × MetaData Core.Expression) ×
      (Core.Expression.Expr × Option Core.Expression.Expr ×
        List (String × Core.Expression.Expr) × MetaData Core.Expression) ×
      (Core.Expression.Expr × MetaData Core.Expression) :=
  match countProc.body with
  | .structured [Stmt.cmd (CmdExt.cmd (Cmd.init _ ty _ md0)),
      Stmt.loop (.det g) m inv [Stmt.cmd (CmdExt.cmd (Cmd.set _ (.det e) md2))] md1] =>
    ((ty, md0), (g, m, inv, md1), (e, md2))
  | _ => default

private def countSet : Core.Statement :=
  Core.Statement.set countY countParts.2.2.1 countParts.2.2.2

private def countLoop : Core.Statement :=
  .loop (.det countParts.2.1.1) countParts.2.1.2.1 countParts.2.1.2.2.1 [countSet]
    countParts.2.1.2.2.2

private def countInit : Core.Statement :=
  Core.Statement.init countY countParts.1.1 (.det (Lambda.LExpr.intConst () 0)) countParts.1.2

/-- The translated body really is the declaration followed by the loop. -/
private theorem count_body_eq : countProc.body = .structured [countInit, countLoop] := by
  native_decide

/-- `y` is declared at type `int`. -/
private theorem countTy_mono :
    countParts.1.1.toMonoType? = some (Lambda.LMonoTy.tcons "int" []) := by
  native_decide

/-- The guard is `int.le(y, 9)` in `Core.Factory`'s operator form. -/
private theorem countGuard_shape :
    countParts.2.1.1 =
      Lambda.LExpr.app () (Lambda.LExpr.app () Core.coreIntLeOpExpr
        (Lambda.LExpr.fvar () countY (some (Lambda.LMonoTy.tcons "int" []))))
        (Lambda.LExpr.const () (Lambda.LConst.intConst 9)) := by
  native_decide

/-- The increment is `int.add(y, 1)` in `Core.Factory`'s operator form. -/
private theorem countRhs_shape :
    countParts.2.2.1 =
      Lambda.LExpr.app () (Lambda.LExpr.app () Core.coreIntAddOpExpr
        (Lambda.LExpr.fvar () countY (some (Lambda.LMonoTy.tcons "int" []))))
        (Lambda.LExpr.const () (Lambda.LConst.intConst 1)) := by
  native_decide

/-- An integer literal is a value of type `int`. -/
private theorem intConst_valueOfTy (f : Core.Expression.Factory) (n : Int) :
    HasVal.valueOfTy (P := Core.Expression) f (Lambda.LExpr.intConst () n) countParts.1.1 :=
  ⟨_, Lambda.isValue_const_true _ _ _, countTy_mono,
    by simp [Lambda.LExpr.typeCheck, Lambda.LConst.ty, Lambda.LMonoTy.int]⟩

/-- With `y ↦ n`, the guard evaluates to `n ≤ 9`. -/
private theorem countGuard_eval (σ : Core.CoreStore) (n : Int)
    (hy : σ countY = some (Lambda.LExpr.intConst () n)) :
    Core.Expression.eval Core.Factory σ countParts.2.1.1
      = some (Lambda.LExpr.boolConst () (decide (n ≤ 9))) := by
  rw [countGuard_shape]
  exact Core.coreEval_intLe_numeral σ _ n
    (Lambda.evalFully_fvar_of_value Core.Factory σ () countY _ _ hy
      (Lambda.isValue_const_true _ _ _))

/-- With `y ↦ n`, the increment evaluates to `n + 1`. -/
private theorem countRhs_eval (σ : Core.CoreStore) (n : Int)
    (hy : σ countY = some (Lambda.LExpr.intConst () n)) :
    Core.Expression.eval Core.Factory σ countParts.2.2.1
      = some (Lambda.LExpr.intConst () (n + 1)) := by
  rw [countRhs_shape]
  exact Core.coreEval_intAdd_numeral σ _ n
    (Lambda.evalFully_fvar_of_value Core.Factory σ () countY _ _ hy
      (Lambda.isValue_const_true _ _ _))

section Count

variable (π : String → Option Core.Procedure)

/-- From `y ↦ n` with `n ≤ 10`, the loop finishes: by induction on the
    iterations left, `10 - n`. -/
private theorem count_loop_finishes :
    ∀ (k : Nat) (n : Int) (ρ : Env Core.Expression), (10 - n).toNat = k →
      ρ.factory = Core.Factory → ρ.store countY = some (Lambda.LExpr.intConst () n) → n ≤ 10 →
      Finishes π (fun _ => True) (.stmt countLoop ρ) := by
  intro k
  induction k with
  | zero =>
    intro n ρ hk hf hy _
    refine fin_loop_exit π ?_ trivial
    rw [hf, countGuard_eval ρ.store n hy, decide_eq_false (by omega)]
    rfl
  | succ k ih =>
    intro n ρ hk hf hy hn
    have hle : n ≤ 9 := by omega
    have hg : Core.Expression.eval ρ.factory ρ.store countParts.2.1.1 = some HasBool.tt := by
      rw [hf, countGuard_eval ρ.store n hy, decide_eq_true hle]
      rfl
    have hev : Core.Expression.eval ρ.factory ρ.store countParts.2.2.1
        = some (Lambda.LExpr.intConst () (n + 1)) := by
      rw [hf]; exact countRhs_eval ρ.store n hy
    let σ' : Core.CoreStore := fun z => if z = countY then some (Lambda.LExpr.intConst () (n + 1))
      else ρ.store z
    have hset : Finishes π
        (fun ρ₁ => ρ₁.factory = Core.Factory ∧
          ρ₁.store countY = some (Lambda.LExpr.intConst () (n + 1)))
        (.stmt countSet ρ) := by
      refine fin_cmd π ⟨σ', [], .cmd_sem (.eval_set hev
          (.update hy (ite_eq_left rfl) (fun z hz => ite_eq_right (Ne.symm hz)))
          ⟨_, _, hy, intConst_valueOfTy _ n, intConst_valueOfTy _ (n + 1)⟩
          (hf ▸ Core.coreFactory_WellFormedSemanticEval.var))⟩ ?_
      intro σ'' em hc
      cases hc with
      | cmd_sem hc' =>
        cases hc' with
        | eval_set heval hupd _ _ =>
          have hv := Option.some.inj (heval.symm.trans hev)
          cases hupd with
          | update _ hnew _ => exact ⟨hf, hv ▸ hnew⟩
    refine fin_loop_enter π hg (fin_seq π (fin_block π (fin_cons π
      (fin_seq π hset (fun _ h => fin_nil π h)))) ?_)
    rintro ρ' ⟨ρ₁, ⟨hf₁, hy₁⟩, rfl⟩
    refine fin_cons π (fin_seq π (ih (n + 1) _ (by omega) hf₁ ?_ (by omega))
      (fun _ _ => fin_nil π trivial))
    simp [projectStore, hy, hy₁]

/-- From a state where `y` is undeclared and the factory is `Core.Factory`,
    the whole body finishes. -/
private theorem count_finishes (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory)
    (hy : ρ.store countY = none) :
    Finishes π (fun _ => True) (.stmts [countInit, countLoop] ρ) := by
  have hev : Core.Expression.eval ρ.factory ρ.store (Lambda.LExpr.intConst () 0)
      = some (Lambda.LExpr.intConst () 0) :=
    Lambda.evalFully_const ρ.factory ρ.store () (Lambda.LConst.intConst 0)
  let σ' : Core.CoreStore := fun z => if z = countY then some (Lambda.LExpr.intConst () 0)
    else ρ.store z
  have hinit : Finishes π
      (fun ρ₁ => ρ₁.factory = Core.Factory ∧ ρ₁.store countY = some (Lambda.LExpr.intConst () 0))
      (.stmt countInit ρ) := by
    refine fin_cmd π ⟨σ', [], .cmd_sem (.eval_init hev
        (.init hy (ite_eq_left rfl) (fun z hz => ite_eq_right (Ne.symm hz)))
        (intConst_valueOfTy _ 0) (hf ▸ Core.coreFactory_WellFormedSemanticEval.var))⟩ ?_
    intro σ'' em hc
    cases hc with
    | cmd_sem hc' =>
      cases hc' with
      | eval_init heval hini _ _ =>
        have hv := Option.some.inj (heval.symm.trans hev)
        cases hini with
        | init _ hnew _ => exact ⟨hf, hv ▸ hnew⟩
  refine fin_cons π (fin_seq π hinit ?_)
  rintro ρ₁ ⟨hf₁, hy₁⟩
  exact fin_cons π (fin_seq π (count_loop_finishes π 10 0 ρ₁ (by decide) hf₁ hy₁
    (by decide)) (fun _ _ => fin_nil π trivial))

end Count

/-- **`var y : int := 0; while (int.le(y, 9)) { y := int.add(y, 1); }`
    terminates** from every state where `y` is undeclared and the factory is
    `Core.Factory`: every execution finishes after ten iterations. -/
theorem count_terminates (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (hy : ρ.store countY = none) :
    (Core.Logic.EventLang.coreBlock π).Terminates [countInit, countLoop] ρ :=
  (count_finishes π ρ hf hy).mustTerminate π

/-- The counting loop has no infinite run from any state where `y` is
    undeclared and the factory is `Core.Factory`. -/
theorem count_not_canDiverge (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) (hf : ρ.factory = Core.Factory) (hy : ρ.store countY = none) :
    ¬ (Core.Logic.EventLang.coreBlock π).CanDiverge
      ((Core.Logic.EventLang.coreBlock π).stmtCfg [countInit, countLoop] ρ) :=
  (EventLang.mustTerminate_iff.mp (count_terminates π ρ hf hy)).1

/-! ## A `failed` verdict

`assert [a]: false;` fails from every entry state: the two-step path into the
assertion command emits the assertion, whose condition denotes `false` in every
world. The verdict's witness is the entry state. -/

/-- The entries of a statement list: every state over `Core.Factory`, each
    running `ss` from it. -/
private def blockEntries (π : String → Option Core.Procedure) (ss : List Core.Statement) :
    ProgramEntries (fun _ : Unit => Core.Logic.EventLang.coreBlock π) where
  Program := Unit
  Entry := Env Core.Expression
  entries _ ρ := ρ.factory = Core.Factory
  start _ ρ := ⟨(), (Core.Logic.EventLang.coreBlock π).stmtCfg ss ρ⟩

private def failPgm : Program :=
#strata
program Core;

procedure Fail()
{
  assert [a]: false;
};
#end

private def failPgmAST : Core.Program := cstToAST failPgm

private def failProc : Core.Procedure := (failPgmAST.findProcByString? "Fail").get!

/-- The expression and metadata of the translated assertion. -/
private def failParts : Core.Expression.Expr × MetaData Core.Expression :=
  match failProc.body with
  | .structured [Stmt.cmd (.cmd (.assert "a" e md))] => (e, md)
  | _ => default

private def failAssert : Core.Statement := .cmd (.cmd (.assert "a" failParts.1 failParts.2))

/-- The translated body really is the single assertion. -/
private theorem fail_body_eq : failProc.body = .structured [failAssert] := by
  native_decide

/-- The asserted expression really is the literal `false`. -/
private theorem failExpr_eq :
    failParts.1 = Lambda.LExpr.const () (Lambda.LConst.boolConst false) := by
  native_decide

/-- The assertion's identifier. -/
private def failId : AssertId Core.Expression := ⟨"a", failParts.1⟩

/-- **`assert [a]: false;` has a correct `failed` verdict** in every model,
    witnessed by any entry state `ρ`. -/
theorem fail_failed (model : Lambda.Interp Core.Factory) (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) (hρ : ρ.factory = Core.Factory) :
    Strata.Analysis.VerdictCorrect (Core.Logic.DenoteBasedInterp model)
      (blockEntries π [failAssert]) () failId (.failed ρ) := by
  have hrun : (Core.Logic.EventLang.coreBlock π).ReachesWithin 2
      ((Core.Logic.EventLang.coreBlock π).stmtCfg [failAssert] ρ)
      [.assert ⟨ρ.factory, ρ.store, "a", failParts.fst, failParts.snd⟩]
      (.seq (.terminal ρ) []) :=
    .inr ⟨[], _, _, .step_admin .step_stmts_cons,
      .inr ⟨_, _, [], .step_seq_inner (.step_cmd (.cmd_sem .eval_assert)), ⟨rfl, rfl⟩,
        rfl⟩, rfl⟩
  refine ⟨hρ, 2, _, ⟨_, hrun⟩, fun hvalid => ?_⟩
  have hholds := hvalid.1 ⟨rfl, rfl⟩ (CoreHoareTestSupport.someValuation model)
    (fun _ h => by simp at h)
  rcases hholds with ⟨_, _, hd⟩ | ⟨hne, _⟩
  · revert hd
    simp only [Core.Logic.capturedExpr, failExpr_eq]
    simp [Lambda.LExpr.substFvarsFromEnv, Lambda.LMonoTy.bool, Lambda.denote_boolConst]
  · exact hne hρ

/-! ## A `valid` verdict

`assert [b]: true;` is valid in every model: every configuration a bounded path
reaches is one of five, all in the entry state, and the only event any step
emits is the assertion, whose condition is the literal `true`. -/

private def okPgm : Program :=
#strata
program Core;

procedure Ok()
{
  assert [b]: true;
};
#end

private def okPgmAST : Core.Program := cstToAST okPgm

private def okProc : Core.Procedure := (okPgmAST.findProcByString? "Ok").get!

/-- The expression and metadata of the translated assertion. -/
private def okParts : Core.Expression.Expr × MetaData Core.Expression :=
  match okProc.body with
  | .structured [Stmt.cmd (.cmd (.assert "b" e md))] => (e, md)
  | _ => default

private def okAssert : Core.Statement := .cmd (.cmd (.assert "b" okParts.1 okParts.2))

/-- The translated body really is the single assertion. -/
private theorem ok_body_eq : okProc.body = .structured [okAssert] := by
  native_decide

/-- The asserted expression really is the literal `true`. -/
private theorem okExpr_eq :
    okParts.1 = Lambda.LExpr.const () (Lambda.LConst.boolConst true) := by
  native_decide

/-- The assertion's identifier. -/
private def okId : AssertId Core.Expression := ⟨"b", okParts.1⟩

/-- The configurations a run of `assert [b]: true;` from `ρ` passes through. -/
private def OkShape (ρ : Env Core.Expression) (c : Core.CoreConfig) : Prop :=
  c = .stmts [okAssert] ρ ∨ c = .seq (.stmt okAssert ρ) [] ∨
    c = .seq (.terminal ρ) [] ∨ c = .stmts [] ρ ∨ c = .terminal ρ

/-- Every event in the list is the assertion `b`, captured in `ρ`. -/
private def OkEvents (ρ : Env Core.Expression) (trace : Trace Core.Expression) : Prop :=
  ∀ ev ∈ trace, ev = .assert ⟨ρ.factory, ρ.store, "b", okParts.1, okParts.2⟩

/-- An administrative step keeps the shape. -/
private theorem ok_admin_step {ρ : Env Core.Expression} {c c' : Core.CoreConfig}
    (hc : OkShape ρ c)
    (hs : StepStmt Core.Expression (noCommandEvalE Core.Expression Core.Command) c c') :
    OkShape ρ c' := by
  rcases hc with rfl | rfl | rfl | rfl | rfl
  · cases hs; exact .inr (.inl rfl)
  · cases hs with
    | step_seq_inner h => cases h with
      | step_cmd h => exact absurd h (by simp [noCommandEvalE])
  · cases hs with
    | step_seq_inner h => cases h
    | step_seq_done => exact .inr (.inr (.inr (.inl rfl)))
  · cases hs; exact .inr (.inr (.inr (.inr rfl)))
  · cases hs

/-- A step keeps the shape, and emits only the assertion `b`. -/
private theorem ok_step (π : String → Option Core.Procedure) {ρ : Env Core.Expression}
    {c c' : Core.CoreConfig} {emitted : Trace Core.Expression} (hc : OkShape ρ c)
    (hs : Core.CoreStepE π c emitted c') :
    OkShape ρ c' ∧ OkEvents ρ emitted := by
  cases hs with
  | step_admin h => exact ⟨ok_admin_step hc h, by simp [OkEvents]⟩
  | step_cmd h =>
    rcases hc with h' | h' | h' | h' | h' <;> cases h'
  | step_block_body h =>
    rcases hc with h' | h' | h' | h' | h' <;> cases h'
  | step_seq_inner h =>
    rcases hc with h' | h' | h' | h' | h' <;> cases h'
    · cases h with
      | step_cmd hcmd =>
        cases hcmd with
        | cmd_sem hc' =>
          cases hc'
          exact ⟨.inr (.inr (.inl rfl)), by
            intro ev hev; simpa using hev⟩
      | step_admin h =>
        cases h with
        | step_cmd h => exact absurd h (by simp [noCommandEvalE])
    · cases h with
      | step_admin h => cases h

/-- Bounded paths from a shaped configuration stay shaped and emit only the
    assertion `b`. -/
private theorem ok_reaches (π : String → Option Core.Procedure) (ρ : Env Core.Expression) :
    ∀ n {c c' : Core.CoreConfig} {trace : Trace Core.Expression}, OkShape ρ c →
      (Core.Logic.EventLang.coreBlock π).ReachesWithin n c trace c' → OkEvents ρ trace := by
  intro n
  induction n with
  | zero => rintro c c' trace _ ⟨rfl, rfl⟩; simp [OkEvents]
  | succ n ih =>
    rintro c c' trace hc (⟨rfl, rfl⟩ | ⟨emitted, c₁, rest, hs, hr, rfl⟩)
    · simp [OkEvents]
    · obtain ⟨hc₁, he⟩ := ok_step π hc hs
      intro ev hev
      rcases List.mem_append.mp hev with hev | hev
      · exact he ev hev
      · exact ih hc₁ hr ev hev

/-- On a trace of assertions `b` only, captured over `Core.Factory`, every
    occurrence of `b` holds in every world. -/
private theorem ok_valid_from (model : Lambda.Interp Core.Factory) (ρ : Env Core.Expression)
    (hρ : ρ.factory = Core.Factory) :
    ∀ (trace assumptions : Trace Core.Expression), OkEvents ρ trace →
      Trace.AssertionValidFrom Core.Expression (Core.Logic.DenoteBasedInterp model) okId
        assumptions trace
  | [], _, _ => trivial
  | ev :: rest, assumptions, h => by
    obtain rfl := h ev (List.mem_cons_self ..)
    refine ⟨fun _ _ _ => .inl ⟨hρ, ?_⟩, ok_valid_from model ρ hρ rest assumptions fun ev hev =>
      h ev (List.mem_cons_of_mem _ hev)⟩
    have hcap : Core.Logic.capturedExpr ⟨ρ.factory, ρ.store, "b", okParts.1, okParts.2⟩
        = Lambda.LExpr.const () (Lambda.LConst.boolConst true) := by
      simp [Core.Logic.capturedExpr, okExpr_eq, Lambda.LExpr.substFvarsFromEnv]
    rw [hcap]
    exact ⟨Lambda.LExpr.typeCheck_to_HasTypeA (by rfl),
      Lambda.denote_boolConst _ _ _ _ _ _⟩

/-- **`assert [b]: true;` has a correct `valid` verdict** in every model: it
    holds from every entry state. -/
theorem ok_valid (model : Lambda.Interp Core.Factory) (π : String → Option Core.Procedure) :
    Strata.Analysis.VerdictCorrect (Core.Logic.DenoteBasedInterp model)
      (blockEntries π [okAssert]) () okId .valid := by
  intro ρ hρ n trace ⟨_, hrun⟩
  exact ok_valid_from model ρ hρ _ [] (ok_reaches π ρ n (.inl rfl) hrun)

/-! ## An exit caught by its block does not finish the run

In `name: { exit name; } assert [after]: true;`, the `exit` produces an exiting
configuration nested inside the block's frame. Only a configuration that is
exiting as a whole, after the exit has left every enclosing block, is `Final`;
here the block catches the exit and the run goes on to `after`. -/

private def exitPgm : Program :=
#strata
program Core;

procedure Exit()
{
  name: {
    exit name;
  }
  assert [after]: true;
};
#end

private def exitPgmAST : Core.Program := cstToAST exitPgm

private def exitProc : Core.Procedure := (exitPgmAST.findProcByString? "Exit").get!

/-- The metadata of the exit and the block, and the trailing assertion. -/
private def exitParts : MetaData Core.Expression × MetaData Core.Expression × Core.Statement :=
  match exitProc.body with
  | .structured [Stmt.block "name" [Stmt.exit "name" mdExit] mdBlock, after] =>
    (mdExit, mdBlock, after)
  | _ => default

private def exitBlock : Core.Statement :=
  .block "name" [.exit "name" exitParts.1] exitParts.2.1

/-- The translated body really is the block followed by the assertion. -/
private theorem exit_body_eq : exitProc.body = .structured [exitBlock, exitParts.2.2] := by
  native_decide

/-- The configuration right after `exit name;` has stepped: the exit is still
    inside the block and the sequence frames around it. -/
private def afterExit (ρ : Env Core.Expression) : Core.CoreConfig :=
  .seq (.block (some "name") ρ.store (.seq (.exiting "name" ρ) [])) [exitParts.2.2]

/-- **The configuration right after `exit name;` is not final**, and so not
    finished, and it is reachable from the entry configuration. -/
theorem afterExit_reachable_not_final (π : String → Option Core.Procedure)
    (ρ : Env Core.Expression) :
    (Core.Logic.EventLang.coreBlock π).ReachesWithin 4
        ((Core.Logic.EventLang.coreBlock π).stmtCfg [exitBlock, exitParts.2.2] ρ) []
        (afterExit ρ) ∧
      ¬ (Core.Logic.EventLang.coreBlock π).Final (afterExit ρ) := by
  refine ⟨.inr ⟨[], _, [], .step_admin .step_stmts_cons,
    .inr ⟨[], _, [], .step_admin (.step_seq_inner .step_block),
    .inr ⟨[], _, [], .step_admin (.step_seq_inner (.step_block_body .step_stmts_cons)),
    .inr ⟨[], _, [], .step_admin (.step_seq_inner (.step_block_body (.step_seq_inner .step_exit))),
      ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, ?_⟩
  rintro (⟨_, h⟩ | ⟨_, _, h⟩) <;> cases h

/-- **After `exit name;`, the block catches the exit and the run reaches
    `after`**: from the configuration right after the exit, four administrative
    steps lead to the trailing assertion. -/
theorem afterExit_reaches_after (π : String → Option Core.Procedure) (ρ : Env Core.Expression) :
    (Core.Logic.EventLang.coreBlock π).ReachesWithin 4 (afterExit ρ) []
      (.seq (.stmt exitParts.2.2 { ρ with store := projectStore ρ.store ρ.store }) []) :=
  .inr ⟨[], _, [], .step_admin (.step_seq_inner (.step_block_body .step_seq_exit)),
    .inr ⟨[], _, [], .step_admin (.step_seq_inner (.step_block_exit_match rfl)),
    .inr ⟨[], _, [], .step_admin .step_seq_done,
    .inr ⟨[], _, [], .step_admin .step_stmts_cons, ⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩

end TerminationTests

end Strata
