/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Host

/-!
# Fuel monotonicity of the Laurel interpreter

`monoAt : ∀ n, MonoAt cfg n`: each of the interpreter's 22 mutual functions satisfies
`Le (f n …) (f (n + 1) …)`, for every external backend `cfg`. It is one induction on
`n`; each `step_*` lemma unfolds one function and closes the goal with `mono_real`.

The `While` arm and the expression cases are split by hand: unfolding only the
outermost call (`conv`) and treating one constructor at a time keeps elaboration within
bounds, where `simp only [evalStmt]` would also unfold the inner calls.

Monotonicity needs the interpreter's `try` to skip `finally` when it runs out of fuel;
see `evalStmt`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

variable (cfg : ExternalBackendM PM)

theorem withBlockScope_le {stmts : List StmtExprMd} {x y : EvalM PM α} (h : Le x y) :
    Le (withBlockScope stmts x) (withBlockScope stmts y) := by
  unfold withBlockScope
  mono_tac

theorem withLabels_le {f : List String → List String} {x y : EvalM PM α} (h : Le x y) :
    Le (withLabels f x) (withLabels f y) := by
  unfold withLabels
  mono_tac

theorem jumpBoundary_le {x y : EvalM PM α} (h : Le x y) : Le (jumpBoundary x) (jumpBoundary y) := by
  unfold jumpBoundary
  mono_tac

theorem withOpenLabel_le {l : String} {x y : EvalM PM α} (h : Le x y) :
    Le (withOpenLabel l x) (withOpenLabel l y) :=
  withLabels_le h

theorem withOperandWindow_le {s : StmtExprMd} {x y : EvalM PM α} (h : Le x y) :
    Le (withOperandWindow s x) (withOperandWindow s y) := by
  simp only [withOperandWindow]
  mono_tac

theorem preconditionValue_le {ev ev' : StmtExprMd → EvalM PM Value} (h : ∀ e, Le (ev e) (ev' e))
    (p : Procedure) (a : List Value) :
    Le (preconditionValue cfg ev p a) (preconditionValue cfg ev' p a) := by
  simp only [preconditionValue]
  mono_tac
  all_goals exact h _

structure MonoAt (n : Nat) : Prop where
  scoped_ : ∀ s, Le (evalScopedStmt cfg n s) (evalScopedStmt cfg (n + 1) s)
  exprMd : ∀ e, Le (evalExprMd cfg n e) (evalExprMd cfg (n + 1) e)
  expr : ∀ e, Le (evalExpr cfg n e) (evalExpr cfg (n + 1) e)
  assign : ∀ t, Le (assignTarget cfg n t) (assignTarget cfg (n + 1) t)
  update : ∀ t, Le (readForUpdate cfg n t) (readForUpdate cfg (n + 1) t)
  stmt : ∀ s, Le (evalStmt cfg n s) (evalStmt cfg (n + 1) s)
  iter : ∀ c b p ci ci' eb eb', Le ci ci' → Le eb eb' →
    Le (evalWhileIter cfg c b p ci eb n) (evalWhileIter cfg c b p ci' eb' (n + 1))
  blockLoop : ∀ ss l invs base, Le (evalBlockLoop cfg n ss l invs base) (evalBlockLoop cfg (n + 1) ss l invs base)
  blockFrom : ∀ ss bl invs k l d,
    Le (evalBlockFrom cfg n ss bl invs k l d) (evalBlockFrom cfg (n + 1) ss bl invs k l d)
  stmtFrom : ∀ s l d, Le (evalStmtFrom cfg n s l d) (evalStmtFrom cfg (n + 1) s l d)
  runFrom : ∀ ss k l d, Le (runFrom cfg n ss k l d) (runFrom cfg (n + 1) ss k l d)
  fin : ∀ f i b k, Le (runTryFinally cfg n f i b k) (runTryFinally cfg (n + 1) f i b k)
  finish : ∀ f i b k c, Le (finishCatchClause cfg n f i b k c) (finishCatchClause cfg (n + 1) f i b k c)
  clauses : ∀ f i b k v j cs,
    Le (tryCatchClauses cfg n f i b k v j cs) (tryCatchClauses cfg (n + 1) f i b k v j cs)
  go : ∀ a b s i k ss, Le (evalStmtListGo cfg n a b s i k ss) (evalStmtListGo cfg (n + 1) a b s i k ss)
  list : ∀ ss a, Le (evalStmtList cfg n ss a) (evalStmtList cfg (n + 1) ss a)
  resume : ∀ t v, Le (resumeCoroutine cfg n t v) (resumeCoroutine cfg (n + 1) t v)
  outputs : ∀ e, Le (evalCallOutputs cfg n e) (evalCallOutputs cfg (n + 1) e)
  callee : ∀ s c a, Le (invokeCallee cfg n s c a) (invokeCallee cfg (n + 1) s c a)
  pre : ∀ s p a, Le (checkPreconditions cfg n s p a) (checkPreconditions cfg (n + 1) s p a)
  post : ∀ p ps fr e x y r,
    Le (checkPostconditions cfg n p ps fr e x y r) (checkPostconditions cfg (n + 1) p ps fr e x y r)
  proc : ∀ s p a, Le (invokeProc cfg n s p a) (invokeProc cfg (n + 1) s p a)

theorem oof_le (y : EvalM PM α) : Le (throw .outOfFuel) y := ⟨fun _ _ h => absurd trivial h⟩

set_option hygiene false in
macro "mono_real" : tactic => `(tactic|
  repeat' (first
    | with_reducible exact oof_le _
    | with_reducible exact Le.refl _
    | with_reducible assumption
    | with_reducible exact ih.scoped_ _
    | with_reducible exact ih.exprMd _
    | with_reducible exact ih.expr _
    | with_reducible exact ih.assign _
    | with_reducible exact ih.update _
    | with_reducible exact ih.stmt _
    | with_reducible (apply ih.iter <;> assumption)
    | with_reducible exact ih.blockLoop _ _ _ _
    | with_reducible exact ih.blockFrom _ _ _ _ _ _
    | with_reducible exact ih.stmtFrom _ _ _
    | with_reducible exact ih.runFrom _ _ _ _
    | with_reducible exact ih.fin _ _ _ _
    | with_reducible exact ih.finish _ _ _ _ _
    | with_reducible exact ih.clauses _ _ _ _ _ _ _
    | with_reducible exact ih.go _ _ _ _ _ _
    | with_reducible exact ih.list _ _
    | with_reducible exact ih.resume _ _
    | with_reducible exact ih.outputs _
    | with_reducible exact ih.callee _ _ _
    | with_reducible exact ih.pre _ _ _
    | with_reducible exact ih.post _ _ _ _ _ _ _
    | with_reducible exact ih.proc _ _ _
    | with_reducible apply jumpBoundary_le
    | ((with_reducible show KeepsOOF _); keeps_oof)
    | with_reducible apply muteSel_le
    | with_reducible apply muteE_le
    | with_reducible refine tryCatch_le ?_ ?_ ?_
    | with_reducible apply bind_le
    | with_reducible apply ite_le
    | with_reducible apply map_le
    | apply forM_le
    | apply mapM_le
    | apply forIn_le
    | apply arrayMapM_le
    | apply withBlockScope_le
    | apply withLabels_le
    | apply withOpenLabel_le
    | apply withOperandWindow_le
    | apply preconditionValue_le
    | refine fun _ => ?_
    | (dsimp only; done)
    | dsimp only
    | split
    | (injections; subst_vars)
    | (exfalso; omega)))

set_option maxHeartbeats 4000000 in
/-- `evalScopedStmt` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_scoped_ {n : Nat} (ih : MonoAt cfg n) :
    ∀ s, Le (evalScopedStmt cfg (n + 1) s) (evalScopedStmt cfg (n + 1 + 1) s) := by
  intro s; simp only [evalScopedStmt]; mono_real

set_option maxHeartbeats 4000000 in
/-- `evalExprMd` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_exprMd {n : Nat} (ih : MonoAt cfg n) :
    ∀ e, Le (evalExprMd cfg (n + 1) e) (evalExprMd cfg (n + 1 + 1) e) := by
  intro e; simp only [evalExprMd]; mono_real

set_option maxHeartbeats 4000000 in
/-- `evalExpr` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_expr {n : Nat} (ih : MonoAt cfg n) :
    ∀ e, Le (evalExpr cfg (n + 1) e) (evalExpr cfg (n + 1 + 1) e) := by
  intro e
  cases e
  case Block stmts label invs dec =>
    cases label <;> (simp only [evalExpr]; mono_real)
  case ContractOf ty f =>
    rcases f with ⟨fv, fs⟩
    cases ty
    case Precondition =>
      cases fv
      case Call r callee args ta => cases r <;> (simp only [evalExpr]; mono_real)
      all_goals (simp only [evalExpr]; mono_real)
    all_goals (simp only [evalExpr]; mono_real)
  case Call r callee args ta => cases r <;> (simp only [evalExpr]; mono_real)
  all_goals (try (rename_i v; cases v))
  all_goals (simp only [evalExpr]; mono_real)

set_option maxHeartbeats 4000000 in
/-- `assignTarget` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_assign {n : Nat} (ih : MonoAt cfg n) :
    ∀ t, Le (assignTarget cfg (n + 1) t) (assignTarget cfg (n + 1 + 1) t) := by
  intro t; simp only [assignTarget]; mono_real

set_option maxHeartbeats 4000000 in
/-- `readForUpdate` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_update {n : Nat} (ih : MonoAt cfg n) :
    ∀ t, Le (readForUpdate cfg (n + 1) t) (readForUpdate cfg (n + 1 + 1) t) := by
  intro t; simp only [readForUpdate]; mono_real

set_option maxHeartbeats 4000000 in
/-- `evalStmt` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_stmt {n : Nat} (ih : MonoAt cfg n) :
    ∀ s, Le (evalStmt cfg (n + 1) s) (evalStmt cfg (n + 1 + 1) s) := by
  intro s
  rcases s with ⟨v, src⟩
  cases v
  case While c invs dec body p =>
    (conv => lhs; rw [evalStmt]); (conv => rhs; rw [evalStmt]); dsimp only
    repeat' (first
      | with_reducible exact Le.refl _
      | with_reducible exact ih.stmt _
      | with_reducible exact ih.scoped_ _
      | with_reducible apply ih.iter
      | with_reducible apply bind_le
      | with_reducible apply ite_le
      | with_reducible apply forIn_le
      | refine fun _ => ?_
      | split)
  case Block stmts label invs dec =>
    cases label
    · simp only [evalStmt]; mono_real
    · (conv => lhs; rw [evalStmt]); (conv => rhs; rw [evalStmt]); dsimp only
      mono_real
  case Call r callee args ta => cases r <;> (simp only [evalStmt]; mono_real)
  all_goals (try (rename_i x; cases x))
  all_goals (simp only [evalStmt]; mono_real)

set_option maxHeartbeats 4000000 in
/-- `evalBlockLoop` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_blockLoop {n : Nat} (ih : MonoAt cfg n) :
    ∀ ss l invs base, Le (evalBlockLoop cfg (n + 1) ss l invs base) (evalBlockLoop cfg (n + 1 + 1) ss l invs base) := by
  intro ss l invs base; rw [evalBlockLoop, evalBlockLoop]; mono_real

set_option maxHeartbeats 4000000 in
/-- `evalBlockFrom` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_blockFrom {n : Nat} (ih : MonoAt cfg n) :
    ∀ ss bl invs k l d,
    Le (evalBlockFrom cfg (n + 1) ss bl invs k l d) (evalBlockFrom cfg (n + 1 + 1) ss bl invs k l d) := by
  intro ss bl invs k l d
  unfold evalBlockFrom
  dsimp only
  mono_real

set_option maxHeartbeats 4000000 in
/-- `evalStmtFrom` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_stmtFrom {n : Nat} (ih : MonoAt cfg n) :
    ∀ s l d, Le (evalStmtFrom cfg (n + 1) s l d) (evalStmtFrom cfg (n + 1 + 1) s l d) := by
  intro s l d
  rcases s with ⟨v, src⟩
  cases v
  case Block stmts bl invs dec =>
    unfold evalStmtFrom
    dsimp only
    mono_real
  case IfThenElse c th el =>
    unfold evalStmtFrom
    dsimp only
    mono_real
  all_goals
    unfold evalStmtFrom
    dsimp only
    mono_real

set_option maxHeartbeats 4000000 in
/-- `runFrom` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_runFrom {n : Nat} (ih : MonoAt cfg n) :
    ∀ ss k l d, Le (runFrom cfg (n + 1) ss k l d) (runFrom cfg (n + 1 + 1) ss k l d) := by
  intro ss k l d
  unfold runFrom
  dsimp only
  mono_real

set_option maxHeartbeats 4000000 in
/-- `evalWhileIter` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_iter {n : Nat} (ih : MonoAt cfg n) :
    ∀ c b p ci ci' eb eb', Le ci ci' → Le eb eb' →
    Le (evalWhileIter cfg c b p ci eb (n + 1)) (evalWhileIter cfg c b p ci' eb' (n + 1 + 1)) := by
  intro c b p ci ci' eb eb' hci heb; rw [evalWhileIter, evalWhileIter]; mono_real

set_option maxHeartbeats 4000000 in
/-- `runTryFinally` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_fin {n : Nat} (ih : MonoAt cfg n) :
    ∀ f i b k, Le (runTryFinally cfg (n + 1) f i b k) (runTryFinally cfg (n + 1 + 1) f i b k) := by
  intro f i b k; simp only [runTryFinally]; mono_real

set_option maxHeartbeats 4000000 in
/-- `finishCatchClause` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_finish {n : Nat} (ih : MonoAt cfg n) :
    ∀ f i b k c, Le (finishCatchClause cfg (n + 1) f i b k c) (finishCatchClause cfg (n + 1 + 1) f i b k c) := by
  intro f i b k c; simp only [finishCatchClause]; mono_real

set_option maxHeartbeats 4000000 in
/-- `tryCatchClauses` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_clauses {n : Nat} (ih : MonoAt cfg n) :
    ∀ f i b k v j cs,
    Le (tryCatchClauses cfg (n + 1) f i b k v j cs) (tryCatchClauses cfg (n + 1 + 1) f i b k v j cs) := by
  intro f i b k v j cs
  cases cs <;> simp only [tryCatchClauses] <;> mono_real

set_option maxHeartbeats 4000000 in
/-- `evalStmtListGo` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_go {n : Nat} (ih : MonoAt cfg n) :
    ∀ a b s i k ss, Le (evalStmtListGo cfg (n + 1) a b s i k ss) (evalStmtListGo cfg (n + 1 + 1) a b s i k ss) := by
  intro a b s i k ss
  cases ss <;> simp only [evalStmtListGo] <;> mono_real

set_option maxHeartbeats 4000000 in
/-- `evalStmtList` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_list {n : Nat} (ih : MonoAt cfg n) :
    ∀ ss a, Le (evalStmtList cfg (n + 1) ss a) (evalStmtList cfg (n + 1 + 1) ss a) := by
  intro ss a; simp only [evalStmtList]; mono_real

set_option maxHeartbeats 4000000 in
/-- `resumeCoroutine` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_resume {n : Nat} (ih : MonoAt cfg n) :
    ∀ t v, Le (resumeCoroutine cfg (n + 1) t v) (resumeCoroutine cfg (n + 1 + 1) t v) := by
  intro t v; simp only [resumeCoroutine]; mono_real

set_option maxHeartbeats 4000000 in
/-- `evalCallOutputs` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_outputs {n : Nat} (ih : MonoAt cfg n) :
    ∀ e, Le (evalCallOutputs cfg (n + 1) e) (evalCallOutputs cfg (n + 1 + 1) e) := by
  intro e; simp only [evalCallOutputs]; mono_real

set_option maxHeartbeats 4000000 in
/-- `invokeCallee` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_callee {n : Nat} (ih : MonoAt cfg n) :
    ∀ s c a, Le (invokeCallee cfg (n + 1) s c a) (invokeCallee cfg (n + 1 + 1) s c a) := by
  intro s c a; simp only [invokeCallee]; mono_real

set_option maxHeartbeats 4000000 in
/-- `checkPreconditions` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_pre {n : Nat} (ih : MonoAt cfg n) :
    ∀ s p a, Le (checkPreconditions cfg (n + 1) s p a) (checkPreconditions cfg (n + 1 + 1) s p a) := by
  intro s p a; simp only [checkPreconditions]; mono_real

set_option maxHeartbeats 4000000 in
/-- `checkPostconditions` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_post {n : Nat} (ih : MonoAt cfg n) :
    ∀ p ps fr e x y r,
    Le (checkPostconditions cfg (n + 1) p ps fr e x y r) (checkPostconditions cfg (n + 1 + 1) p ps fr e x y r) := by
  intro p ps fr e x y r; simp only [checkPostconditions]; mono_real

set_option maxHeartbeats 16000000 in
/-- `invokeProc` is monotone in its fuel at `n + 1`, given `MonoAt cfg n`. -/
theorem step_proc {n : Nat} (ih : MonoAt cfg n) :
    ∀ s p a, Le (invokeProc cfg (n + 1) s p a) (invokeProc cfg (n + 1 + 1) s p a) := by
  intro s p a; simp only [invokeProc]; mono_real

/-- Fuel monotonicity of the interpreter: for every backend `cfg` and every fuel `n`, each of the
interpreter's mutual functions run with fuel `n + 1` gives exactly the result of the run with fuel
`n` whenever that run does not run out of fuel (`Le`). -/
theorem monoAt : ∀ n, MonoAt cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> first
        | (rw [evalExpr]; exact oof_le _)
        | (rw [evalStmt]; exact oof_le _)
        | (rw [evalWhileIter]; exact oof_le _)
        | (rw [evalBlockLoop]; exact oof_le _)
        | (simp only [evalScopedStmt, evalExprMd, assignTarget, readForUpdate, evalBlockFrom, evalStmtFrom, runFrom,
            runTryFinally,
            finishCatchClause, tryCatchClauses, evalStmtListGo, evalStmtList, resumeCoroutine,
            evalCallOutputs, invokeCallee, checkPreconditions, checkPostconditions, invokeProc]
           exact oof_le _)
  | n + 1 => by
    have ih := monoAt n
    exact ⟨step_scoped_ cfg ih, step_exprMd cfg ih, step_expr cfg ih, step_assign cfg ih, step_update cfg ih, step_stmt cfg ih, step_iter cfg ih, step_blockLoop cfg ih, step_blockFrom cfg ih, step_stmtFrom cfg ih, step_runFrom cfg ih, step_fin cfg ih, step_finish cfg ih, step_clauses cfg ih, step_go cfg ih, step_list cfg ih, step_resume cfg ih, step_outputs cfg ih, step_callee cfg ih, step_pre cfg ih, step_post cfg ih, step_proc cfg ih⟩

end Strata.Laurel.PassSemantics
