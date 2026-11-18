/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Landing

/-!
# Expressions that let no jump out

A `jump_` leaves only a statement: `evalExprMd` and `invokeProc` are jump boundaries
(`noJ_evalExprMd`, `noJ_invokeProc`). This file proves `NoJ` for the interpreter's expression arms
that an expression-level pass rewrites (operator calls, assignments, increments and compound
assignments, variable reads) and for the helpers they use, so that a boundary around them can be
dropped (`jumpBoundary_noJ`).
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

variable (cfg : ExternalBackendM PM)

set_option hygiene false in
macro "noj_tac" : tactic => `(tactic|
  repeat' (first
    | with_reducible exact noJ_evalExprMd _ _ _
    | with_reducible exact noJ_invokeProc _ _ _ _ _ _
    | with_reducible exact noJ_checkPreconditions _ _ _ _ _
    | with_reducible exact noJ_invokeCallee _ _ _ _ _
    | with_reducible exact noJ_assignTarget _ _ _
    | with_reducible exact noJ_readForUpdate _ _ _
    | with_reducible exact noJ_varLocal _ _ _
    | with_reducible exact noJ_chargeStep
    | with_reducible exact noJ_jumpBoundary _
    | with_reducible refine NoJ.tryCatch ?_ (fun _ _ => ?_)
    | with_reducible apply NoJ.bind
    | with_reducible apply NoJ.ite
    | with_reducible apply NoJ.map
    | with_reducible apply NoJ.forM
    | with_reducible apply NoJ.mapM
    | with_reducible apply NoJ.forIn
    | with_reducible apply NoJ.withLabels
    | with_unfolding_none exact NoJ.pure _
    | exact NoJ.throw ‹_›
    | exact NoJ.throw (notJump_of trivial)
    | with_unfolding_none exact NoJ.get
    | with_unfolding_none exact NoJ.modify _
    | with_unfolding_none exact NoJ.set _
    | with_unfolding_none exact NoJ.liftM _
    | with_reducible exact NoJ.evalError _
    | with_reducible exact noJ_hostFail _
    | with_reducible exact noJ_stuckError _
    | with_reducible exact noJ_emitEvent _
    | with_reducible exact noJ_chooseValue _ _
    | with_reducible exact noJ_refuse _
    | with_reducible exact noJ_popOperand
    | with_reducible exact noJ_strictField _ _ _
    | with_reducible exact noJ_readField _ _
    | with_reducible exact noJ_writeField _ _ _
    | with_reducible exact noJ_allocateObject
    | with_reducible exact noJ_missingPrelude _ _
    | with_reducible exact noJ_noFitPrelude _ _ _
    | with_reducible exact noJ_coroInstance _ _
    | with_reducible exact noJ_assignLocal _ _
    | with_reducible exact noJ_writeUpdate _ _
    | with_reducible exact noJ_resolveOverride _ _ _
    | with_reducible exact noJ_muteE _
    | with_reducible refine fun _ => ?_
    | dsimp only
    | split
    | fail "noj_tac"))

theorem notJump_of {c : Control} (h : match c with | .jump_ .. => False | _ => True) : NotJump c := by
  intro l d e
  subst e
  exact h

theorem noJ_hostFail (msg : String) : NoJ (hostFail msg : EvalM PM α) := by
  unfold hostFail; exact NoJ.liftM _

theorem noJ_stuckError (msg : String) : NoJ (stuckError msg : EvalM PM α) := by
  unfold stuckError; exact NoJ.liftM _

theorem noJ_emitEvent (e : Event) : NoJ (emitEvent e : EvalM PM Unit) := by
  unfold emitEvent; exact NoJ.liftM _

theorem noJ_chooseValue (ty : Option HighType) (d : Value) : NoJ (chooseValue ty d : EvalM PM Value) := by
  unfold chooseValue; exact NoJ.liftM _

theorem noJ_refuse (msg : String) : NoJ (refuse msg : EvalM PM α) := by
  unfold refuse; noj_tac

theorem noJ_popOperand : NoJ (popOperand : EvalM PM Value) := by
  unfold popOperand; noj_tac

theorem noJ_strictField (target : Value) (field : Identifier) : NoJ (strictField cfg target field : EvalM PM Unit) := by
  unfold strictField; noj_tac

theorem noJ_readField (target : Value) (name : String) : NoJ (readField target name : EvalM PM Value) := by
  unfold readField; noj_tac

theorem noJ_writeField (target : Value) (name : String) (v : Value) : NoJ (writeField target name v : EvalM PM Unit) := by
  unfold writeField; noj_tac

theorem noJ_allocateObject : NoJ (allocateObject : EvalM PM Value) := by
  unfold allocateObject; noj_tac

theorem noJ_missingPrelude (name : String) (args : List Value) : NoJ (missingPrelude name args : EvalM PM Unit) := by
  unfold missingPrelude; noj_tac

theorem noJ_noFitPrelude (index : ProgramIndex) (op : Operation) (args : List Value) :
    NoJ (noFitPrelude index op args : EvalM PM Unit) := by
  unfold noFitPrelude; noj_tac

theorem noJ_coroInstance (v : Value) (what : String) : NoJ (coroInstance v what : EvalM PM (Nat × CoroState)) := by
  unfold coroInstance; noj_tac

theorem noJ_assignLocal (name : Identifier) (v : Value) : NoJ (assignLocal name v : EvalM PM Unit) := by
  unfold assignLocal; noj_tac

theorem noJ_writeUpdate (u : UpdateTarget) (v : Value) : NoJ (writeUpdate u v : EvalM PM Unit) := by
  unfold writeUpdate; noj_tac

theorem noJ_resolveOverride (target : Value) (id : Nat) (static : Procedure) :
    NoJ (resolveOverride target id static : EvalM PM Procedure) := by
  unfold resolveOverride; noj_tac

theorem noJ_muteE {x : EvalM PM α} (hx : NoJ x) : NoJ (muteE x) := by
  intro σ τ l d σ1 τ1 h
  rw [run_muteE] at h
  rcases hr : run x { σ with muted := true } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · simp [muteR] at h
  · simp only [muteR, Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact hx _ _ _ _ _ _ hr
  · simp [muteR] at h

theorem noJ_varLocal (m : Nat) (x : Identifier) : NoJ (evalExpr cfg m (.Var (.Local x))) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

theorem noJ_checkPreconditions (m : Nat) (site : FileRange) (P : Procedure) (args : List Value) :
    NoJ (checkPreconditions cfg m site P args) := by
  cases m with
  | zero => rw [checkPreconditions]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [checkPreconditions]; noj_tac

theorem noJ_invokeCallee (m : Nat) (site : FileRange) (c : Identifier) (args : List Value) :
    NoJ (invokeCallee cfg m site c args) := by
  cases m with
  | zero => rw [invokeCallee]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [invokeCallee]; noj_tac

theorem noJ_assignTarget (m : Nat) (t : Variable) : NoJ (assignTarget cfg m t) := by
  cases m with
  | zero => rw [assignTarget]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [assignTarget]; noj_tac

theorem noJ_readForUpdate (m : Nat) (t : Variable) : NoJ (readForUpdate cfg m t) := by
  cases m with
  | zero => rw [readForUpdate]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [readForUpdate]; noj_tac

set_option maxHeartbeats 4000000 in
/-- A call without a receiver lets no `jump_` out. -/
theorem noJ_callNone (m : Nat) (c : Identifier) (args : List StmtExprMd) (ta : List HighTypeMd) :
    NoJ (evalExpr cfg m (.Call none c args ta)) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

set_option maxHeartbeats 4000000 in
/-- A single assignment in expression position lets no `jump_` out. -/
theorem noJ_assign1 (m : Nat) (t : VariableMd) (v : StmtExprMd) : NoJ (evalExpr cfg m (.Assign [t] v)) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

theorem noJ_incrDecr (m : Nat) (mode : IncrDecrMode) (o : IncrDecrOp) (t : VariableMd) :
    NoJ (evalExpr cfg m (.IncrDecr mode o t)) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

theorem noJ_compoundAssign (m : Nat) (op : Operation) (t : VariableMd) (R : StmtExprMd) :
    NoJ (evalExpr cfg m (.CompoundAssign op t R)) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

theorem noJ_varField (m : Nat) (t : StmtExprMd) (f : Identifier) : NoJ (evalExpr cfg m (.Var (.Field t f))) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; noj_tac

theorem noJ_literalInt (m : Nat) (i : Int) : NoJ (evalExpr cfg m (.LiteralInt i)) := by
  cases m with
  | zero => rw [evalExpr]; exact NoJ.throw (fun _ _ h => by cases h)
  | succ m => simp only [evalExpr]; exact NoJ.pure _

end Strata.Laurel.PassSemantics
