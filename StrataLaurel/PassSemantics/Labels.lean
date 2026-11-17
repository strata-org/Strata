/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Sim

/-!
# The Laurel interpreter keeps the open labels

`openLabels_at : ∀ n, KeepsAt cfg n`: each of the interpreter's mutual functions, run with
fuel `n`, leaves `EvalState.openLabels` as it found it, whether it finishes or leaves by a
signal. A labelled block opens its label for the statements it runs and closes it again on
every way out (`withLabels`), so a statement or an expression does not change which blocks
are open around it. Pass proofs use this for a block the pass adds around code it rewrites:
the jump that leaves the block finds it open after running statements of the original
program, which the simulation relation does not describe.

`OLKeep o x` says that whenever `x` starts with the open labels `o` and returns, with a value or
with a signal, it ends with them. `KeepsOL x` says this for every `o`. The combinator lemmas
`OLKeep.bind`, `OLKeep.tryCatch` and so on are proved first, then the proof is one induction on
`n` as in `RealMono.lean`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

/-- When `x` starts with the open labels `o` and returns, with a value or with a control signal, it ends with
them. -/
structure OLKeep (o : List String) (x : EvalM PM α) : Prop where
  keep : ∀ σ τ r σ1 τ1, σ.openLabels = o → run x σ τ = .ok ((r, σ1), τ1) → σ1.openLabels = o

/-- `x` leaves the open labels as it found them, whatever they were. -/
@[reducible] def KeepsOL (x : EvalM PM α) : Prop := ∀ o, OLKeep o x

theorem OLKeep.pure {o : List String} (a : α) : OLKeep o (pure a : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem OLKeep.throw {o : List String} (c : Control) : OLKeep o (throw c : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_throw] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem OLKeep.get {o : List String} : OLKeep o (MonadState.get : EvalM PM EvalState) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_get] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem OLKeep.set {o : List String} (σ' : EvalState) (hσ' : σ'.openLabels = o) :
    OLKeep o (MonadStateOf.set σ' : EvalM PM PUnit) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    have e : run (MonadStateOf.set σ' : EvalM PM PUnit) σ τ = .ok ((.ok (), σ'), τ) := rfl
    rw [e] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ'⟩

theorem OLKeep.modify {o : List String} {f : EvalState → EvalState} (hf : ∀ σ, σ.openLabels = o → (f σ).openLabels = o) :
    OLKeep o (_root_.modify f : EvalM PM PUnit) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_modify] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hf σ hσ⟩

theorem OLKeep.liftM {o : List String} (x : PM α) : OLKeep o (liftM x : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_lift] at h
    rcases hx : x τ with e | ⟨a, τ'⟩ <;> rw [hx] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact hσ⟩

/-- `bind` keeps the open labels if both parts do. -/
theorem OLKeep.bind {o : List String} {x : EvalM PM α} {f : α → EvalM PM β} (hx : OLKeep o x)
    (hf : ∀ a, OLKeep o (f a)) : OLKeep o (x >>= f) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx.keep _ _ _ _ _ hσ hr
  · exact (hf a).keep _ _ _ _ _ (hx.keep _ _ _ _ _ hσ hr) h

/-- `get` followed by an action that keeps the open labels when they are those of the state read keeps the
open labels. -/
theorem OLKeep.getBind {o : List String} {f : EvalState → EvalM PM β} (hf : ∀ s, s.openLabels = o → OLKeep o (f s)) :
    OLKeep o (MonadState.get >>= f) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_bind, run_get] at h
  exact (hf σ hσ).keep _ _ _ _ _ hσ h

/-- `tryCatch` keeps the open labels if the body and every handler do. -/
theorem OLKeep.tryCatch {o : List String} {x : EvalM PM α} {h : Control → EvalM PM α} (hx : OLKeep o x)
    (hh : ∀ c, OLKeep o (h c)) : OLKeep o (MonadExcept.tryCatch x h) := by
  refine ⟨fun σ τ r σ1 τ1 hσ he => ?_⟩
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact (hh c).keep _ _ _ _ _ (hx.keep _ _ _ _ _ hσ hr) he
  · simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, -⟩ := he
    exact hx.keep _ _ _ _ _ hσ hr

theorem OLKeep.ite {o : List String} {c : Prop} [Decidable c] {x y : EvalM PM α} (hx : OLKeep o x) (hy : OLKeep o y) :
    OLKeep o (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem OLKeep.map {o : List String} {x : EvalM PM α} (f : α → β) (hx : OLKeep o x) : OLKeep o (f <$> x) := by
  simp only [map_eq_pure_bind]
  exact hx.bind (fun _ => OLKeep.pure _)

theorem OLKeep.forM {o : List String} {l : List β} {f : β → EvalM PM PUnit} (h : ∀ b, OLKeep o (f b)) :
    OLKeep o (l.forM f) := by
  induction l with
  | nil => exact OLKeep.pure _
  | cons b bs ih => exact (h b).bind (fun _ => ih)

theorem OLKeep.mapM {o : List String} {l : List β} {f : β → EvalM PM γ} (h : ∀ b, OLKeep o (f b)) :
    OLKeep o (l.mapM f) := by
  induction l with
  | nil => exact OLKeep.pure _
  | cons b bs ih =>
    simp only [List.mapM_cons]
    exact (h b).bind (fun _ => ih.bind (fun _ => OLKeep.pure _))

theorem OLKeep.forIn {o : List String} {l : List β} {b : γ} {f : β → γ → EvalM PM (ForInStep γ)}
    (h : ∀ x c, OLKeep o (f x c)) : OLKeep o (forIn l b f) := by
  induction l generalizing b with
  | nil => exact OLKeep.pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine (h x b).bind (fun r => ?_)
    cases r with
    | done c => exact OLKeep.pure _
    | yield c => exact ih

theorem OLKeep.arrayMapM {o : List String} {l : Array β} {f : β → EvalM PM γ} (h : ∀ b, OLKeep o (f b)) :
    OLKeep o (l.mapM f) := by
  simp only [Array.mapM_eq_mapM_toList, Functor.map]
  exact (OLKeep.mapM h).bind (fun _ => OLKeep.pure _)

theorem OLKeep.muteE {o : List String} {x : EvalM PM α} (hx : OLKeep o x) : OLKeep o (Interpreter.muteE x) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_muteE] at h
  rcases hr : run x { σ with muted := true } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · simp [muteR] at h
  · simp only [muteR, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    have := hx.keep { σ with muted := true } _ _ _ _ hσ hr
    exact this
  · simp only [muteR, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    have := hx.keep { σ with muted := true } _ _ _ _ hσ hr
    exact this

theorem OLKeep.muteSel {o : List String} {c : Prop} [Decidable c] {x : EvalM PM α} (hx : OLKeep o x) :
    OLKeep o ((if c then Interpreter.muteE else id) x) := by
  split
  · exact hx.muteE
  · exact hx

/-- `withLabels` keeps the open labels whatever it runs, since it restores the labels open on entry on
every way out. -/
theorem OLKeep.withLabels {o : List String} (f : List String → List String) (x : EvalM PM α) :
    OLKeep o (Interpreter.withLabels f x) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  unfold Interpreter.withLabels at h
  simp only [run_bind, run_get, run_modify, run_tryCatch] at h
  rcases hr : run x { σ with openLabels := f σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h <;>
    simp only [run_throw, run_pure, Except.ok.injEq, Prod.mk.injEq] at h
  · cases h
  · obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ
  · obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ

/-- Running `withLabels f x` runs `x` with the open labels replaced by `f` of them, and puts the labels open
on entry back into the state it ends in, whether `x` returned a value or a signal. -/
theorem run_withLabels (f : List String → List String) (x : EvalM PM α) (σ : EvalState) (τ : Trace) :
    run (Interpreter.withLabels f x) σ τ = match run x { σ with openLabels := f σ.openLabels } τ with
      | .error e => .error e
      | .ok ((r, σ1), τ1) => .ok ((r, { σ1 with openLabels := σ.openLabels }), τ1) := by
  unfold Interpreter.withLabels
  simp only [run_bind, run_get, run_modify, run_tryCatch]
  rcases run x { σ with openLabels := f σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;>
    simp only [run_throw, run_pure]

theorem run_withOpenLabel (l : String) (x : EvalM PM α) (σ : EvalState) (τ : Trace) :
    run (Interpreter.withOpenLabel l x) σ τ = match run x { σ with openLabels := l :: σ.openLabels } τ with
      | .error e => .error e
      | .ok ((r, σ1), τ1) => .ok ((r, { σ1 with openLabels := σ.openLabels }), τ1) :=
  run_withLabels (l :: ·) x σ τ

theorem OLKeep.withOpenLabel {o : List String} (l : String) (x : EvalM PM α) :
    OLKeep o (Interpreter.withOpenLabel l x) :=
  OLKeep.withLabels _ x

set_option hygiene false in
macro "keep_tac" : tactic => `(tactic|
  repeat' (first
    | with_reducible apply OLKeep.jumpBoundary
    | with_reducible apply OLKeep.muteSel
    | with_reducible apply OLKeep.muteE
    | with_reducible refine OLKeep.tryCatch ?_ ?_
    | with_reducible apply OLKeep.getBind
    | with_reducible apply OLKeep.bind
    | with_reducible apply OLKeep.ite
    | with_reducible apply OLKeep.map
    | with_reducible apply OLKeep.forM
    | with_reducible apply OLKeep.mapM
    | with_reducible apply OLKeep.forIn
    | with_reducible apply OLKeep.arrayMapM
    | with_reducible apply OLKeep.withBlockScope
    | with_reducible apply OLKeep.withOperandWindow
    | with_unfolding_none exact OLKeep.pure _
    | with_unfolding_none exact OLKeep.throw _
    | with_unfolding_none exact OLKeep.get
    | with_reducible assumption
    | with_reducible exact hev _
    | with_reducible exact ih.exprMd
    | with_reducible exact ih.scoped_ _ _
    | with_reducible exact ih.exprMd _ _
    | with_reducible exact ih.expr _ _
    | with_reducible exact ih.assign _ _
    | with_reducible exact ih.update _ _
    | with_reducible exact ih.stmt _ _
    | with_reducible refine ih.iter _ _ _ _ _ ?_ ?_ _
    | with_reducible exact ih.blockLoop _ _ _ _ _
    | with_reducible exact ih.blockFrom _ _ _ _ _ _ _
    | with_reducible exact ih.stmtFrom _ _ _ _
    | with_reducible exact ih.runFrom _ _ _ _ _
    | with_reducible exact ih.fin _ _ _ _ _
    | with_reducible exact ih.finish _ _ _ _ _ _
    | with_reducible exact ih.clauses _ _ _ _ _ _ _ _
    | with_reducible exact ih.go _ _ _ _ _ _ _
    | with_reducible exact ih.list _ _ _
    | with_reducible exact ih.resume _ _ _
    | with_reducible exact ih.outputs _ _
    | with_reducible exact ih.callee _ _ _ _
    | with_reducible exact ih.pre _ _ _ _
    | with_reducible exact ih.post _ _ _ _ _ _ _ _
    | with_reducible exact ih.proc _ _ _ _
    | with_unfolding_none exact OLKeep.liftM _
    | with_unfolding_none exact OLKeep.withLabels _ _
    | with_unfolding_none exact OLKeep.withOpenLabel _ _
    | with_unfolding_none refine OLKeep.modify (fun σ hσ => ?_)
    | with_unfolding_none refine OLKeep.set _ ?_
    | refine fun _ => ?_
    | dsimp only
    | split
    | with_reducible exact keeps_hostFail _ _
    | with_reducible exact keeps_evalError _ _
    | with_reducible exact keeps_refuse _ _
    | with_reducible exact keeps_stuckError _ _
    | with_reducible exact keeps_chargeStep _
    | with_reducible exact keeps_enterChild _ _ _ _
    | with_reducible exact keeps_chargeIteration _ _
    | with_reducible exact keeps_emitEvent _ _
    | with_reducible exact keeps_chooseValue _ _ _
    | with_reducible exact keeps_popOperand _
    | with_reducible exact keeps_missingPrelude _ _ _
    | with_reducible exact keeps_noFitPrelude _ _ _ _
    | with_reducible exact keeps_strictField _ _ _
    | with_reducible exact keeps_allocateObject _
    | with_reducible exact keeps_readField _ _ _
    | with_reducible exact keeps_writeField _ _ _ _
    | with_reducible exact keeps_resolveOverride _ _ _ _
    | with_reducible exact keeps_resolveMethod _ _ _
    | with_reducible exact keeps_coroInstance _ _ _
    | with_reducible exact keeps_evalYield _
    | with_reducible exact keeps_checkExcType _ _ _
    | with_reducible exact keeps_checkCaught _ _ _
    | with_reducible exact keeps_escapeSig _ _ _
    | with_reducible exact keeps_assignLocal _ _ _
    | with_reducible exact keeps_writeUpdate _ _ _
    | with_reducible apply keeps_returnedValues
    | with_reducible apply keeps_preconditionValue
    | fail "keep_tac"))

section Helpers

variable {cfg : ExternalBackendM PM}

private theorem keeps_enterChild (base : List Nat) (k : Nat) (childSeek : Option (List Nat)) :
    KeepsOL (enterChild base k childSeek : EvalM PM Unit) := fun o => by
  unfold enterChild; keep_tac

private theorem keeps_hostFail (msg : String) : KeepsOL (hostFail msg : EvalM PM α) := fun o => by
  unfold hostFail; exact OLKeep.liftM _

private theorem keeps_chargeStep : KeepsOL (chargeStep : EvalM PM Unit) := fun o => by
  unfold chargeStep; keep_tac

private theorem keeps_chargeIteration (b : StmtExprMd) : KeepsOL (chargeIteration b : EvalM PM Unit) := fun o => by
  unfold chargeIteration; keep_tac

private theorem keeps_emitEvent (e : Event) : KeepsOL (emitEvent e : EvalM PM Unit) := fun o => by
  unfold emitEvent; exact OLKeep.liftM _

private theorem keeps_chooseValue (ty : Option HighType) (d : Value) : KeepsOL (chooseValue ty d : EvalM PM Value) :=
  fun o => by
  unfold chooseValue; exact OLKeep.liftM _

private theorem keeps_evalError (msg : String) : KeepsOL (evalError msg : EvalM PM α) := fun o => by
  unfold evalError; keep_tac

private theorem keeps_refuse (msg : String) : KeepsOL (refuse msg : EvalM PM α) := fun o => by
  unfold refuse; keep_tac

private theorem keeps_stuckError (msg : String) : KeepsOL (stuckError msg : EvalM PM α) := fun o => by
  unfold stuckError; exact OLKeep.liftM _

private theorem keeps_popOperand : KeepsOL (popOperand : EvalM PM Value) := fun o => by
  unfold popOperand; keep_tac

private theorem keeps_returnedValues (proc : Procedure) (restore : EvalM PM Unit) (hr : KeepsOL restore)
    (vs : List Value) : KeepsOL (returnedValues proc restore vs) := fun o => by
  have hr := hr o
  unfold returnedValues; keep_tac

private theorem keeps_missingPrelude (name : String) (args : List Value) :
    KeepsOL (missingPrelude name args : EvalM PM Unit) := fun o => by
  unfold missingPrelude; keep_tac

private theorem keeps_noFitPrelude (index : ProgramIndex) (op : Operation) (args : List Value) :
    KeepsOL (noFitPrelude index op args : EvalM PM Unit) := fun o => by
  unfold noFitPrelude; keep_tac

private theorem keeps_strictField (target : Value) (field : Identifier) :
    KeepsOL (strictField cfg target field : EvalM PM Unit) := fun o => by
  unfold strictField; keep_tac

private theorem keeps_allocateObject : KeepsOL (allocateObject : EvalM PM Value) := fun o => by
  unfold allocateObject; keep_tac

private theorem keeps_readField (target : Value) (name : String) : KeepsOL (readField target name : EvalM PM Value) :=
  fun o => by
  unfold readField; keep_tac

private theorem keeps_writeField (target : Value) (name : String) (v : Value) :
    KeepsOL (writeField target name v : EvalM PM Unit) := fun o => by
  unfold writeField; keep_tac

private theorem keeps_resolveOverride (target : Value) (id : Nat) (static : Procedure) :
    KeepsOL (resolveOverride target id static : EvalM PM Procedure) := fun o => by
  unfold resolveOverride; keep_tac

private theorem keeps_resolveMethod (target : Value) (name : String) :
    KeepsOL (resolveMethod target name : EvalM PM Procedure) := fun o => by
  unfold resolveMethod; keep_tac

private theorem keeps_coroInstance (v : Value) (what : String) :
    KeepsOL (coroInstance v what : EvalM PM (Nat × CoroState)) := fun o => by
  unfold coroInstance; keep_tac

private theorem keeps_evalYield : KeepsOL (evalYield : EvalM PM Value) := fun o => by
  unfold evalYield; keep_tac

private theorem keeps_checkExcType (ty : HighType) (v : Value) : KeepsOL (checkExcType ty v : EvalM PM Unit) :=
  fun o => by
  unfold checkExcType; keep_tac

private theorem keeps_checkCaught (catches : List CatchClause) (v : Value) :
    KeepsOL (checkCaught catches v : EvalM PM Unit) := fun o => by
  unfold checkCaught; keep_tac

private theorem keeps_escapeSig (proc : Procedure) (c : Control) : KeepsOL (escapeSig proc c : EvalM PM α) :=
  fun o => by
  unfold escapeSig; keep_tac

private theorem keeps_assignLocal (name : Identifier) (v : Value) : KeepsOL (assignLocal name v : EvalM PM Unit) :=
  fun o => by
  unfold assignLocal; keep_tac

private theorem keeps_writeUpdate (u : UpdateTarget) (v : Value) : KeepsOL (writeUpdate u v : EvalM PM Unit) :=
  fun o => by
  unfold writeUpdate; keep_tac

private theorem keeps_preconditionValue (ev : StmtExprMd → EvalM PM Value) (hev : ∀ e, KeepsOL (ev e))
    (proc : Procedure) (args : List Value) : KeepsOL (preconditionValue cfg ev proc args) := fun o => by
  have hev := fun e => hev e o
  unfold preconditionValue; keep_tac

end Helpers

theorem OLKeep.withBlockScope {o : List String} {l : List StmtExprMd} {x : EvalM PM α} (hx : OLKeep o x) :
    OLKeep o (Interpreter.withBlockScope l x) := by
  unfold Interpreter.withBlockScope
  keep_tac

theorem OLKeep.jumpBoundary {o : List String} {x : EvalM PM α} (hx : OLKeep o x) :
    OLKeep o (Interpreter.jumpBoundary x) := by
  unfold Interpreter.jumpBoundary
  refine OLKeep.tryCatch hx (fun c => ?_)
  cases c <;> keep_tac

theorem OLKeep.withOperandWindow {o : List String} {s : StmtExprMd} {x : EvalM PM α} (hx : OLKeep o x) :
    OLKeep o (Interpreter.withOperandWindow s x) := by
  unfold Interpreter.withOperandWindow
  refine OLKeep.getBind (fun st hst => ?_)
  rcases hop : st.operands with _ | ⟨v, vs⟩
  · dsimp only; exact hx
  · dsimp only
    rcases hw : st.operandWindow with _ | _ | ⟨hd, tl⟩
    all_goals dsimp only
    all_goals first | exact hx | keep_tac


variable (cfg : ExternalBackendM PM)

structure KeepsAt (n : Nat) : Prop where
  scoped_ : ∀ s, KeepsOL (evalScopedStmt cfg n s)
  exprMd : ∀ e, KeepsOL (evalExprMd cfg n e)
  expr : ∀ e, KeepsOL (evalExpr cfg n e)
  assign : ∀ t, KeepsOL (assignTarget cfg n t)
  update : ∀ t, KeepsOL (readForUpdate cfg n t)
  stmt : ∀ s, KeepsOL (evalStmt cfg n s)
  iter : ∀ c b p ci eb, KeepsOL ci → KeepsOL eb → KeepsOL (evalWhileIter cfg c b p ci eb n)
  blockLoop : ∀ ss l invs base, KeepsOL (evalBlockLoop cfg n ss l invs base)
  blockFrom : ∀ ss bl invs k l d, KeepsOL (evalBlockFrom cfg n ss bl invs k l d)
  stmtFrom : ∀ s l d, KeepsOL (evalStmtFrom cfg n s l d)
  runFrom : ∀ ss k l d, KeepsOL (runFrom cfg n ss k l d)
  fin : ∀ f i b k, KeepsOL (runTryFinally cfg n f i b k)
  finish : ∀ f i b k c, KeepsOL (finishCatchClause cfg n f i b k c)
  clauses : ∀ f i b k v j cs, KeepsOL (tryCatchClauses cfg n f i b k v j cs)
  go : ∀ a b s i k ss, KeepsOL (evalStmtListGo cfg n a b s i k ss)
  list : ∀ ss a, KeepsOL (evalStmtList cfg n ss a)
  resume : ∀ t v, KeepsOL (resumeCoroutine cfg n t v)
  outputs : ∀ e, KeepsOL (evalCallOutputs cfg n e)
  callee : ∀ s c a, KeepsOL (invokeCallee cfg n s c a)
  pre : ∀ s p a, KeepsOL (checkPreconditions cfg n s p a)
  post : ∀ p ps fr e x y r, KeepsOL (checkPostconditions cfg n p ps fr e x y r)
  proc : ∀ s p a, KeepsOL (invokeProc cfg n s p a)

set_option maxHeartbeats 4000000 in
/-- `evalScopedStmt` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_scoped_ {n : Nat} (ih : KeepsAt cfg n) : ∀ s, KeepsOL (evalScopedStmt cfg (n + 1) s) := by
  intro s o; simp only [evalScopedStmt]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalExprMd` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_exprMd {n : Nat} (ih : KeepsAt cfg n) : ∀ e, KeepsOL (evalExprMd cfg (n + 1) e) := by
  intro e o; simp only [evalExprMd]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalExpr` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_expr {n : Nat} (ih : KeepsAt cfg n) : ∀ e, KeepsOL (evalExpr cfg (n + 1) e) := by
  intro e o
  cases e
  case Block stmts label invs dec =>
    cases label <;> (simp only [evalExpr]; keep_tac)
  case ContractOf ty f =>
    rcases f with ⟨fv, fs⟩
    cases ty
    case Precondition =>
      cases fv
      case Call r callee args ta => cases r <;> (simp only [evalExpr]; keep_tac)
      all_goals (simp only [evalExpr]; keep_tac)
    all_goals (simp only [evalExpr]; keep_tac)
  case Call r callee args ta => cases r <;> (simp only [evalExpr]; keep_tac)
  all_goals (try (rename_i v; cases v))
  all_goals (simp only [evalExpr]; keep_tac)

set_option maxHeartbeats 4000000 in
/-- `assignTarget` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_assign {n : Nat} (ih : KeepsAt cfg n) : ∀ t, KeepsOL (assignTarget cfg (n + 1) t) := by
  intro t o; simp only [assignTarget]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `readForUpdate` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_update {n : Nat} (ih : KeepsAt cfg n) : ∀ t, KeepsOL (readForUpdate cfg (n + 1) t) := by
  intro t o; simp only [readForUpdate]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmt` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_stmt {n : Nat} (ih : KeepsAt cfg n) : ∀ s, KeepsOL (evalStmt cfg (n + 1) s) := by
  intro s o
  rcases s with ⟨v, src⟩
  cases v
  case While c invs dec body p =>
    rw [evalStmt]; dsimp only
    keep_tac
  case Block stmts label invs dec =>
    cases label
    · simp only [evalStmt]; keep_tac
    · rw [evalStmt]; dsimp only
      keep_tac
  case Call r callee args ta => cases r <;> (simp only [evalStmt]; keep_tac)
  all_goals (try (rename_i x; cases x))
  all_goals (simp only [evalStmt]; keep_tac)

set_option maxHeartbeats 4000000 in
/-- `evalBlockLoop` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_blockLoop {n : Nat} (ih : KeepsAt cfg n) :
    ∀ ss l invs base, KeepsOL (evalBlockLoop cfg (n + 1) ss l invs base) := by
  intro ss l invs base o; rw [evalBlockLoop]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalBlockFrom` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_blockFrom {n : Nat} (ih : KeepsAt cfg n) :
    ∀ ss bl invs k l d, KeepsOL (evalBlockFrom cfg (n + 1) ss bl invs k l d) := by
  intro ss bl invs k l d o
  have _ := ih
  unfold evalBlockFrom
  dsimp only
  keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtFrom` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_stmtFrom {n : Nat} (ih : KeepsAt cfg n) :
    ∀ s l d, KeepsOL (evalStmtFrom cfg (n + 1) s l d) := by
  intro s l d o
  rcases s with ⟨v, src⟩
  cases v
  case Block stmts bl invs dec =>
    unfold evalStmtFrom
    dsimp only
    keep_tac
  case IfThenElse c th el =>
    unfold evalStmtFrom
    dsimp only
    keep_tac
  all_goals
    unfold evalStmtFrom
    dsimp only
    keep_tac

set_option maxHeartbeats 4000000 in
/-- `runFrom` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_runFrom {n : Nat} (ih : KeepsAt cfg n) :
    ∀ ss k l d, KeepsOL (runFrom cfg (n + 1) ss k l d) := by
  intro ss k l d o
  unfold runFrom
  dsimp only
  keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalWhileIter` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_iter {n : Nat} (ih : KeepsAt cfg n) :
    ∀ c b p ci eb, KeepsOL ci → KeepsOL eb → KeepsOL (evalWhileIter cfg c b p ci eb (n + 1)) := by
  intro c b p ci eb hci heb o
  have _ := ih
  have hci := hci o
  have heb := heb o
  rw [evalWhileIter]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `runTryFinally` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_fin {n : Nat} (ih : KeepsAt cfg n) :
    ∀ f i b k, KeepsOL (runTryFinally cfg (n + 1) f i b k) := by
  intro f i b k o; simp only [runTryFinally]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `finishCatchClause` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_finish {n : Nat} (ih : KeepsAt cfg n) :
    ∀ f i b k c, KeepsOL (finishCatchClause cfg (n + 1) f i b k c) := by
  intro f i b k c o; simp only [finishCatchClause]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `tryCatchClauses` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_clauses {n : Nat} (ih : KeepsAt cfg n) :
    ∀ f i b k v j cs, KeepsOL (tryCatchClauses cfg (n + 1) f i b k v j cs) := by
  intro f i b k v j cs o
  cases cs <;> simp only [tryCatchClauses] <;> keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtListGo` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_go {n : Nat} (ih : KeepsAt cfg n) :
    ∀ a b s i k ss, KeepsOL (evalStmtListGo cfg (n + 1) a b s i k ss) := by
  intro a b s i k ss o
  cases ss <;> simp only [evalStmtListGo] <;> keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtList` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_list {n : Nat} (ih : KeepsAt cfg n) : ∀ ss a, KeepsOL (evalStmtList cfg (n + 1) ss a) := by
  intro ss a o; simp only [evalStmtList]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `resumeCoroutine` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_resume {n : Nat} (ih : KeepsAt cfg n) : ∀ t v, KeepsOL (resumeCoroutine cfg (n + 1) t v) := by
  intro t v o; simp only [resumeCoroutine]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `evalCallOutputs` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_outputs {n : Nat} (ih : KeepsAt cfg n) : ∀ e, KeepsOL (evalCallOutputs cfg (n + 1) e) := by
  intro e o; simp only [evalCallOutputs]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `invokeCallee` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_callee {n : Nat} (ih : KeepsAt cfg n) : ∀ s c a, KeepsOL (invokeCallee cfg (n + 1) s c a) := by
  intro s c a o; simp only [invokeCallee]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `checkPreconditions` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_pre {n : Nat} (ih : KeepsAt cfg n) : ∀ s p a, KeepsOL (checkPreconditions cfg (n + 1) s p a) := by
  intro s p a o; simp only [checkPreconditions]; keep_tac

set_option maxHeartbeats 4000000 in
/-- `checkPostconditions` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_post {n : Nat} (ih : KeepsAt cfg n) :
    ∀ p ps fr e x y r, KeepsOL (checkPostconditions cfg (n + 1) p ps fr e x y r) := by
  intro p ps fr e x y r o; simp only [checkPostconditions]; keep_tac

set_option maxHeartbeats 16000000 in
/-- `invokeProc` keeps the open labels at fuel `n + 1`, given `KeepsAt cfg n`. -/
private theorem keep_proc {n : Nat} (ih : KeepsAt cfg n) : ∀ s p a, KeepsOL (invokeProc cfg (n + 1) s p a) := by
  intro s p a o; simp only [invokeProc]; keep_tac

/-- Every one of the interpreter's mutual functions, run with any fuel `n` and any external backend `cfg`,
leaves the open labels as it found them, whether it returns a value or a control signal. -/
theorem keepsAt : ∀ n, KeepsAt cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> (try intro o) <;> first
        | (rw [evalExpr]; exact OLKeep.throw _)
        | (rw [evalStmt]; exact OLKeep.throw _)
        | (rw [evalWhileIter]; exact OLKeep.throw _)
        | (rw [evalBlockLoop]; exact OLKeep.throw _)
        | (simp only [evalScopedStmt, evalExprMd, assignTarget, readForUpdate, evalBlockFrom, evalStmtFrom, runFrom,
            runTryFinally, finishCatchClause, tryCatchClauses, evalStmtListGo, evalStmtList, resumeCoroutine,
            evalCallOutputs, invokeCallee, checkPreconditions, checkPostconditions, invokeProc]
           exact OLKeep.throw _)
  | n + 1 => by
    have ih := keepsAt n
    exact ⟨keep_scoped_ cfg ih, keep_exprMd cfg ih, keep_expr cfg ih, keep_assign cfg ih, keep_update cfg ih,
      keep_stmt cfg ih, keep_iter cfg ih, keep_blockLoop cfg ih, keep_blockFrom cfg ih, keep_stmtFrom cfg ih,
      keep_runFrom cfg ih, keep_fin cfg ih, keep_finish cfg ih, keep_clauses cfg ih, keep_go cfg ih, keep_list cfg ih,
      keep_resume cfg ih, keep_outputs cfg ih, keep_callee cfg ih, keep_pre cfg ih, keep_post cfg ih, keep_proc cfg ih⟩

/-- The part of a labelled block's `evalStmt` arm that runs inside the scope of its label, the statements and the
handler for the signals that leave or restart the block, keeps the open labels. -/
theorem keeps_blockArm (n : Nat) (ss : List StmtExprMd) (lab : String) (base : List Nat) :
    KeepsOL (tryCatch (do let _ ← withBlockScope ss (evalStmtList cfg n ss (asExpr := false)); pure ())
      (fun (c : Control) => match c with
        | .exit_ l =>
            if l == lab then
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
            else throw (.exit_ l)
        | .goto_ l =>
            if l == lab then do
              modify fun (s : EvalState) => { s with cursor := base, seek := none }
              chargeStep
              evalBlockLoop cfg n ss lab [] base
            else throw (.goto_ l)
        | other => throw other : Control → EvalM PM Unit)) := by
  intro o
  have ih := keepsAt cfg n
  refine OLKeep.tryCatch ?_ (fun c => ?_)
  · keep_tac
  · cases c <;> keep_tac

end Strata.Laurel.PassSemantics
