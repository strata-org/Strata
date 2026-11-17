/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Jumps

/-!
# The Laurel interpreter keeps a run outside a coroutine body outside one

`cnAt : ∀ n, CNAt cfg n`: each of the interpreter's mutual functions, run with fuel `n` from a state
outside a coroutine body (`coroSelf = none`), ends outside one, whether it finishes or leaves by a
signal. Only `resumeCoroutine` enters a coroutine body, and it puts the caller's `coroSelf` back on
every way out; a call clears `coroSelf` for its callee and puts the caller's back. Pass proofs use
this to know that a statement list run again after a jump back to its block's start runs as a
plain list, which lands the jumps to its own blocks.

`CN x` is the property for one action. The combinator lemmas are proved first, then the proof is
one induction on `n` as in `Labels.lean`; `resumeCoroutine` is proved by hand.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

/-- When `x` starts outside a coroutine body (`coroSelf = none`) and returns, with a value or with a control
signal, it ends outside one. -/
structure CN (x : EvalM PM α) : Prop where
  keep : ∀ σ τ r σ1 τ1, σ.coroSelf = none → run x σ τ = .ok ((r, σ1), τ1) → σ1.coroSelf = none

theorem CN.pure (a : α) : CN (pure a : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem CN.throw (c : Control) : CN (throw c : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_throw] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem CN.get : CN (MonadState.get : EvalM PM EvalState) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_get] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ⟩

theorem CN.set (σ' : EvalState) (hσ' : σ'.coroSelf = none) :
    CN (MonadStateOf.set σ' : EvalM PM PUnit) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    have e : run (MonadStateOf.set σ' : EvalM PM PUnit) σ τ = .ok ((.ok (), σ'), τ) := rfl
    rw [e] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hσ'⟩

theorem CN.modify {f : EvalState → EvalState} (hf : ∀ σ, σ.coroSelf = none → (f σ).coroSelf = none) :
    CN (_root_.modify f : EvalM PM PUnit) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_modify] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hf σ hσ⟩

theorem CN.liftM (x : PM α) : CN (liftM x : EvalM PM α) :=
  ⟨fun σ τ r σ1 τ1 hσ h => by
    rw [run_lift] at h
    rcases hx : x τ with e | ⟨a, τ'⟩ <;> rw [hx] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact hσ⟩

/-- `bind` keeps the coroutine-free state if both parts do. -/
theorem CN.bind {x : EvalM PM α} {f : α → EvalM PM β} (hx : CN x)
    (hf : ∀ a, CN (f a)) : CN (x >>= f) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx.keep _ _ _ _ _ hσ hr
  · exact (hf a).keep _ _ _ _ _ (hx.keep _ _ _ _ _ hσ hr) h

/-- `get` followed by an action that keeps the coroutine-free state when they are those of the state read keeps the
coroutine-free state. -/
theorem CN.getBind {f : EvalState → EvalM PM β} (hf : ∀ s, s.coroSelf = none → CN (f s)) :
    CN (MonadState.get >>= f) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_bind, run_get] at h
  exact (hf σ hσ).keep _ _ _ _ _ hσ h

/-- `tryCatch` keeps the coroutine-free state if the body and every handler do. -/
theorem CN.tryCatch {x : EvalM PM α} {h : Control → EvalM PM α} (hx : CN x)
    (hh : ∀ c, CN (h c)) : CN (MonadExcept.tryCatch x h) := by
  refine ⟨fun σ τ r σ1 τ1 hσ he => ?_⟩
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact (hh c).keep _ _ _ _ _ (hx.keep _ _ _ _ _ hσ hr) he
  · simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, -⟩ := he
    exact hx.keep _ _ _ _ _ hσ hr

theorem CN.ite {c : Prop} [Decidable c] {x y : EvalM PM α} (hx : CN x) (hy : CN y) :
    CN (if c then x else y) := by
  split
  · exact hx
  · exact hy

theorem CN.map {x : EvalM PM α} (f : α → β) (hx : CN x) : CN (f <$> x) := by
  simp only [map_eq_pure_bind]
  exact hx.bind (fun _ => CN.pure _)

theorem CN.forM {l : List β} {f : β → EvalM PM PUnit} (h : ∀ b, CN (f b)) :
    CN (l.forM f) := by
  induction l with
  | nil => exact CN.pure _
  | cons b bs ih => exact (h b).bind (fun _ => ih)

theorem CN.mapM {l : List β} {f : β → EvalM PM γ} (h : ∀ b, CN (f b)) :
    CN (l.mapM f) := by
  induction l with
  | nil => exact CN.pure _
  | cons b bs ih =>
    simp only [List.mapM_cons]
    exact (h b).bind (fun _ => ih.bind (fun _ => CN.pure _))

theorem CN.forIn {l : List β} {b : γ} {f : β → γ → EvalM PM (ForInStep γ)}
    (h : ∀ x c, CN (f x c)) : CN (forIn l b f) := by
  induction l generalizing b with
  | nil => exact CN.pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine (h x b).bind (fun r => ?_)
    cases r with
    | done c => exact CN.pure _
    | yield c => exact ih

theorem CN.arrayMapM {l : Array β} {f : β → EvalM PM γ} (h : ∀ b, CN (f b)) :
    CN (l.mapM f) := by
  simp only [Array.mapM_eq_mapM_toList, Functor.map]
  exact (CN.mapM h).bind (fun _ => CN.pure _)

theorem CN.muteE {x : EvalM PM α} (hx : CN x) : CN (Interpreter.muteE x) := by
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

theorem CN.muteSel {c : Prop} [Decidable c] {x : EvalM PM α} (hx : CN x) :
    CN ((if c then Interpreter.muteE else id) x) := by
  split
  · exact hx.muteE
  · exact hx

/-- `withLabels` keeps the coroutine-free state if what it runs does: it only changes the open labels. -/
theorem CN.withLabels (f : List String → List String) {x : EvalM PM α} (hx : CN x) :
    CN (Interpreter.withLabels f x) := by
  refine ⟨fun σ τ r σ1 τ1 hσ h => ?_⟩
  rw [run_withLabels] at h
  rcases hr : run x { σ with openLabels := f σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx.keep { σ with openLabels := f σ.openLabels } _ _ σ2 _ hσ hr
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx.keep { σ with openLabels := f σ.openLabels } _ _ σ2 _ hσ hr

theorem CN.withOpenLabel (l : String) {x : EvalM PM α} (hx : CN x) :
    CN (Interpreter.withOpenLabel l x) :=
  CN.withLabels _ hx

set_option hygiene false in
macro "cn_tac" : tactic => `(tactic|
  repeat' (first
    | with_reducible apply CN.jumpBoundary
    | with_reducible apply CN.muteSel
    | with_reducible apply CN.muteE
    | with_reducible refine CN.tryCatch ?_ ?_
    | with_reducible apply CN.getBind
    | with_reducible apply CN.bind
    | with_reducible apply CN.ite
    | with_reducible apply CN.map
    | with_reducible apply CN.forM
    | with_reducible apply CN.mapM
    | with_reducible apply CN.forIn
    | with_reducible apply CN.arrayMapM
    | with_reducible apply CN.withBlockScope
    | with_reducible apply CN.withOperandWindow
    | with_unfolding_none exact CN.pure _
    | with_unfolding_none exact CN.throw _
    | with_unfolding_none exact CN.get
    | with_reducible assumption
    | with_reducible exact hev _
    | with_reducible exact ih.exprMd
    | with_reducible exact ih.scoped_ _
    | with_reducible exact ih.exprMd _
    | with_reducible exact ih.expr _
    | with_reducible exact ih.assign _
    | with_reducible exact ih.update _
    | with_reducible exact ih.stmt _
    | with_reducible refine ih.iter _ _ _ _ _ ?_ ?_
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
    | with_unfolding_none exact CN.liftM _
    | with_reducible apply CN.withLabels
    | with_reducible apply CN.withOpenLabel
    | with_unfolding_none refine CN.modify (fun σ hσ => ?_)
    | with_unfolding_none refine CN.set _ ?_
    | refine fun _ => ?_
    | dsimp only
    | split
    | with_reducible exact cn_hostFail _
    | with_reducible exact cn_evalError _
    | with_reducible exact cn_refuse _
    | with_reducible exact cn_stuckError _
    | with_reducible exact cn_chargeStep
    | with_reducible exact cn_enterChild _ _ _
    | with_reducible exact cn_chargeIteration _
    | with_reducible exact cn_emitEvent _
    | with_reducible exact cn_chooseValue _ _
    | with_reducible exact cn_popOperand
    | with_reducible exact cn_missingPrelude _ _
    | with_reducible exact cn_noFitPrelude _ _ _
    | with_reducible exact cn_strictField _ _
    | with_reducible exact cn_allocateObject
    | with_reducible exact cn_readField _ _
    | with_reducible exact cn_writeField _ _ _
    | with_reducible exact cn_resolveOverride _ _ _
    | with_reducible exact cn_resolveMethod _ _
    | with_reducible exact cn_coroInstance _ _
    | with_reducible exact cn_evalYield
    | with_reducible exact cn_checkExcType _ _
    | with_reducible exact cn_checkCaught _ _
    | with_reducible exact cn_escapeSig _ _
    | with_reducible exact cn_assignLocal _ _
    | with_reducible exact cn_writeUpdate _ _
    | with_reducible apply cn_returnedValues
    | with_reducible apply cn_preconditionValue
    | fail "cn_tac"))

/-- `x` never returns a control signal. -/
def NE (x : EvalM PM α) : Prop := ∀ σ τ c σ1 τ1, run x σ τ ≠ .ok ((.error c, σ1), τ1)

/-- Whenever `x` returns a control signal, from any state, it ends outside a coroutine body. -/
def EN (x : EvalM PM α) : Prop := ∀ σ τ c σ1 τ1, run x σ τ = .ok ((.error c, σ1), τ1) → σ1.coroSelf = none

/-- Whenever `x` returns, from any state, it ends outside a coroutine body. -/
def RN (x : EvalM PM α) : Prop := ∀ σ τ r σ1 τ1, run x σ τ = .ok ((r, σ1), τ1) → σ1.coroSelf = none

theorem NE.pure (a : α) : NE (pure a : EvalM PM α) := by
  intro σ τ c σ1 τ1 h; rw [run_pure] at h; cases h

theorem NE.get : NE (MonadState.get : EvalM PM EvalState) := by
  intro σ τ c σ1 τ1 h; rw [run_get] at h; cases h

theorem NE.modify (f : EvalState → EvalState) : NE (_root_.modify f : EvalM PM PUnit) := by
  intro σ τ c σ1 τ1 h; rw [run_modify] at h; cases h

theorem NE.bind {x : EvalM PM α} {f : α → EvalM PM β} (hx : NE x) (hf : ∀ a, NE (f a)) : NE (x >>= f) := by
  intro σ τ c σ1 τ1 h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c' | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · exact hx _ _ _ _ _ hr
  · exact hf a _ _ _ _ _ h

theorem EN.ofNE {x : EvalM PM α} (hx : NE x) : EN x := fun _ _ _ _ _ h => absurd h (hx _ _ _ _ _)

theorem EN.ofRN {x : EvalM PM α} (hx : RN x) : EN x := fun _ _ _ _ _ h => hx _ _ _ _ _ h

theorem EN.bind {x : EvalM PM α} {f : α → EvalM PM β} (hx : EN x) (hf : ∀ a, EN (f a)) : EN (x >>= f) := by
  intro σ τ c σ1 τ1 h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c' | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx _ _ _ _ _ hr
  · exact hf a _ _ _ _ _ h

/-- The signals `tryCatch x h` returns come from its handler. -/
theorem EN.tryCatch {x : EvalM PM α} {h : Control → EvalM PM α} (hh : ∀ c, EN (h c)) :
    EN (MonadExcept.tryCatch x h) := by
  intro σ τ c σ1 τ1 he
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c' | a, σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact hh c' _ _ _ _ _ he
  · cases he

theorem RN.bind {x : EvalM PM α} {f : α → EvalM PM β} (hx : EN x) (hf : ∀ a, RN (f a)) : RN (x >>= f) := by
  intro σ τ r σ1 τ1 h
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c' | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨-, rfl⟩, -⟩ := h
    exact hx _ _ _ _ _ hr
  · exact hf a _ _ _ _ _ h

/-- A state update that leaves a coroutine body, followed by an action that stays outside one, ends outside
one from any state. -/
theorem RN.modifyBind {g : EvalState → EvalState} {f : PUnit → EvalM PM β} (hg : ∀ σ, (g σ).coroSelf = none)
    (hf : ∀ a, CN (f a)) : RN (_root_.modify g >>= f) := by
  intro σ τ r σ1 τ1 h
  rw [run_bind, run_modify] at h
  exact (hf ()).keep _ _ _ _ _ (hg σ) h

theorem CN.modifyThenRN {g : EvalState → EvalState} {f : PUnit → EvalM PM β} (hf : ∀ a, RN (f a)) :
    CN (_root_.modify g >>= f) := by
  refine ⟨fun σ τ r σ1 τ1 _ h => ?_⟩
  rw [run_bind, run_modify] at h
  exact hf () _ _ _ _ _ h

set_option hygiene false in
macro "rn_tac" : tactic => `(tactic|
  repeat' (first
    | (with_reducible refine RN.modifyBind (fun σ => by dsimp only; assumption) ?_)
    | (with_reducible refine EN.ofRN (RN.modifyBind (fun σ => by dsimp only; assumption) ?_))
    | with_reducible apply RN.bind
    | with_reducible apply EN.bind
    | with_reducible refine EN.tryCatch ?_
    | with_unfolding_none exact EN.ofNE (NE.pure _)
    | with_unfolding_none exact EN.ofNE NE.get
    | with_unfolding_none exact EN.ofNE (NE.modify _)
    | with_unfolding_none exact CN.pure _
    | with_unfolding_none exact CN.throw _
    | refine fun _ => ?_
    | dsimp only
    | split
    | fail "rn_tac"))

set_option hygiene false in
macro "cn_tac_r" : tactic => `(tactic|
  repeat' (first
    | (with_reducible refine CN.modifyThenRN ?_; intro _; rn_tac; done)
    | with_reducible apply CN.jumpBoundary
    | with_reducible apply CN.muteSel
    | with_reducible apply CN.muteE
    | with_reducible refine CN.tryCatch ?_ ?_
    | with_reducible apply CN.getBind
    | with_reducible apply CN.bind
    | with_reducible apply CN.ite
    | with_reducible apply CN.map
    | with_reducible apply CN.forM
    | with_reducible apply CN.mapM
    | with_reducible apply CN.forIn
    | with_reducible apply CN.arrayMapM
    | with_reducible apply CN.withBlockScope
    | with_reducible apply CN.withOperandWindow
    | with_unfolding_none exact CN.pure _
    | with_unfolding_none exact CN.throw _
    | with_unfolding_none exact CN.get
    | with_reducible assumption
    | with_reducible exact hev _
    | with_reducible exact ih.exprMd
    | with_reducible exact ih.scoped_ _
    | with_reducible exact ih.exprMd _
    | with_reducible exact ih.expr _
    | with_reducible exact ih.assign _
    | with_reducible exact ih.update _
    | with_reducible exact ih.stmt _
    | with_reducible refine ih.iter _ _ _ _ _ ?_ ?_
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
    | with_unfolding_none exact CN.liftM _
    | with_reducible apply CN.withLabels
    | with_reducible apply CN.withOpenLabel
    | with_unfolding_none refine CN.modify (fun σ hσ => ?_)
    | with_unfolding_none refine CN.set _ ?_
    | refine fun _ => ?_
    | dsimp only
    | split
    | with_reducible exact cn_hostFail _
    | with_reducible exact cn_evalError _
    | with_reducible exact cn_refuse _
    | with_reducible exact cn_stuckError _
    | with_reducible exact cn_chargeStep
    | with_reducible exact cn_enterChild _ _ _
    | with_reducible exact cn_chargeIteration _
    | with_reducible exact cn_emitEvent _
    | with_reducible exact cn_chooseValue _ _
    | with_reducible exact cn_popOperand
    | with_reducible exact cn_missingPrelude _ _
    | with_reducible exact cn_noFitPrelude _ _ _
    | with_reducible exact cn_strictField _ _
    | with_reducible exact cn_allocateObject
    | with_reducible exact cn_readField _ _
    | with_reducible exact cn_writeField _ _ _
    | with_reducible exact cn_resolveOverride _ _ _
    | with_reducible exact cn_resolveMethod _ _
    | with_reducible exact cn_coroInstance _ _
    | with_reducible exact cn_evalYield
    | with_reducible exact cn_checkExcType _ _
    | with_reducible exact cn_checkCaught _ _
    | with_reducible exact cn_escapeSig _ _
    | with_reducible exact cn_assignLocal _ _
    | with_reducible exact cn_writeUpdate _ _
    | with_reducible apply cn_returnedValues
    | with_reducible apply cn_preconditionValue
    | fail "cn_tac_r"))

section Helpers

variable {cfg : ExternalBackendM PM}

theorem cn_enterChild (base : List Nat) (k : Nat) (childSeek : Option (List Nat)) :
    CN (enterChild base k childSeek : EvalM PM Unit) := by
  unfold enterChild; cn_tac

theorem cn_hostFail (msg : String) : CN (hostFail msg : EvalM PM α) := by
  unfold hostFail; exact CN.liftM _

theorem cn_chargeStep : CN (chargeStep : EvalM PM Unit) := by
  unfold chargeStep; cn_tac

theorem cn_chargeIteration (b : StmtExprMd) : CN (chargeIteration b : EvalM PM Unit) := by
  unfold chargeIteration; cn_tac

theorem cn_emitEvent (e : Event) : CN (emitEvent e : EvalM PM Unit) := by
  unfold emitEvent; exact CN.liftM _

theorem cn_chooseValue (ty : Option HighType) (d : Value) : CN (chooseValue ty d : EvalM PM Value) := by
  unfold chooseValue; exact CN.liftM _

theorem cn_evalError (msg : String) : CN (evalError msg : EvalM PM α) := by
  unfold evalError; cn_tac

theorem cn_refuse (msg : String) : CN (refuse msg : EvalM PM α) := by
  unfold refuse; cn_tac

private theorem cn_stuckError (msg : String) : CN (stuckError msg : EvalM PM α) := by
  unfold stuckError; exact CN.liftM _

theorem cn_popOperand : CN (popOperand : EvalM PM Value) := by
  unfold popOperand; cn_tac

theorem cn_returnedValues (proc : Procedure) (restore : EvalM PM Unit) (hr : CN restore)
    (vs : List Value) : CN (returnedValues proc restore vs) := by
  unfold returnedValues; cn_tac

theorem cn_missingPrelude (name : String) (args : List Value) :
    CN (missingPrelude name args : EvalM PM Unit) := by
  unfold missingPrelude; cn_tac

theorem cn_noFitPrelude (index : ProgramIndex) (op : Operation) (args : List Value) :
    CN (noFitPrelude index op args : EvalM PM Unit) := by
  unfold noFitPrelude; cn_tac

private theorem cn_strictField (target : Value) (field : Identifier) :
    CN (strictField cfg target field : EvalM PM Unit) := by
  unfold strictField; cn_tac

theorem cn_allocateObject : CN (allocateObject : EvalM PM Value) := by
  unfold allocateObject; cn_tac

theorem cn_readField (target : Value) (name : String) : CN (readField target name : EvalM PM Value) := by
  unfold readField; cn_tac

theorem cn_writeField (target : Value) (name : String) (v : Value) :
    CN (writeField target name v : EvalM PM Unit) := by
  unfold writeField; cn_tac

theorem cn_resolveOverride (target : Value) (id : Nat) (static : Procedure) :
    CN (resolveOverride target id static : EvalM PM Procedure) := by
  unfold resolveOverride; cn_tac

theorem cn_resolveMethod (target : Value) (name : String) :
    CN (resolveMethod target name : EvalM PM Procedure) := by
  unfold resolveMethod; cn_tac

theorem cn_coroInstance (v : Value) (what : String) :
    CN (coroInstance v what : EvalM PM (Nat × CoroState)) := by
  unfold coroInstance; cn_tac

theorem cn_evalYield : CN (evalYield : EvalM PM Value) := by
  unfold evalYield; cn_tac

theorem cn_checkExcType (ty : HighType) (v : Value) : CN (checkExcType ty v : EvalM PM Unit) := by
  unfold checkExcType; cn_tac

theorem cn_checkCaught (catches : List CatchClause) (v : Value) :
    CN (checkCaught catches v : EvalM PM Unit) := by
  unfold checkCaught; cn_tac

theorem cn_escapeSig (proc : Procedure) (c : Control) : CN (escapeSig proc c : EvalM PM α) := by
  unfold escapeSig; cn_tac

theorem cn_assignLocal (name : Identifier) (v : Value) : CN (assignLocal name v : EvalM PM Unit) := by
  unfold assignLocal; cn_tac

theorem cn_writeUpdate (u : UpdateTarget) (v : Value) : CN (writeUpdate u v : EvalM PM Unit) := by
  unfold writeUpdate; cn_tac

theorem cn_preconditionValue (ev : StmtExprMd → EvalM PM Value) (hev : ∀ e, CN (ev e))
    (proc : Procedure) (args : List Value) : CN (preconditionValue cfg ev proc args) := by
  unfold preconditionValue; cn_tac

end Helpers

theorem CN.withBlockScope {l : List StmtExprMd} {x : EvalM PM α} (hx : CN x) :
    CN (Interpreter.withBlockScope l x) := by
  unfold Interpreter.withBlockScope
  cn_tac

theorem CN.jumpBoundary {x : EvalM PM α} (hx : CN x) :
    CN (Interpreter.jumpBoundary x) := by
  unfold Interpreter.jumpBoundary
  refine CN.tryCatch hx (fun c => ?_)
  cases c <;> cn_tac

theorem CN.withOperandWindow {s : StmtExprMd} {x : EvalM PM α} (hx : CN x) :
    CN (Interpreter.withOperandWindow s x) := by
  unfold Interpreter.withOperandWindow
  refine CN.getBind (fun st hst => ?_)
  rcases hop : st.operands with _ | ⟨v, vs⟩
  · dsimp only; exact hx
  · dsimp only
    rcases hw : st.operandWindow with _ | _ | ⟨hd, tl⟩
    all_goals dsimp only
    all_goals first | exact hx | cn_tac


variable (cfg : ExternalBackendM PM)

structure CNAt (n : Nat) : Prop where
  scoped_ : ∀ s, CN (evalScopedStmt cfg n s)
  exprMd : ∀ e, CN (evalExprMd cfg n e)
  expr : ∀ e, CN (evalExpr cfg n e)
  assign : ∀ t, CN (assignTarget cfg n t)
  update : ∀ t, CN (readForUpdate cfg n t)
  stmt : ∀ s, CN (evalStmt cfg n s)
  iter : ∀ c b p ci eb, CN ci → CN eb → CN (evalWhileIter cfg c b p ci eb n)
  blockLoop : ∀ ss l invs base, CN (evalBlockLoop cfg n ss l invs base)
  blockFrom : ∀ ss bl invs k l d, CN (evalBlockFrom cfg n ss bl invs k l d)
  stmtFrom : ∀ s l d, CN (evalStmtFrom cfg n s l d)
  runFrom : ∀ ss k l d, CN (runFrom cfg n ss k l d)
  fin : ∀ f i b k, CN (runTryFinally cfg n f i b k)
  finish : ∀ f i b k c, CN (finishCatchClause cfg n f i b k c)
  clauses : ∀ f i b k v j cs, CN (tryCatchClauses cfg n f i b k v j cs)
  go : ∀ a b s i k ss, CN (evalStmtListGo cfg n a b s i k ss)
  list : ∀ ss a, CN (evalStmtList cfg n ss a)
  resume : ∀ t v, CN (resumeCoroutine cfg n t v)
  outputs : ∀ e, CN (evalCallOutputs cfg n e)
  callee : ∀ s c a, CN (invokeCallee cfg n s c a)
  pre : ∀ s p a, CN (checkPreconditions cfg n s p a)
  post : ∀ p ps fr e x y r, CN (checkPostconditions cfg n p ps fr e x y r)
  proc : ∀ s p a, CN (invokeProc cfg n s p a)

set_option maxHeartbeats 4000000 in
/-- `evalScopedStmt` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_scoped_ {n : Nat} (ih : CNAt cfg n) : ∀ s, CN (evalScopedStmt cfg (n + 1) s) := by
  intro s; simp only [evalScopedStmt]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalExprMd` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_exprMd {n : Nat} (ih : CNAt cfg n) : ∀ e, CN (evalExprMd cfg (n + 1) e) := by
  intro e; simp only [evalExprMd]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalExpr` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_expr {n : Nat} (ih : CNAt cfg n) : ∀ e, CN (evalExpr cfg (n + 1) e) := by
  intro e
  cases e
  case Block stmts label invs dec =>
    cases label <;> (simp only [evalExpr]; cn_tac)
  case ContractOf ty f =>
    rcases f with ⟨fv, fs⟩
    cases ty
    case Precondition =>
      cases fv
      case Call r callee args ta => cases r <;> (simp only [evalExpr]; cn_tac)
      all_goals (simp only [evalExpr]; cn_tac)
    all_goals (simp only [evalExpr]; cn_tac)
  case Call r callee args ta => cases r <;> (simp only [evalExpr]; cn_tac)
  all_goals (try (rename_i v; cases v))
  all_goals (simp only [evalExpr]; cn_tac)

set_option maxHeartbeats 4000000 in
/-- `assignTarget` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_assign {n : Nat} (ih : CNAt cfg n) : ∀ t, CN (assignTarget cfg (n + 1) t) := by
  intro t; simp only [assignTarget]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `readForUpdate` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_update {n : Nat} (ih : CNAt cfg n) : ∀ t, CN (readForUpdate cfg (n + 1) t) := by
  intro t; simp only [readForUpdate]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmt` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_stmt {n : Nat} (ih : CNAt cfg n) : ∀ s, CN (evalStmt cfg (n + 1) s) := by
  intro s
  rcases s with ⟨v, src⟩
  cases v
  case While c invs dec body p =>
    rw [evalStmt]; dsimp only
    cn_tac
  case Block stmts label invs dec =>
    cases label
    · simp only [evalStmt]; cn_tac
    · rw [evalStmt]; dsimp only
      cn_tac
  case Call r callee args ta => cases r <;> (simp only [evalStmt]; cn_tac)
  all_goals (try (rename_i x; cases x))
  all_goals (simp only [evalStmt]; cn_tac)

set_option maxHeartbeats 4000000 in
/-- `evalBlockLoop` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_blockLoop {n : Nat} (ih : CNAt cfg n) :
    ∀ ss l invs base, CN (evalBlockLoop cfg (n + 1) ss l invs base) := by
  intro ss l invs base; rw [evalBlockLoop]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalBlockFrom` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_blockFrom {n : Nat} (ih : CNAt cfg n) :
    ∀ ss bl invs k l d, CN (evalBlockFrom cfg (n + 1) ss bl invs k l d) := by
  intro ss bl invs k l d
  have _ := ih
  unfold evalBlockFrom
  dsimp only
  cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtFrom` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_stmtFrom {n : Nat} (ih : CNAt cfg n) :
    ∀ s l d, CN (evalStmtFrom cfg (n + 1) s l d) := by
  intro s l d
  rcases s with ⟨v, src⟩
  cases v
  case Block stmts bl invs dec =>
    unfold evalStmtFrom
    dsimp only
    cn_tac
  case IfThenElse c th el =>
    unfold evalStmtFrom
    dsimp only
    cn_tac
  all_goals
    unfold evalStmtFrom
    dsimp only
    cn_tac

set_option maxHeartbeats 4000000 in
/-- `runFrom` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_runFrom {n : Nat} (ih : CNAt cfg n) :
    ∀ ss k l d, CN (runFrom cfg (n + 1) ss k l d) := by
  intro ss k l d
  unfold runFrom
  dsimp only
  cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalWhileIter` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_iter {n : Nat} (ih : CNAt cfg n) :
    ∀ c b p ci eb, CN ci → CN eb → CN (evalWhileIter cfg c b p ci eb (n + 1)) := by
  intro c b p ci eb hci heb
  have _ := ih
  rw [evalWhileIter]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `runTryFinally` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_fin {n : Nat} (ih : CNAt cfg n) :
    ∀ f i b k, CN (runTryFinally cfg (n + 1) f i b k) := by
  intro f i b k; simp only [runTryFinally]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `finishCatchClause` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_finish {n : Nat} (ih : CNAt cfg n) :
    ∀ f i b k c, CN (finishCatchClause cfg (n + 1) f i b k c) := by
  intro f i b k c; simp only [finishCatchClause]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `tryCatchClauses` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_clauses {n : Nat} (ih : CNAt cfg n) :
    ∀ f i b k v j cs, CN (tryCatchClauses cfg (n + 1) f i b k v j cs) := by
  intro f i b k v j cs
  cases cs <;> simp only [tryCatchClauses] <;> cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtListGo` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_go {n : Nat} (ih : CNAt cfg n) :
    ∀ a b s i k ss, CN (evalStmtListGo cfg (n + 1) a b s i k ss) := by
  intro a b s i k ss
  cases ss <;> simp only [evalStmtListGo] <;> cn_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtList` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_list {n : Nat} (ih : CNAt cfg n) : ∀ ss a, CN (evalStmtList cfg (n + 1) ss a) := by
  intro ss a; simp only [evalStmtList]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `resumeCoroutine` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_resume {n : Nat} (_ih : CNAt cfg n) : ∀ t v, CN (resumeCoroutine cfg (n + 1) t v) := by
  intro t v; simp only [resumeCoroutine]; cn_tac_r

set_option maxHeartbeats 4000000 in
/-- `evalCallOutputs` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_outputs {n : Nat} (ih : CNAt cfg n) : ∀ e, CN (evalCallOutputs cfg (n + 1) e) := by
  intro e; simp only [evalCallOutputs]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `invokeCallee` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_callee {n : Nat} (ih : CNAt cfg n) : ∀ s c a, CN (invokeCallee cfg (n + 1) s c a) := by
  intro s c a; simp only [invokeCallee]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `checkPreconditions` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_pre {n : Nat} (ih : CNAt cfg n) : ∀ s p a, CN (checkPreconditions cfg (n + 1) s p a) := by
  intro s p a; simp only [checkPreconditions]; cn_tac

set_option maxHeartbeats 4000000 in
/-- `checkPostconditions` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_post {n : Nat} (ih : CNAt cfg n) :
    ∀ p ps fr e x y r, CN (checkPostconditions cfg (n + 1) p ps fr e x y r) := by
  intro p ps fr e x y r; simp only [checkPostconditions]; cn_tac

set_option maxHeartbeats 16000000 in
/-- `invokeProc` keeps the coroutine-free state at fuel `n + 1`, given `CNAt cfg n`. -/
private theorem cn_s_proc {n : Nat} (ih : CNAt cfg n) : ∀ s p a, CN (invokeProc cfg (n + 1) s p a) := by
  intro s p a; simp only [invokeProc]; cn_tac

/-- Every one of the interpreter's mutual functions, run with any fuel `n` and any external backend `cfg`,
leaves the coroutine-free state as it found them, whether it returns a value or a control signal. -/
theorem cnAt : ∀ n, CNAt cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> first
        | (rw [evalExpr]; exact CN.throw _)
        | (rw [evalStmt]; exact CN.throw _)
        | (rw [evalWhileIter]; exact CN.throw _)
        | (rw [evalBlockLoop]; exact CN.throw _)
        | (simp only [evalScopedStmt, evalExprMd, assignTarget, readForUpdate, evalBlockFrom, evalStmtFrom, runFrom,
            runTryFinally, finishCatchClause, tryCatchClauses, evalStmtListGo, evalStmtList, resumeCoroutine,
            evalCallOutputs, invokeCallee, checkPreconditions, checkPostconditions, invokeProc]
           exact CN.throw _)
  | n + 1 => by
    have ih := cnAt n
    exact ⟨cn_s_scoped_ cfg ih, cn_s_exprMd cfg ih, cn_s_expr cfg ih, cn_s_assign cfg ih, cn_s_update cfg ih,
      cn_s_stmt cfg ih, cn_s_iter cfg ih, cn_s_blockLoop cfg ih, cn_s_blockFrom cfg ih, cn_s_stmtFrom cfg ih,
      cn_s_runFrom cfg ih, cn_s_fin cfg ih, cn_s_finish cfg ih, cn_s_clauses cfg ih, cn_s_go cfg ih, cn_s_list cfg ih,
      cn_s_resume cfg ih, cn_s_outputs cfg ih, cn_s_callee cfg ih, cn_s_pre cfg ih, cn_s_post cfg ih, cn_s_proc cfg ih⟩

end Strata.Laurel.PassSemantics
