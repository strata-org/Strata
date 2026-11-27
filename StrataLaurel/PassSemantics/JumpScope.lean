/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.PassSemantics.Coro

/-!
# A jump to an open block never escapes

`jkAt : ∀ n, JKAt cfg n`: each of the interpreter's mutual functions, run with fuel `n`, keeps the
open labels (`OLKeep`) and never returns a `jump_` to a label that was open when it started. A
`goto` to an open block is an `exit_` or a `goto_`, a nested labelled block only adds to the open
labels, and a call and an expression are jump boundaries (`jumpBoundary`), so no `jump_` comes
out of them at all.

`JK o x` is the property for one action started with the open labels `o`. The combinator lemmas
are proved first, then the proof is one induction on `n` as in `Labels.lean`.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

/-- `x`, started with the open labels `o`, keeps them, and never returns a `jump_` to one of them. -/
structure JK (o : List String) (x : EvalM PM α) : Prop where
  keep : OLKeep o x
  nj : ∀ σ τ l d σ1 τ1, σ.openLabels = o → run x σ τ = .ok ((.error (.jump_ l d), σ1), τ1) → l ∉ o

/-- `x` has `JK` for every list of open labels. -/
@[reducible] def KeepsJK (x : EvalM PM α) : Prop := ∀ o, JK o x

theorem JK.ofNoJ {o : List String} {x : EvalM PM α} (hk : OLKeep o x) (hn : NoJ x) : JK o x :=
  ⟨hk, fun _ _ _ _ _ _ _ h => absurd h (hn _ _ _ _ _ _)⟩

theorem JK.pure {o : List String} (a : α) : JK o (pure a : EvalM PM α) :=
  JK.ofNoJ (OLKeep.pure a) (NoJ.pure a)

theorem JK.throw {o : List String} (c : Control) (hc : ∀ l d, c = .jump_ l d → l ∉ o) :
    JK o (throw c : EvalM PM α) := by
  refine ⟨OLKeep.throw c, fun σ τ l d σ1 τ1 _ h => ?_⟩
  rw [run_throw] at h
  simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
  exact hc l d h.1.1

theorem JK.throwSome {o : List String} (c : Control) (hc : ∀ c', some c = some c' → ∀ l d, c' = .jump_ l d → l ∉ o) :
    JK o (MonadExcept.throw c : EvalM PM α) :=
  JK.throw c (hc c rfl)

theorem JK.get {o : List String} : JK o (MonadState.get : EvalM PM EvalState) :=
  JK.ofNoJ OLKeep.get NoJ.get

theorem JK.set {o : List String} (σ' : EvalState) (hσ' : σ'.openLabels = o) :
    JK o (MonadStateOf.set σ' : EvalM PM PUnit) :=
  JK.ofNoJ (OLKeep.set σ' hσ') (NoJ.set σ')

theorem JK.modify {o : List String} {f : EvalState → EvalState} (hf : ∀ σ, σ.openLabels = o → (f σ).openLabels = o) :
    JK o (_root_.modify f : EvalM PM PUnit) :=
  JK.ofNoJ (OLKeep.modify hf) (NoJ.modify f)

theorem JK.liftM {o : List String} (x : PM α) : JK o (liftM x : EvalM PM α) :=
  JK.ofNoJ (OLKeep.liftM x) (NoJ.liftM x)

theorem JK.bind {o : List String} {x : EvalM PM α} {f : α → EvalM PM β} (hx : JK o x) (hf : ∀ a, JK o (f a)) :
    JK o (x >>= f) := by
  refine ⟨OLKeep.bind hx.keep (fun a => (hf a).keep), fun σ τ l d σ1 τ1 hσ h => ?_⟩
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact hx.nj _ _ _ _ _ _ hσ hr
  · exact (hf a).nj _ _ _ _ _ _ (hx.keep.keep _ _ _ _ _ hσ hr) h

theorem JK.getBind {o : List String} {f : EvalState → EvalM PM β} (hf : ∀ s, s.openLabels = o → JK o (f s)) :
    JK o (MonadState.get >>= f) := by
  refine ⟨OLKeep.getBind (fun s hs => (hf s hs).keep), fun σ τ l d σ1 τ1 hσ h => ?_⟩
  rw [run_bind, run_get] at h
  exact (hf σ hσ).nj _ _ _ _ _ _ hσ h

/-- `tryCatch` has `JK` if its body does and its handler does on every signal that is not a `jump_` to an open
block, which are the only ones the body returns. -/
theorem JK.tryCatch {o : List String} {x : EvalM PM α} {h : Control → EvalM PM α} (hx : JK o x)
    (hh : ∀ c, (∀ l d, c = .jump_ l d → l ∉ o) → JK o (h c)) : JK o (MonadExcept.tryCatch x h) := by
  have hc : ∀ σ τ c σ2 τ2, σ.openLabels = o → run x σ τ = .ok ((.error c, σ2), τ2) →
      σ2.openLabels = o ∧ ∀ l d, c = .jump_ l d → l ∉ o := fun σ τ c σ2 τ2 hσ hr =>
    ⟨hx.keep.keep _ _ _ _ _ hσ hr, fun l d e => hx.nj _ _ _ _ _ _ hσ (e ▸ hr)⟩
  refine ⟨⟨fun σ τ r σ1 τ1 hσ he => ?_⟩, fun σ τ l d σ1 τ1 hσ he => ?_⟩
  · rw [run_tryCatch] at he
    rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
    · cases he
    · obtain ⟨h1, h2⟩ := hc _ _ _ _ _ hσ hr
      exact (hh c h2).keep.keep _ _ _ _ _ h1 he
    · simp only [Except.ok.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨-, rfl⟩, -⟩ := he
      exact hx.keep.keep _ _ _ _ _ hσ hr
  · rw [run_tryCatch] at he
    rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at he
    · cases he
    · obtain ⟨h1, h2⟩ := hc _ _ _ _ _ hσ hr
      exact (hh c h2).nj _ _ _ _ _ _ h1 he
    · cases he

theorem JK.ite {o : List String} {c : Prop} [Decidable c] {x y : EvalM PM α} (hx : c → JK o x) (hy : ¬ c → JK o y) :
    JK o (if c then x else y) := by
  split
  · exact hx ‹_›
  · exact hy ‹_›

theorem JK.map {o : List String} {x : EvalM PM α} (f : α → β) (hx : JK o x) : JK o (f <$> x) := by
  simp only [map_eq_pure_bind]
  exact hx.bind (fun _ => JK.pure _)

theorem JK.forM {o : List String} {l : List β} {f : β → EvalM PM PUnit} (h : ∀ b, JK o (f b)) :
    JK o (l.forM f) := by
  induction l with
  | nil => exact JK.pure _
  | cons b bs ih => exact (h b).bind (fun _ => ih)

theorem JK.mapM {o : List String} {l : List β} {f : β → EvalM PM γ} (h : ∀ b, JK o (f b)) :
    JK o (l.mapM f) := by
  induction l with
  | nil => exact JK.pure _
  | cons b bs ih =>
    simp only [List.mapM_cons]
    exact (h b).bind (fun _ => ih.bind (fun _ => JK.pure _))

theorem JK.forIn {o : List String} {l : List β} {b : γ} {f : β → γ → EvalM PM (ForInStep γ)}
    (h : ∀ x c, JK o (f x c)) : JK o (forIn l b f) := by
  induction l generalizing b with
  | nil => exact JK.pure _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine (h x b).bind (fun r => ?_)
    cases r with
    | done c => exact JK.pure _
    | yield c => exact ih

theorem JK.arrayMapM {o : List String} {l : Array β} {f : β → EvalM PM γ} (h : ∀ b, JK o (f b)) :
    JK o (l.mapM f) := by
  simp only [Array.mapM_eq_mapM_toList, Functor.map]
  exact (JK.mapM h).bind (fun _ => JK.pure _)

theorem JK.muteE {o : List String} {x : EvalM PM α} (hx : JK o x) : JK o (Interpreter.muteE x) := by
  refine ⟨hx.keep.muteE, fun σ τ l d σ1 τ1 hσ h => ?_⟩
  rw [run_muteE] at h
  rcases hr : run x { σ with muted := true } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · simp [muteR] at h
  · simp only [muteR, Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    exact hx.nj { σ with muted := true } _ _ _ _ _ hσ hr
  · simp [muteR] at h

theorem JK.muteSel {o : List String} {c : Prop} [Decidable c] {x : EvalM PM α} (hx : JK o x) :
    JK o ((if c then Interpreter.muteE else id) x) := by
  split
  · exact hx.muteE
  · exact hx

/-- An action whose value is `none` or a signal it caught, and the open labels it ends with. -/
structure JKC (o : List String) (x : EvalM PM (Option Control)) : Prop where
  jk : JK o x
  val : ∀ σ τ a σ1 τ1, σ.openLabels = o → run x σ τ = .ok ((.ok a, σ1), τ1) →
    ∀ c, a = some c → ∀ l d, c = .jump_ l d → l ∉ o

theorem JKC.pure_none {o : List String} : JKC o (pure none) :=
  ⟨JK.pure _, fun σ τ a σ1 τ1 _ h c hc => by
    rw [run_pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    cases hc⟩

theorem JKC.pure_some {o : List String} {c : Control} (hc : ∀ l d, c = .jump_ l d → l ∉ o) : JKC o (pure (some c)) :=
  ⟨JK.pure _, fun σ τ a σ1 τ1 _ h c' hc' => by
    rw [run_pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    cases hc'
    exact hc⟩

theorem JKC.throw {o : List String} (c : Control) (hc : ∀ l d, c = .jump_ l d → l ∉ o) :
    JKC o (throw c) :=
  ⟨JK.throw c hc, fun σ τ a σ1 τ1 _ h => by rw [run_throw] at h; cases h⟩

theorem JKC.bindNone {o : List String} {x : EvalM PM PUnit} (hx : JK o x) : JKC o (x >>= fun _ => pure none) := by
  refine ⟨hx.bind (fun _ => JK.pure _), fun σ τ a σ1 τ1 _ h c hc => ?_⟩
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c' | u, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · cases h
  · dsimp only at h
    rw [run_pure] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    cases hc

/-- An action with `JK` followed by one that returns `none` or a caught signal. -/
theorem JKC.bindL {o : List String} {x : EvalM PM α} {f : α → EvalM PM (Option Control)} (hx : JK o x)
    (hf : ∀ a, JKC o (f a)) : JKC o (x >>= f) := by
  refine ⟨hx.bind (fun a => (hf a).jk), fun σ τ a σ1 τ1 hσ h => ?_⟩
  rw [run_bind] at h
  rcases hr : run x σ τ with e | ⟨⟨c | b, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · cases h
  · exact (hf b).val _ _ _ _ _ (hx.keep.keep _ _ _ _ _ hσ hr) h

/-- `tryCatch` that returns `none` or the signal its handler caught keeps `JKC`. -/
theorem JKC.tryCatch {o : List String} {x : EvalM PM (Option Control)} {h : Control → EvalM PM (Option Control)}
    (hx : JKC o x) (hh : ∀ c, (∀ l d, c = .jump_ l d → l ∉ o) → JKC o (h c)) : JKC o (MonadExcept.tryCatch x h) := by
  refine ⟨JK.tryCatch hx.jk (fun c hc => (hh c hc).jk), fun σ τ a σ1 τ1 hσ he => ?_⟩
  rw [run_tryCatch] at he
  rcases hr : run x σ τ with e | ⟨⟨c | a', σ2⟩, τ2⟩ <;> rw [hr] at he
  · cases he
  · exact (hh c (fun l d e => hx.jk.nj _ _ _ _ _ _ hσ (e ▸ hr))).val _ _ _ _ _
      (hx.jk.keep.keep _ _ _ _ _ hσ hr) he
  · simp only [Except.ok.injEq, Prod.mk.injEq] at he
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := he
    exact hx.val _ _ _ _ _ hσ hr

theorem JKC.bind {o : List String} {x : EvalM PM (Option Control)} {f : Option Control → EvalM PM β} (hx : JKC o x)
    (hf : ∀ a, (∀ c, a = some c → ∀ l d, c = .jump_ l d → l ∉ o) → JK o (f a)) : JK o (x >>= f) := by
  refine ⟨⟨fun σ τ r σ1 τ1 hσ h => ?_⟩, fun σ τ l d σ1 τ1 hσ h => ?_⟩
  · rw [run_bind] at h
    rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨-, rfl⟩, -⟩ := h
      exact hx.jk.keep.keep _ _ _ _ _ hσ hr
    · exact (hf a (hx.val _ _ _ _ _ hσ hr)).keep.keep _ _ _ _ _ (hx.jk.keep.keep _ _ _ _ _ hσ hr) h
  · rw [run_bind] at h
    rcases hr : run x σ τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact hx.jk.nj _ _ _ _ _ _ hσ hr
    · exact (hf a (hx.val _ _ _ _ _ hσ hr)).nj _ _ _ _ _ _ (hx.jk.keep.keep _ _ _ _ _ hσ hr) h

/-- A labelled block's label is open while its statements run, so a `jump_` that leaves them is to none of the
labels open outside it either. -/
theorem JK.withOpenLabel {o : List String} (l : String) {x : EvalM PM α} (hx : JK (l :: o) x) :
    JK o (Interpreter.withOpenLabel l x) := by
  refine ⟨OLKeep.withOpenLabel l x, fun σ τ l' d σ1 τ1 hσ h => ?_⟩
  rw [run_withOpenLabel] at h
  rcases hr : run x { σ with openLabels := l :: σ.openLabels } τ with e | ⟨⟨c | a, σ2⟩, τ2⟩ <;> rw [hr] at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq, Except.error.injEq] at h
    obtain ⟨⟨rfl, -⟩, -⟩ := h
    have := hx.nj { σ with openLabels := l :: σ.openLabels } _ _ _ _ _ (by rw [hσ]) hr
    exact fun hm => this (List.mem_cons_of_mem _ hm)
  · cases h

set_option hygiene false in
macro "jk_tac" : tactic => `(tactic|
  repeat' (first
    | with_reducible apply JK.muteSel
    | with_reducible apply JK.muteE
    | with_reducible refine JK.tryCatch ?_ ?_
    | with_reducible apply JK.getBind
    | with_reducible refine JKC.bind ?_ (fun _ _ => ?_)
    | with_reducible refine JKC.tryCatch ?_ (fun _ _ => ?_)
    | with_reducible refine JKC.bindNone ?_
    | with_reducible refine JKC.bindL ?_ (fun _ => ?_)
    | with_unfolding_none exact JKC.pure_none
    | (with_unfolding_none refine JKC.pure_some ?_; first | assumption | (intro _ _ h; cases h; done))
    | (with_unfolding_none refine JKC.throw _ ?_; first | assumption | (intro _ _ h; cases h; done))
    | with_reducible apply JK.bind
    | with_reducible refine JK.ite (fun _ => ?_) (fun _ => ?_)
    | with_reducible apply JK.map
    | with_reducible apply JK.forM
    | with_reducible apply JK.mapM
    | with_reducible apply JK.forIn
    | with_reducible apply JK.arrayMapM
    | with_reducible apply JK.withBlockScope
    | with_reducible apply JK.withOperandWindow
    | with_unfolding_none exact JK.pure _
    | (with_unfolding_none refine JK.throw _ ?_; first | assumption | (intro _ _ h; cases h; done))
    | (with_unfolding_none refine JK.throwSome _ ?_; assumption)
    | with_unfolding_none exact JK.get
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
    | with_unfolding_none exact JK.liftM _
    | with_reducible apply JK.withOpenLabel
    | with_unfolding_none refine JK.modify (fun σ hσ => ?_)
    | with_unfolding_none refine JK.set _ ?_
    | refine fun _ => ?_
    | dsimp only
    | split
    | with_reducible exact jk_hostFail _ _
    | with_reducible exact jk_evalError _ _
    | with_reducible exact jk_refuse _ _
    | with_reducible exact jk_stuckError _ _
    | with_reducible exact jk_chargeStep _
    | with_reducible exact jk_enterChild _ _ _ _
    | with_reducible exact jk_chargeIteration _ _
    | with_reducible exact jk_emitEvent _ _
    | with_reducible exact jk_chooseValue _ _ _
    | with_reducible exact jk_popOperand _
    | with_reducible exact jk_missingPrelude _ _ _
    | with_reducible exact jk_noFitPrelude _ _ _ _
    | with_reducible exact jk_strictField _ _ _
    | with_reducible exact jk_allocateObject _
    | with_reducible exact jk_readField _ _ _
    | with_reducible exact jk_writeField _ _ _ _
    | with_reducible exact jk_arrayObject _ _
    | with_reducible exact jk_arrayPosition _ _ _
    | with_reducible exact jk_readElement _ _ _
    | with_reducible exact jk_writeElement _ _ _ _
    | with_reducible exact jk_resolveOverride _ _ _ _
    | with_reducible exact jk_resolveMethod _ _ _
    | with_reducible exact jk_coroInstance _ _ _
    | with_reducible exact jk_evalYield _
    | with_reducible exact jk_checkExcType _ _ _
    | with_reducible exact jk_checkCaught _ _ _
    | with_reducible exact jk_assignLocal _ _ _
    | with_reducible exact jk_writeUpdate _ _ _
    | with_reducible apply jk_returnedValues
    | with_reducible apply jk_preconditionValue
    | fail "jk_tac"))

section Helpers

variable {cfg : ExternalBackendM PM}

theorem jk_enterChild (base : List Nat) (k : Nat) (childSeek : Option (List Nat)) :
    KeepsJK (enterChild base k childSeek : EvalM PM Unit) := fun o => by
  unfold enterChild; jk_tac

theorem jk_hostFail (msg : String) : KeepsJK (hostFail msg : EvalM PM α) := fun o => by
  unfold hostFail; exact JK.liftM _

theorem jk_chargeStep : KeepsJK (chargeStep : EvalM PM Unit) := fun o => by
  unfold chargeStep; jk_tac

theorem jk_chargeIteration (b : StmtExprMd) : KeepsJK (chargeIteration b : EvalM PM Unit) := fun o => by
  unfold chargeIteration; jk_tac

theorem jk_emitEvent (e : Event) : KeepsJK (emitEvent e : EvalM PM Unit) := fun o => by
  unfold emitEvent; exact JK.liftM _

theorem jk_chooseValue (ty : Option HighType) (d : Value) : KeepsJK (chooseValue ty d : EvalM PM Value) :=
  fun o => by
  unfold chooseValue; exact JK.liftM _

theorem jk_evalError (msg : String) : KeepsJK (evalError msg : EvalM PM α) := fun o => by
  unfold evalError; jk_tac

theorem jk_refuse (msg : String) : KeepsJK (refuse msg : EvalM PM α) := fun o => by
  unfold refuse; jk_tac

theorem jk_stuckError (msg : String) : KeepsJK (stuckError msg : EvalM PM α) := fun o => by
  unfold stuckError; exact JK.liftM _

theorem jk_popOperand : KeepsJK (popOperand : EvalM PM Value) := fun o => by
  unfold popOperand; jk_tac

theorem jk_returnedValues (proc : Procedure) (restore : EvalM PM Unit) (hr : KeepsJK restore)
    (vs : List Value) : KeepsJK (returnedValues proc restore vs) := fun o => by
  have hr := hr o
  unfold returnedValues; jk_tac

theorem jk_missingPrelude (name : String) (args : List Value) :
    KeepsJK (missingPrelude name args : EvalM PM Unit) := fun o => by
  unfold missingPrelude; jk_tac

theorem jk_noFitPrelude (index : ProgramIndex) (op : Operation) (args : List Value) :
    KeepsJK (noFitPrelude index op args : EvalM PM Unit) := fun o => by
  unfold noFitPrelude; jk_tac

theorem jk_strictField (target : Value) (field : Identifier) :
    KeepsJK (strictField cfg target field : EvalM PM Unit) := fun o => by
  unfold strictField; jk_tac

theorem jk_allocateObject : KeepsJK (allocateObject : EvalM PM Value) := fun o => by
  unfold allocateObject; jk_tac

theorem jk_readField (target : Value) (name : String) : KeepsJK (readField target name : EvalM PM Value) :=
  fun o => by
  unfold readField; jk_tac

theorem jk_writeField (target : Value) (name : String) (v : Value) :
    KeepsJK (writeField target name v : EvalM PM Unit) := fun o => by
  unfold writeField; jk_tac

theorem jk_arrayObject (target : Value) :
    KeepsJK (arrayObject target : EvalM PM (Nat × HeapObject)) := fun o => by
  unfold arrayObject; jk_tac

theorem jk_arrayPosition (obj : HeapObject) (index : Value) :
    KeepsJK (arrayPosition obj index : EvalM PM Nat) := fun o => by
  unfold arrayPosition; jk_tac

theorem jk_readElement (target index : Value) :
    KeepsJK (readElement target index : EvalM PM Value) := fun o => by
  unfold readElement; jk_tac

theorem jk_writeElement (target index v : Value) :
    KeepsJK (writeElement target index v : EvalM PM Unit) := fun o => by
  unfold writeElement; jk_tac

theorem jk_resolveOverride (target : Value) (id : Nat) (static : Procedure) :
    KeepsJK (resolveOverride target id static : EvalM PM Procedure) := fun o => by
  unfold resolveOverride; jk_tac

theorem jk_resolveMethod (target : Value) (name : String) :
    KeepsJK (resolveMethod target name : EvalM PM Procedure) := fun o => by
  unfold resolveMethod; jk_tac

theorem jk_coroInstance (v : Value) (what : String) :
    KeepsJK (coroInstance v what : EvalM PM (Nat × CoroState)) := fun o => by
  unfold coroInstance; jk_tac

theorem jk_evalYield : KeepsJK (evalYield : EvalM PM Value) := fun o => by
  unfold evalYield; jk_tac

theorem jk_checkExcType (ty : HighType) (v : Value) : KeepsJK (checkExcType ty v : EvalM PM Unit) :=
  fun o => by
  unfold checkExcType; jk_tac

theorem jk_checkCaught (catches : List CatchClause) (v : Value) :
    KeepsJK (checkCaught catches v : EvalM PM Unit) := fun o => by
  unfold checkCaught; jk_tac

theorem jk_assignLocal (name : Identifier) (v : Value) : KeepsJK (assignLocal name v : EvalM PM Unit) :=
  fun o => by
  unfold assignLocal; jk_tac

theorem jk_writeUpdate (u : UpdateTarget) (v : Value) : KeepsJK (writeUpdate u v : EvalM PM Unit) :=
  fun o => by
  unfold writeUpdate; jk_tac

theorem jk_preconditionValue (ev : StmtExprMd → EvalM PM Value) (hev : ∀ e, KeepsJK (ev e))
    (proc : Procedure) (args : List Value) : KeepsJK (preconditionValue cfg ev proc args) := fun o => by
  have hev := fun e => hev e o
  unfold preconditionValue; jk_tac

end Helpers

theorem JK.withBlockScope {o : List String} {l : List StmtExprMd} {x : EvalM PM α} (hx : JK o x) :
    JK o (Interpreter.withBlockScope l x) := by
  unfold Interpreter.withBlockScope
  jk_tac

theorem JK.jumpBoundary {o : List String} {x : EvalM PM α} (hx : JK o x) :
    JK o (Interpreter.jumpBoundary x) := by
  unfold Interpreter.jumpBoundary
  refine JK.tryCatch hx (fun c _ => ?_)
  cases c <;> jk_tac

theorem JK.withOperandWindow {o : List String} {s : StmtExprMd} {x : EvalM PM α} (hx : JK o x) :
    JK o (Interpreter.withOperandWindow s x) := by
  unfold Interpreter.withOperandWindow
  refine JK.getBind (fun st hst => ?_)
  rcases hop : st.operands with _ | ⟨v, vs⟩
  · dsimp only; exact hx
  · dsimp only
    rcases hw : st.operandWindow with _ | _ | ⟨hd, tl⟩
    all_goals dsimp only
    all_goals first | exact hx | jk_tac


variable (cfg : ExternalBackendM PM)

structure JKAt (n : Nat) : Prop where
  scoped_ : ∀ s, KeepsJK (evalScopedStmt cfg n s)
  exprMd : ∀ e, KeepsJK (evalExprMd cfg n e)
  expr : ∀ e, KeepsJK (evalExpr cfg n e)
  assign : ∀ t, KeepsJK (assignTarget cfg n t)
  update : ∀ t, KeepsJK (readForUpdate cfg n t)
  stmt : ∀ s, KeepsJK (evalStmt cfg n s)
  iter : ∀ c b p ci eb, KeepsJK ci → KeepsJK eb → KeepsJK (evalWhileIter cfg c b p ci eb n)
  blockLoop : ∀ ss l invs base, KeepsJK (evalBlockLoop cfg n ss l invs base)
  blockFrom : ∀ ss bl invs k l d, KeepsJK (evalBlockFrom cfg n ss bl invs k l d)
  stmtFrom : ∀ s l d, KeepsJK (evalStmtFrom cfg n s l d)
  runFrom : ∀ ss k l d, KeepsJK (runFrom cfg n ss k l d)
  fin : ∀ f i b k, KeepsJK (runTryFinally cfg n f i b k)
  finish : ∀ f i b k c, KeepsJK (finishCatchClause cfg n f i b k c)
  clauses : ∀ f i b k v j cs, KeepsJK (tryCatchClauses cfg n f i b k v j cs)
  go : ∀ a b s i k ss, KeepsJK (evalStmtListGo cfg n a b s i k ss)
  list : ∀ ss a, KeepsJK (evalStmtList cfg n ss a)
  resume : ∀ t v, KeepsJK (resumeCoroutine cfg n t v)
  outputs : ∀ e, KeepsJK (evalCallOutputs cfg n e)
  callee : ∀ s c a, KeepsJK (invokeCallee cfg n s c a)
  pre : ∀ s p a, KeepsJK (checkPreconditions cfg n s p a)
  post : ∀ p ps fr e x y r, KeepsJK (checkPostconditions cfg n p ps fr e x y r)
  proc : ∀ s p a, KeepsJK (invokeProc cfg n s p a)

set_option maxHeartbeats 4000000 in
/-- `evalScopedStmt` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_scoped_ {n : Nat} (ih : JKAt cfg n) : ∀ s, KeepsJK (evalScopedStmt cfg (n + 1) s) := by
  intro s o; simp only [evalScopedStmt]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalExprMd` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_exprMd {n : Nat} (_ih : JKAt cfg n) : ∀ e, KeepsJK (evalExprMd cfg (n + 1) e) := by
  intro e o
  refine JK.ofNoJ ((keepsAt cfg (n + 1)).exprMd e o) ?_
  simp only [evalExprMd]
  exact noJ_jumpBoundary _

set_option maxHeartbeats 4000000 in
/-- `evalExpr` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_expr {n : Nat} (ih : JKAt cfg n) : ∀ e, KeepsJK (evalExpr cfg (n + 1) e) := by
  intro e o
  cases e
  case Block stmts label invs dec =>
    cases label <;> (simp only [evalExpr]; jk_tac)
  case ContractOf ty f =>
    rcases f with ⟨fv, fs⟩
    cases ty
    case Precondition =>
      cases fv
      case Call r callee args ta => cases r <;> (simp only [evalExpr]; jk_tac)
      all_goals (simp only [evalExpr]; jk_tac)
    all_goals (simp only [evalExpr]; jk_tac)
  case Call r callee args ta => cases r <;> (simp only [evalExpr]; jk_tac)
  all_goals (try (rename_i v; cases v))
  all_goals (simp only [evalExpr]; jk_tac)

set_option maxHeartbeats 4000000 in
/-- `assignTarget` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_assign {n : Nat} (ih : JKAt cfg n) : ∀ t, KeepsJK (assignTarget cfg (n + 1) t) := by
  intro t o; simp only [assignTarget]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `readForUpdate` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_update {n : Nat} (ih : JKAt cfg n) : ∀ t, KeepsJK (readForUpdate cfg (n + 1) t) := by
  intro t o; simp only [readForUpdate]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmt` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_stmt {n : Nat} (ih : JKAt cfg n) : ∀ s, KeepsJK (evalStmt cfg (n + 1) s) := by
  intro s o
  rcases s with ⟨v, src⟩
  cases v
  case While c invs dec body p =>
    rw [evalStmt]; dsimp only
    jk_tac
  case Block stmts label invs dec =>
    cases label
    · simp only [evalStmt]; jk_tac
    · rw [evalStmt]; dsimp only
      jk_tac
  case Call r callee args ta => cases r <;> (simp only [evalStmt]; jk_tac)
  case Goto target dest =>
    simp only [evalStmt]
    refine JK.getBind (fun s hs => ?_)
    refine JK.ite (fun _ => ?_) (fun hn => ?_)
    · cases dest <;> exact JK.throw _ (by intro _ _ h; cases h)
    · refine JK.throw _ (fun l d h => ?_)
      cases h
      rw [← hs]
      simpa [List.contains_iff_mem] using hn
  all_goals (try (rename_i x; cases x))
  all_goals (simp only [evalStmt]; jk_tac)

set_option maxHeartbeats 4000000 in
/-- `evalBlockLoop` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_blockLoop {n : Nat} (ih : JKAt cfg n) :
    ∀ ss l invs base, KeepsJK (evalBlockLoop cfg (n + 1) ss l invs base) := by
  intro ss l invs base o; rw [evalBlockLoop]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalBlockFrom` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_blockFrom {n : Nat} (ih : JKAt cfg n) :
    ∀ ss bl invs k l d, KeepsJK (evalBlockFrom cfg (n + 1) ss bl invs k l d) := by
  intro ss bl invs k l d o
  have _ := ih
  unfold evalBlockFrom
  dsimp only
  jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtFrom` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_stmtFrom {n : Nat} (ih : JKAt cfg n) :
    ∀ s l d, KeepsJK (evalStmtFrom cfg (n + 1) s l d) := by
  intro s l d o
  rcases s with ⟨v, src⟩
  cases v
  case Block stmts bl invs dec =>
    unfold evalStmtFrom
    dsimp only
    jk_tac
  case IfThenElse c th el =>
    unfold evalStmtFrom
    dsimp only
    jk_tac
  all_goals
    unfold evalStmtFrom
    dsimp only
    jk_tac

set_option maxHeartbeats 4000000 in
/-- `runFrom` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_runFrom {n : Nat} (ih : JKAt cfg n) :
    ∀ ss k l d, KeepsJK (runFrom cfg (n + 1) ss k l d) := by
  intro ss k l d o
  unfold runFrom
  dsimp only
  jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalWhileIter` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_iter {n : Nat} (ih : JKAt cfg n) :
    ∀ c b p ci eb, KeepsJK ci → KeepsJK eb → KeepsJK (evalWhileIter cfg c b p ci eb (n + 1)) := by
  intro c b p ci eb hci heb o
  have _ := ih
  have hci := hci o
  have heb := heb o
  rw [evalWhileIter]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `runTryFinally` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_fin {n : Nat} (ih : JKAt cfg n) :
    ∀ f i b k, KeepsJK (runTryFinally cfg (n + 1) f i b k) := by
  intro f i b k o; simp only [runTryFinally]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `finishCatchClause` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_finish {n : Nat} (ih : JKAt cfg n) :
    ∀ f i b k c, KeepsJK (finishCatchClause cfg (n + 1) f i b k c) := by
  intro f i b k c o; simp only [finishCatchClause]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `tryCatchClauses` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_clauses {n : Nat} (ih : JKAt cfg n) :
    ∀ f i b k v j cs, KeepsJK (tryCatchClauses cfg (n + 1) f i b k v j cs) := by
  intro f i b k v j cs o
  cases cs <;> simp only [tryCatchClauses] <;> jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtListGo` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_go {n : Nat} (ih : JKAt cfg n) :
    ∀ a b s i k ss, KeepsJK (evalStmtListGo cfg (n + 1) a b s i k ss) := by
  intro a b s i k ss o
  cases ss <;> simp only [evalStmtListGo] <;> jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalStmtList` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_list {n : Nat} (ih : JKAt cfg n) : ∀ ss a, KeepsJK (evalStmtList cfg (n + 1) ss a) := by
  intro ss a o; simp only [evalStmtList]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `resumeCoroutine` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_resume {n : Nat} (ih : JKAt cfg n) : ∀ t v, KeepsJK (resumeCoroutine cfg (n + 1) t v) := by
  intro t v o; simp only [resumeCoroutine]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `evalCallOutputs` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_outputs {n : Nat} (ih : JKAt cfg n) : ∀ e, KeepsJK (evalCallOutputs cfg (n + 1) e) := by
  intro e o; simp only [evalCallOutputs]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `invokeCallee` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_callee {n : Nat} (ih : JKAt cfg n) : ∀ s c a, KeepsJK (invokeCallee cfg (n + 1) s c a) := by
  intro s c a o; simp only [invokeCallee]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `checkPreconditions` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_pre {n : Nat} (ih : JKAt cfg n) : ∀ s p a, KeepsJK (checkPreconditions cfg (n + 1) s p a) := by
  intro s p a o; simp only [checkPreconditions]; jk_tac

set_option maxHeartbeats 4000000 in
/-- `checkPostconditions` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_post {n : Nat} (ih : JKAt cfg n) :
    ∀ p ps fr e x y r, KeepsJK (checkPostconditions cfg (n + 1) p ps fr e x y r) := by
  intro p ps fr e x y r o; simp only [checkPostconditions]; jk_tac

set_option maxHeartbeats 16000000 in
/-- `invokeProc` keeps the open labels and lets no jump to an open block out at fuel `n + 1`, given `JKAt cfg n`. -/
private theorem jk_s_proc {n : Nat} (_ih : JKAt cfg n) : ∀ s p a, KeepsJK (invokeProc cfg (n + 1) s p a) := by
  intro s p a o
  refine JK.ofNoJ ((keepsAt cfg (n + 1)).proc s p a o) ?_
  simp only [invokeProc]
  exact noJ_jumpBoundary _

/-- Every one of the interpreter's mutual functions, run with any fuel `n` and any external backend `cfg`,
leaves the open labels as it found them and never returns a `jump_` to a block that was open when it
started. -/
theorem jkAt : ∀ n, JKAt cfg n
  | 0 => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      intros <;> (try intro o) <;> first
        | (rw [evalExpr]; exact JK.throw _ (fun _ _ h => by cases h))
        | (rw [evalStmt]; exact JK.throw _ (fun _ _ h => by cases h))
        | (rw [evalWhileIter]; exact JK.throw _ (fun _ _ h => by cases h))
        | (rw [evalBlockLoop]; exact JK.throw _ (fun _ _ h => by cases h))
        | (simp only [evalScopedStmt, evalExprMd, assignTarget, readForUpdate, evalBlockFrom, evalStmtFrom, runFrom,
            runTryFinally, finishCatchClause, tryCatchClauses, evalStmtListGo, evalStmtList, resumeCoroutine,
            evalCallOutputs, invokeCallee, checkPreconditions, checkPostconditions, invokeProc]
           exact JK.throw _ (fun _ _ h => by cases h))
  | n + 1 => by
    have ih := jkAt n
    exact ⟨jk_s_scoped_ cfg ih, jk_s_exprMd cfg ih, jk_s_expr cfg ih, jk_s_assign cfg ih, jk_s_update cfg ih,
      jk_s_stmt cfg ih, jk_s_iter cfg ih, jk_s_blockLoop cfg ih, jk_s_blockFrom cfg ih, jk_s_stmtFrom cfg ih,
      jk_s_runFrom cfg ih, jk_s_fin cfg ih, jk_s_finish cfg ih, jk_s_clauses cfg ih, jk_s_go cfg ih, jk_s_list cfg ih,
      jk_s_resume cfg ih, jk_s_outputs cfg ih, jk_s_callee cfg ih, jk_s_pre cfg ih, jk_s_post cfg ih, jk_s_proc cfg ih⟩

end Strata.Laurel.PassSemantics
