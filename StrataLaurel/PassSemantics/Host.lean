/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Implementation.Interpreter

/-!
# The proof host for the Laurel interpreter

Pass correctness is stated against the real interpreter (`Interpreter.lean`), run in
the pure host `PM`, not against a separate reference interpreter.

* `PM := StateT Trace (Except HErr)`. `Trace` records the emitted events and
  answers `choose` from an oracle, so nondeterministic values are an input of the
  run rather than fixed defaults.
* `run x σ τ` runs an interpreter action; `OOF r` says the run ran out of fuel.
* `Le x y`: whenever `x` does not run out of fuel, `y` gives exactly the same result,
  state, events and oracle position. `Le` is a structure rather than a definition so
  that `intro` does not unfold it.
* `bind_le`, `tryCatch_le`, `ite_le`, `forM_le`, `mapM_le`, `forIn_le`, `map_le`:
  `Le` is preserved by each combinator the interpreter is written with.
  `tryCatch_le` needs `KeepsOOF`: the handler must rethrow `outOfFuel`.
* `mono_tac` applies those lemmas. Its `exact`/`assumption` steps run
  `with_reducible`, because unifying two large interpreter terms at default
  transparency is very slow.

With monotonicity (`RealMono.lean`), "the program has result `r`" is
`∃ n, ¬ OOF (run (X n) σ τ) ∧ run (X n) σ τ = r`, which does not depend on how much
fuel each side charges. That is why the pass theorems hold in both directions, and so
also cover divergence.
-/

namespace Strata.Laurel.PassSemantics

open Strata.Laurel
open Strata.Laurel.Interpreter

structure Trace where
  events : Array Event := #[]
  oracle : Nat → Option HighType → Value → Value := fun _ _ d => d
  next : Nat := 0
  init : String → Option Value := fun _ => none
  heap0 : Option (Array HeapObject) := none

inductive HErr where
  | fail (msg : String)
  | stuck (msg : String)

def HErr.isStuck : HErr → Prop
  | .stuck _ => True
  | .fail _ => False

abbrev PM := StateT Trace (Except HErr)

instance : InterpHost PM where
  fail msg := throw (.fail msg)
  stuck msg := throw (.stuck msg)
  emit e := modify fun t => { t with events := t.events.push e }
  choose ty d := modifyGet fun t => (t.oracle t.next ty d, { t with next := t.next + 1 })
  chooseInit k _ d := fun t => pure ((t.init k).getD d, t)
  chooseHeap h := fun t => pure (t.heap0.getD h, t)
  recover x y := fun t => match x t with
    | .error (.fail _) => y t
    | r => r
  mute x := fun t => match x t with
    | .ok (a, t') => .ok (a, { t' with events := t.events })
    | .error e => .error e

abbrev R (α : Type) := Except HErr ((Except Control α × EvalState) × Trace)

def run (x : EvalM PM α) (σ : EvalState) (τ : Trace) : R α := (x.run.run σ).run τ

def OOF : R α → Prop
  | .ok ((.error .outOfFuel, _), _) => True
  | _ => False

structure Le (x y : EvalM PM α) : Prop where
  eq : ∀ σ τ, ¬ OOF (run x σ τ) → run y σ τ = run x σ τ

theorem get_bind_ignore (x : EvalM PM α) : (get >>= fun _ => x) = x := rfl

theorem strictField_none {cfg : ExternalBackendM PM} (h : cfg.strict = none) (v : Value) (f : Identifier)
    (x : EvalM PM α) : (strictField cfg v f >>= fun _ => x) = x := by
  simp only [strictField, h]
  exact pure_bind _ _

/-- Every interpreter action is related to itself by `Le`. -/
theorem Le.refl (x : EvalM PM α) : Le x x := ⟨fun _ _ _ => rfl⟩

/-- `Le` is transitive: if `y` gives the result of `x` whenever `x` does not run out of fuel, and `z`
gives the result of `y` whenever `y` does not, then `z` gives the result of `x` whenever `x` does
not run out of fuel. -/
theorem Le.trans {x y z : EvalM PM α} (h1 : Le x y) (h2 : Le y z) : Le x z := by
  refine ⟨fun σ τ h => ?_⟩
  rw [h2.eq σ τ (by rw [h1.eq σ τ h]; exact h), h1.eq σ τ h]

theorem run_bind (x : EvalM PM α) (f : α → EvalM PM β) (σ : EvalState) (τ : Trace) :
    run (x >>= f) σ τ = match run x σ τ with
      | .error e => .error e
      | .ok ((.error c, σ'), τ') => .ok ((.error c, σ'), τ')
      | .ok ((.ok a, σ'), τ') => run (f a) σ' τ' := by
  unfold run
  show (x σ τ >>= fun p => _) = _
  simp only [StateT.run, ExceptT.run]
  rcases x σ τ with e | ⟨⟨_ | a, σ'⟩, τ'⟩ <;> rfl

theorem run_tryCatch (x : EvalM PM α) (h : Control → EvalM PM α) (σ : EvalState) (τ : Trace) :
    run (tryCatch x h) σ τ = match run x σ τ with
      | .ok ((.error c, σ'), τ') => run (h c) σ' τ'
      | r => r := by
  unfold run
  show (x σ τ >>= fun p => _) = _
  simp only [StateT.run, ExceptT.run]
  rcases x σ τ with e | ⟨⟨_ | a, σ'⟩, τ'⟩ <;> rfl

theorem OOF_err {c : Control} {σ : EvalState} {τ : Trace} :
    OOF (.ok ((.error c, σ), τ) : R α) ↔ c = .outOfFuel := by
  cases c <;> simp [OOF]

theorem not_OOF_ok {a : α} {σ : EvalState} {τ : Trace} : ¬ OOF (.ok ((.ok a, σ), τ) : R α) := by
  simp [OOF]

theorem not_OOF_error {e : HErr} : ¬ OOF (.error e : R α) := by
  simp [OOF]

/-- `Le` is preserved by `bind`: if `Le x x'` and `Le (f a) (f' a)` for every value `a`, then
`Le (x >>= f) (x' >>= f')`. -/
theorem bind_le {x x' : EvalM PM α} {f f' : α → EvalM PM β} (hx : Le x x')
    (hf : ∀ a, Le (f a) (f' a)) : Le (x >>= f) (x' >>= f') := by
  refine ⟨fun σ τ h => ?_⟩
  simp only [run_bind] at h ⊢
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ'⟩, τ'⟩ <;> rw [hr] at h <;> dsimp only at h
  · rw [(hx.eq σ τ (by rw [hr]; exact not_OOF_error)).trans hr]
  · rw [(hx.eq σ τ (by rw [hr, OOF_err]; exact fun hc => h (OOF_err.mpr hc))).trans hr]
  · rw [(hx.eq σ τ (by rw [hr]; exact not_OOF_ok)).trans hr]
    exact (hf a).eq σ' τ' h

def KeepsOOF (h : Control → EvalM PM α) : Prop := ∀ σ τ, OOF (run (h .outOfFuel) σ τ)

/-- `Le` is preserved by `tryCatch`: if `Le x x'`, `Le (h c) (h' c)` for every control signal `c`, and
the handler `h` rethrows `outOfFuel` (`KeepsOOF h`), then `Le (tryCatch x h) (tryCatch x' h')`. -/
theorem tryCatch_le {x x' : EvalM PM α} {h h' : Control → EvalM PM α} (hx : Le x x')
    (hh : ∀ c, Le (h c) (h' c)) (hk : KeepsOOF h) : Le (tryCatch x h) (tryCatch x' h') := by
  refine ⟨fun σ τ hn => ?_⟩
  simp only [run_tryCatch] at hn ⊢
  rcases hr : run x σ τ with e | ⟨⟨c | a, σ'⟩, τ'⟩ <;> rw [hr] at hn <;> dsimp only at hn
  · rw [(hx.eq σ τ (by rw [hr]; exact not_OOF_error)).trans hr]
  · have hc : c ≠ .outOfFuel := by
      rintro rfl
      exact hn (hk σ' τ')
    rw [(hx.eq σ τ (by rw [hr, OOF_err]; exact hc)).trans hr]
    exact (hh c).eq σ' τ' hn
  · rw [(hx.eq σ τ (by rw [hr]; exact not_OOF_ok)).trans hr]

/-- `Le` is preserved by `if`: if `Le x x'` and `Le y y'`, then
`Le (if c then x else y) (if c then x' else y')`. -/
theorem ite_le {c : Prop} [Decidable c] {x x' y y' : EvalM PM α} (hx : Le x x') (hy : Le y y') :
    Le (if c then x else y) (if c then x' else y') := by
  split
  · exact hx
  · exact hy

/-- `Le` is preserved by `List.forM`: if `Le (f b) (g b)` for every element `b`, then
`Le (l.forM f) (l.forM g)` for every list `l`. -/
theorem forM_le {l : List β} {f g : β → EvalM PM PUnit} (h : ∀ b, Le (f b) (g b)) :
    Le (l.forM f) (l.forM g) := by
  induction l with
  | nil => exact Le.refl _
  | cons b bs ih => exact bind_le (h b) (fun _ => ih)

/-- `Le` is preserved by `List.mapM`: if `Le (f b) (g b)` for every element `b`, then
`Le (l.mapM f) (l.mapM g)` for every list `l`. -/
theorem mapM_le {l : List β} {f g : β → EvalM PM γ} (h : ∀ b, Le (f b) (g b)) :
    Le (l.mapM f) (l.mapM g) := by
  induction l with
  | nil => exact Le.refl _
  | cons b bs ih =>
    simp only [List.mapM_cons]
    exact bind_le (h b) (fun _ => bind_le ih (fun _ => Le.refl _))

theorem run_pure (a : α) (σ : EvalState) (τ : Trace) :
    run (pure a : EvalM PM α) σ τ = .ok ((.ok a, σ), τ) := rfl

theorem run_throw (c : Control) (σ : EvalState) (τ : Trace) :
    run (throw c : EvalM PM α) σ τ = .ok ((.error c, σ), τ) := rfl

theorem run_modify (f : EvalState → EvalState) (σ : EvalState) (τ : Trace) :
    run (modify f : EvalM PM PUnit) σ τ = .ok ((.ok (), f σ), τ) := rfl

theorem run_get (σ : EvalState) (τ : Trace) :
    run (get : EvalM PM EvalState) σ τ = .ok ((.ok σ, σ), τ) := rfl

/-- `Le` is preserved by `forIn` over a list: if `Le (f x c) (g x c)` for every element `x` and
accumulator `c`, then `Le (forIn l b f) (forIn l b g)` for every list `l` and initial value `b`. -/
theorem forIn_le {l : List β} {b : γ} {f g : β → γ → EvalM PM (ForInStep γ)}
    (h : ∀ x c, Le (f x c) (g x c)) : Le (forIn l b f) (forIn l b g) := by
  induction l generalizing b with
  | nil => exact Le.refl _
  | cons x xs ih =>
    simp only [List.forIn_cons]
    refine bind_le (h x b) (fun r => ?_)
    cases r with
    | done c => exact Le.refl _
    | yield c => exact ih

/-- `Le` is preserved by `Array.mapM`: if `Le (f b) (g b)` for every element `b`, then
`Le (l.mapM f) (l.mapM g)` for every array `l`. -/
theorem arrayMapM_le {l : Array β} {f g : β → EvalM PM γ} (h : ∀ b, Le (f b) (g b)) :
    Le (l.mapM f) (l.mapM g) := by
  simp only [Array.mapM_eq_mapM_toList, Functor.map]
  exact bind_le (mapM_le h) (fun _ => Le.refl _)

/-- `Le` is preserved by `Functor.map`: if `Le x x'`, then `Le (f <$> x) (f <$> x')` for every `f`. -/
theorem map_le {x x' : EvalM PM α} (f : α → β) (hx : Le x x') : Le (f <$> x) (f <$> x') := by
  simp only [map_eq_pure_bind]
  exact bind_le hx (fun _ => Le.refl _)

def muteR (σ : EvalState) (τ : Trace) : R α → R α
  | .ok ((r, σ'), τ') => .ok ((r, { σ' with assertFailures := σ.assertFailures, muted := σ.muted }),
      { τ' with events := τ.events })
  | .error e => .error e

theorem run_muteE (x : EvalM PM α) (σ : EvalState) (τ : Trace) :
    run (muteE x) σ τ = muteR σ τ (run x { σ with muted := true } τ) := by
  unfold run muteE
  simp only [ExceptT.run_mk, StateT.run, bind, StateT.bind, InterpHost.mute, pure, StateT.pure]
  rcases h : (ExceptT.run x) { σ with muted := true } τ with _ | ⟨⟨r, σ'⟩, τ'⟩
  · simp only [muteR]
    rfl
  · simp only [muteR]
    rfl

theorem OOF_muteR {σ : EvalState} {τ : Trace} (r : R α) : OOF (muteR σ τ r) ↔ OOF r := by
  rcases r with _ | ⟨⟨c | _, _⟩, _⟩ <;> (try cases c) <;> simp [muteR, OOF]

/-- `Le` is preserved by `muteE`, which runs an action with checks muted and then restores the
events, the assertion failures and the `muted` flag: if `Le x y`, then `Le (muteE x) (muteE y)`. -/
theorem muteE_le {x y : EvalM PM α} (h : Le x y) : Le (muteE x) (muteE y) := by
  refine ⟨fun σ τ hn => ?_⟩
  rw [run_muteE] at hn ⊢
  rw [run_muteE, h.eq _ _ (fun ho => hn ((OOF_muteR _).mpr ho))]

theorem run_emitEvent (e : Event) (σ : EvalState) (τ : Trace) :
    run (emitEvent e : EvalM PM Unit) σ τ = .ok ((.ok (), σ), { τ with events := τ.events.push e }) := rfl

theorem muteSel_apply {c : Prop} [Decidable c] (x : EvalM PM α) :
    (if c then muteE else id) x = if c then muteE x else x := by
  split <;> rfl

/-- `Le` is preserved by optional muting: if `Le x y`, then applying `if c then muteE else id` to both
sides keeps them related by `Le`. -/
theorem muteSel_le {c : Prop} [Decidable c] {x y : EvalM PM α} (h : Le x y) :
    Le ((if c then muteE else id) x) ((if c then muteE else id) y) := by
  split
  · exact muteE_le h
  · exact h

macro "keeps_oof" : tactic => `(tactic|
  (intro σ τ; simp [run_bind, run_throw, run_modify, run_pure, run_get, OOF, escapeSig]))

macro "mono_tac" : tactic => `(tactic|
  repeat' (first
    | with_reducible exact Le.refl _
    | with_reducible assumption
    | with_reducible apply muteSel_le
    | with_reducible apply muteE_le
    | ((with_reducible show KeepsOOF _); keeps_oof)
    | with_reducible refine tryCatch_le ?_ ?_ ?_
    | with_reducible apply bind_le
    | with_reducible apply ite_le
    | with_reducible apply map_le
    | apply forM_le
    | apply mapM_le
    | apply forIn_le
    | apply arrayMapM_le
    | apply withBlockScope_le
    | refine fun _ => ?_
    | split))

end Strata.Laurel.PassSemantics
