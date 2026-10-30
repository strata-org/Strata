/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-!
## `Except` Utilities
-/

public section

namespace Except

/-- `Except`'s bind on a success, as a rewrite. -/
theorem ok_bind {E α β} (a : α) (h : α → Except E β) :
    ((Except.ok a : Except E α) >>= h) = h a := rfl

/-- `Except`'s bind on an error, as a rewrite. -/
theorem error_bind {E α β} (e : E) (h : α → Except E β) :
    ((Except.error e : Except E α) >>= h) = .error e := rfl

/-- If `mapError f e` succeeds with `v`, then `e` succeeds with `v`. -/
theorem mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

/-- Bind inversion: a bind succeeds exactly when it factors through a
    successful intermediate result. The `mp` direction replaces manual case
    analysis whose `error` branches are impossible. -/
theorem bind_is_ok {E α β} (m : Except E α) (h : α → Except E β) (r : β) :
    ((m >>= h) = .ok r) ↔ ∃ (a : α), m = .ok a ∧ h a = .ok r := by
  match m with
  | .ok a => simp [Bind.bind, Except.bind]
  | .error e => simp [Bind.bind, Except.bind]

/-- A handler that always fails cannot make a failed computation succeed. -/
theorem ok_of_tryCatch {ε α : Type} {x : Except ε α}
    {handler : ε → Except ε α} {a : α}
    (h : tryCatch x handler = .ok a) (hh : ∀ e, ∃ e', handler e = .error e') :
    x = .ok a := by
  cases x with
  | error e =>
    obtain ⟨e', he'⟩ := hh e
    simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch, he',
      reduceCtorEq] at h
  | ok b =>
    simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch,
      Except.ok.injEq] at h
    rw [h]

/-- An `if` whose then-branch fails succeeds exactly when its condition is false and its
    else-branch succeeds. -/
theorem ite_error_then_eq_ok {ε β : Type} {c : Prop} [Decidable c]
    {x : Except ε β} {e : ε} {b : β} :
    (if c then Except.error e else x) = .ok b ↔ ¬ c ∧ x = .ok b := by
  split <;> simp_all

end Except

/-- If `mapM f` succeeds, `f` succeeds on every input, with a result among the outputs. -/
theorem mapM_except_mem_left {α β ε : Type _} (f : α → Except ε β) :
    ∀ (as : List α) (bs : List β), as.mapM f = .ok bs →
      ∀ a ∈ as, ∃ b ∈ bs, f a = .ok b := by
  intro as
  induction as with
  | nil => intro bs h a ha; simp at ha
  | cons hd tl ih =>
    intro bs h a ha
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨bs', hbs', h⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨b', hb', hfb'⟩ := ih bs' hbs' a ha'
      exact ⟨b', List.mem_cons_of_mem b hb', hfb'⟩

/-- `mapM` success gives, for each output, a witnessing input. -/
theorem mapM_except_mem_right {α β ε : Type _} (f : α → Except ε β) :
    ∀ (as : List α) (bs : List β), as.mapM f = .ok bs →
      ∀ b ∈ bs, ∃ a ∈ as, f a = .ok b := by
  intro as
  induction as with
  | nil =>
    intro bs h b hb
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | cons hd tl ih =>
    intro bs h b hb
    rw [List.mapM_cons] at h
    obtain ⟨b0, hb0, h⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨bs', hbs', h⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨hd, List.mem_cons_self, hb0⟩
    · obtain ⟨a, ha, hfa⟩ := ih bs' hbs' b hb'
      exact ⟨a, List.mem_cons_of_mem hd ha, hfa⟩

/-- If a `for` loop that throws when `b` fails succeeds, `b` holds on every element. -/
theorem forIn_guard_all {ε α : Type} (b : α → Bool) (e : α → ε) :
    ∀ (xs : List α) (s r : PUnit),
      (forIn xs s (fun (a : α) (_ : PUnit) =>
        if (!b a) = true then (Except.error (e a) : Except ε (ForInStep PUnit))
        else Except.ok (ForInStep.yield PUnit.unit))) = Except.ok r →
      ∀ a ∈ xs, b a = true := by
  intro xs
  induction xs with
  | nil => intro s r _ a ha; exact absurd ha (by simp)
  | cons x xs ih =>
    intro s r h a ha
    rw [List.forIn_cons] at h
    by_cases hbx : b x = true
    · simp only [hbx, Bool.not_true, Bool.false_eq_true, ite_false,
        pure, Except.pure] at h
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hbx
      · exact ih _ _ (by simpa [bind, Except.bind] using h) a ha'
    · simp only [Bool.not_eq_true] at hbx
      simp only [hbx, Bool.not_false, ite_true, bind, Except.bind, reduceCtorEq] at h

/-- If a left fold of the check `f` succeeds, `f` succeeds on every element. -/
theorem foldlM_check_ok {α ε : Type _} (f : α → Except ε Unit) (l : List α) :
    ∀ u : Unit, List.foldlM (fun _ a => f a) u l = .ok () → ∀ a ∈ l, f a = .ok () := by
  induction l with
  | nil => intro _ _ a ha; exact absurd ha (by simp)
  | cons b rest ih =>
    intro u h a ha
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    · rename_i v hv
      rcases List.mem_cons.mp ha with rfl | ha'
      · rw [hv]
      · exact ih v h a ha'

/-- If a right fold of the check `f` succeeds, `f` succeeds on every element. -/
theorem foldrM_check_ok {α ε : Type _} (f : α → Except ε Unit) :
    ∀ (l : List α), List.foldrM (fun a acc => do let _ ← f a; .ok acc) () l = .ok () →
      ∀ a ∈ l, f a = .ok () := by
  intro l
  induction l with
  | nil => intro _ a ha; exact absurd ha (by simp)
  | cons b rest ih =>
    intro h a ha
    rw [List.foldrM_cons] at h
    simp only [bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    rename_i v hv
    split at h
    · exact absurd h (by simp)
    rename_i hb
    rcases List.mem_cons.mp ha with rfl | ha'
    · rw [hb]
    · exact ih hv a ha'
