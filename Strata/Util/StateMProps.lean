/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! ## `StateM` equations and soundness of folding Boolean checks

Key theorems: `foldlM_and_sound`, `foldrM_and_sound`, `foldlM_or_sound` and `foldlM_option_sound`
(a fold of sound checks is sound), and the equations `stateM_get_apply` and `stateM_bind_apply`. -/

public section

/-- `get` returns the state without changing it. -/
theorem stateM_get_apply {σ : Type _} (m : σ) : (get : StateM σ σ) m = (m, m) := rfl

/-- Sequencing runs the first computation on the state and the second on what it left. -/
theorem stateM_bind_apply {σ α β : Type _} (f : StateM σ α) (g : α → StateM σ β) (m : σ) :
    (f >>= g) m = g (f m).1 (f m).2 := rfl

/-- If each check preserves `W` and returns `true` only for elements satisfying `P`, a left
    `&&`-fold of the checks preserves `W` and returns `true` only if `init = true` and every
    element satisfies `P`. -/
theorem foldlM_and_sound {α σ : Type _} (W : σ → Prop)
    (F : α → StateM σ Bool) (P : α → Prop) :
    ∀ (l : List α), (∀ x ∈ l, ∀ m, W m → W (F x m).2 ∧ ((F x m).1 = true → P x)) →
      ∀ (init : Bool) (m : σ), W m →
        W (List.foldlM (fun accA x => do let b ← F x; pure (accA && b)) init l m).2 ∧
        ((List.foldlM (fun accA x => do let b ← F x; pure (accA && b)) init l m).1 = true →
          init = true ∧ ∀ x ∈ l, P x) := by
  intro l
  induction l with
  | nil =>
    intro _ init m hm
    exact ⟨hm, fun hv => ⟨hv, nofun⟩⟩
  | cons a rest ih =>
    intro hF init m hm
    obtain ⟨hmA, hPA⟩ := hF a List.mem_cons_self m hm
    obtain ⟨hmRest, hRest⟩ :=
      ih (fun x hx => hF x (List.mem_cons_of_mem a hx)) (init && (F a m).1) (F a m).2 hmA
    refine ⟨hmRest, ?_⟩
    intro hv
    obtain ⟨hinit, hall⟩ := hRest hv
    simp only [Bool.and_eq_true] at hinit
    refine ⟨hinit.1, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hPA hinit.2
    · exact hall x hx'

/-- If each check preserves `W` and returns `true` only for elements satisfying `Q`, a left
    `||`-fold of the checks preserves `W` and returns `true` only if `init = true` or some
    element satisfies `Q`. -/
theorem foldlM_or_sound {α σ : Type _} (W : σ → Prop)
    (G : α → StateM σ Bool) (Q : α → Prop) :
    ∀ (l : List α), (∀ x ∈ l, ∀ m, W m → W (G x m).2 ∧ ((G x m).1 = true → Q x)) →
      ∀ (init : Bool) (m : σ), W m →
        W (List.foldlM (fun accC x => do let b ← G x; pure (accC || b)) init l m).2 ∧
        ((List.foldlM (fun accC x => do let b ← G x; pure (accC || b)) init l m).1 = true →
          init = true ∨ ∃ x ∈ l, Q x) := by
  intro l
  induction l with
  | nil =>
    intro _ init m hm
    exact ⟨hm, fun hv => Or.inl hv⟩
  | cons a rest ih =>
    intro hG init m hm
    obtain ⟨hmA, hQA⟩ := hG a List.mem_cons_self m hm
    obtain ⟨hmRest, hRest⟩ :=
      ih (fun x hx => hG x (List.mem_cons_of_mem a hx)) (init || (G a m).1) (G a m).2 hmA
    refine ⟨hmRest, ?_⟩
    intro hv
    rcases hRest hv with hinit | ⟨x, hx, hQx⟩
    · simp only [Bool.or_eq_true] at hinit
      rcases hinit with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ⟨a, List.mem_cons_self, hQA h2⟩
    · exact Or.inr ⟨x, List.mem_cons_of_mem a hx, hQx⟩

/-- If each check preserves `W` and returns `true` only for elements satisfying `P`, a right
    `&&`-fold of the checks preserves `W` and returns `true` only if `init = true` and every
    element satisfies `P`. -/
theorem foldrM_and_sound {α σ : Type _} (W : σ → Prop)
    (F : α → StateM σ Bool) (P : α → Prop) :
    ∀ (l : List α), (∀ x ∈ l, ∀ m, W m → W (F x m).2 ∧ ((F x m).1 = true → P x)) →
      ∀ (init : Bool) (m : σ), W m →
        W (List.foldrM (fun x acc => do let b ← F x; pure (b && acc)) init l m).2 ∧
        ((List.foldrM (fun x acc => do let b ← F x; pure (b && acc)) init l m).1 = true →
          init = true ∧ ∀ x ∈ l, P x) := by
  intro l
  induction l with
  | nil =>
    intro _ init m hm
    exact ⟨hm, fun hv => ⟨hv, nofun⟩⟩
  | cons a rest ih =>
    intro hF init m hm
    obtain ⟨hmRest, hRest⟩ :=
      ih (fun x hx => hF x (List.mem_cons_of_mem a hx)) init m hm
    obtain ⟨hmA, hPA⟩ :=
      hF a List.mem_cons_self
        (List.foldrM (fun x acc => do let b ← F x; pure (b && acc)) init rest m).2 hmRest
    rw [List.foldrM_cons]
    refine ⟨hmA, ?_⟩
    intro hv
    have hsplit :
        ((F a (List.foldrM (fun x acc => do let b ← F x; pure (b && acc)) init rest m).2).1 &&
          (List.foldrM (fun x acc => do let b ← F x; pure (b && acc)) init rest m).1) = true := hv
    simp only [Bool.and_eq_true] at hsplit
    obtain ⟨hinit, hall⟩ := hRest hsplit.2
    refine ⟨hinit, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact hPA hsplit.1
    · exact hall x hx'

/-- If each check preserves `W` and returns `true` only for elements satisfying `Q`, a left
    fold recording the key of the first failing element preserves `W` and returns `none` only
    if `acc = none` and every element satisfies `Q`. -/
theorem foldlM_option_sound {α β σ : Type _} (W : σ → Prop)
    (G : α → StateM σ Bool) (Q : α → Prop) (key : α → β) :
    ∀ (l : List α), (∀ x ∈ l, ∀ m, W m → W (G x m).2 ∧ ((G x m).1 = true → Q x)) →
      ∀ (acc : Option β) (m : σ), W m →
        W (List.foldlM (fun (x : Option β) (a : α) =>
          match x with
          | some s => pure (some s)
          | none => do let b ← G a; pure (if b then none else some (key a))) acc l m).2 ∧
        ((List.foldlM (fun (x : Option β) (a : α) =>
          match x with
          | some s => pure (some s)
          | none => do let b ← G a; pure (if b then none else some (key a))) acc l m).1 = none →
          acc = none ∧ ∀ a ∈ l, Q a) := by
  intro l
  induction l with
  | nil =>
    intro _ acc m hm
    exact ⟨hm, fun hv => ⟨hv, nofun⟩⟩
  | cons a rest ih =>
    intro hG acc m hm
    have hGrest : ∀ x ∈ rest, ∀ m, W m → W (G x m).2 ∧ ((G x m).1 = true → Q x) :=
      fun x hx => hG x (List.mem_cons_of_mem a hx)
    cases acc with
    | some s =>
      obtain ⟨hmRest, hRest⟩ := ih hGrest (some s) m hm
      refine ⟨hmRest, ?_⟩
      intro hv
      exact nomatch (hRest hv).1
    | none =>
      obtain ⟨hmA, hQA⟩ := hG a List.mem_cons_self m hm
      obtain ⟨hmRest, hRest⟩ :=
        ih hGrest (if (G a m).1 then none else some (key a)) (G a m).2 hmA
      refine ⟨hmRest, ?_⟩
      intro hv
      obtain ⟨hacc, hall⟩ := hRest hv
      have hb : (G a m).1 = true := by
        by_cases hcase : (G a m).1 = true
        · exact hcase
        · rw [ite_eq_right hcase] at hacc
          exact nomatch hacc
      refine ⟨rfl, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hQA hb
      · exact hall x hx'
