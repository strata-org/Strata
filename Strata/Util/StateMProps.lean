/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init

/-! ## `StateM` equations and soundness of folding Boolean checks

Key theorems: `foldlM_and_sound`, `foldrM_and_sound`, `foldlM_or_sound` and `foldlM_option_sound`
(a fold of sound checks is sound), and the equations `stateM_get_apply` and `stateM_bind_apply`.
For loops whose steps yield and whose results do not depend on the state: `forIn_run_proj`,
`forIn_run_proj_of_eq`, `forIn_array_eq`, `forIn_list_eq`, `mapM_run_fst` and
`optionMapM_run_fst` (the result is a fold or a map); `forIn_state_inv`, `foldlM_state_inv`,
`forIn_state_inv_of_eq`, `foldlM_state_inv_of_eq`, `forIn_acc_inv` and `foldlM_acc_inv` (an
invariant of the state or the accumulator every step keeps holds at the end). -/

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

/-! ## Runs of `forIn`, `foldlM` and `mapM` in `StateM`

Equations for loops whose steps yield, and whose results do not depend on the state, and
invariants of the state or the accumulator that every step keeps. -/

section StateRuns

variable {σ α β γ : Type}

/-- A `forIn` over a list, every step of which yields and changes a projection `π` of the
    accumulator by `step`, changes it by folding `step`, whatever the state. -/
theorem forIn_run_proj (π : β → γ) (step : γ → α → γ) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, ∃ b' s', (f a b).run s = (ForInStep.yield b', s') ∧ π b' = step (π b) a) →
      ∀ b s, π ((forIn l b f).run s).1 = l.foldl step (π b)
  | [], _, _, b, s => rfl
  | a :: l, f, hf, b, s => by
    obtain ⟨b', s', hrun, hπ⟩ := hf a List.mem_cons_self b s
    have ih := forIn_run_proj π step l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s'
    simp only [StateT.run] at hrun
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind, hrun] at ih ⊢
    rw [List.foldl_cons, ← hπ]
    exact ih

/-- `mapM` with an action whose result does not depend on the state maps the results. -/
theorem mapM_run_fst (h : α → StateM σ β) (k : α → β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ s, ∃ s', (h a).run s = (k a, s')) →
      ∀ s, ∃ s', (l.mapM h).run s = (l.map k, s')
  | [], _, s => ⟨s, rfl⟩
  | a :: l, hk, s => by
    obtain ⟨s1, h1⟩ := hk a List.mem_cons_self s
    obtain ⟨s2, h2⟩ := mapM_run_fst h k l (fun a ha => hk a (List.mem_cons_of_mem _ ha)) s1
    refine ⟨s2, ?_⟩
    simp only [StateT.run] at h1 h2
    simp only [List.mapM_cons, StateT.run, bind, StateT.bind, h1, h2, pure, StateT.pure,
      List.map_cons]

/-- `Option.mapM` with an action whose result does not depend on the state maps the
    result. -/
theorem optionMapM_run_fst (h : α → StateM σ β) (k : α → β) (o : Option α)
    (hk : ∀ a ∈ o, ∀ s, ∃ s', (h a).run s = (k a, s')) (s : σ) :
    ∃ s', (o.mapM h).run s = (o.map k, s') := by
  cases o with
  | none => exact ⟨s, rfl⟩
  | some a =>
    obtain ⟨s', h'⟩ := hk a rfl s
    refine ⟨s', ?_⟩
    simp only [StateT.run] at h'
    simp only [Option.mapM, StateT.run, Functor.map, StateT.map, h', Option.map_some]
    rfl

/-- A `forIn` over a list that ends with accumulator `a`, every step of which yields and
    changes a projection `π` of the accumulator by `step`, ends with `π a` the fold of `step`
    over the list from `π b`. -/
theorem forIn_run_proj_of_eq (π : β → γ) (step : γ → α → γ) {l : List α}
    {f : α → β → StateM σ (ForInStep β)} {b a : β} {s s' : σ}
    (heq : (forIn l b f : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, ∃ b' s', (f a b).run s = (ForInStep.yield b', s') ∧
      π b' = step (π b) a) :
    π a = l.foldl step (π b) := by
  have h := forIn_run_proj π step l f hf b s
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

/-- An array `forIn` whose steps all yield pushes what the steps push. -/
private theorem forIn_array_run {σ α β : Type} (step : β → α → β) (xs : Array α)
    (f : α → β → StateM σ (ForInStep β))
    (hf : ∀ a ∈ xs.toList, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    (b : β) (s : σ) :
    ∃ s', (forIn xs b f).run s = (xs.toList.foldl step b, s') := by
  rw [← Array.forIn_toList]
  have h := forIn_run_proj id step xs.toList f
    (fun a ha b s => by obtain ⟨s', hs⟩ := hf a ha b s; exact ⟨_, s', hs, rfl⟩) b s
  exact ⟨_, Prod.ext h rfl⟩

/-- A list `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step`, whatever the state. -/
private theorem forIn_list_run {σ α β : Type} (step : β → α → β) (xs : List α)
    (f : α → β → StateM σ (ForInStep β))
    (hf : ∀ a ∈ xs, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    (b : β) (s : σ) :
    ∃ s', (forIn xs b f).run s = (xs.foldl step b, s') := by
  have h := forIn_run_proj id step xs f
    (fun a ha b s => by obtain ⟨s', hs⟩ := hf a ha b s; exact ⟨_, s', hs, rfl⟩) b s
  exact ⟨_, Prod.ext h rfl⟩

/-- An array `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step` over the array's elements, together with the state it ends in. -/
theorem forIn_array_eq {σ α β : Type} (step : β → α → β) {xs : Array α}
    {f : α → β → StateM σ (ForInStep β)}
    (hf : ∀ a ∈ xs.toList, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    {b : β} {s : σ} :
    (forIn xs b f : StateM σ β) s = (xs.toList.foldl step b, ((forIn xs b f : StateM σ β) s).2) :=
        by
  obtain ⟨s', h⟩ := forIn_array_run step xs f hf b s
  simp only [StateT.run] at h
  rw [h]

/-- A list `forIn` whose steps all yield the accumulator `step` gives returns the fold of
    `step`, together with the state it ends in. -/
theorem forIn_list_eq {σ α β : Type} (step : β → α → β) {xs : List α}
    {f : α → β → StateM σ (ForInStep β)}
    (hf : ∀ a ∈ xs, ∀ b s, ∃ s', (f a b).run s = (ForInStep.yield (step b a), s'))
    {b : β} {s : σ} :
    (forIn xs b f : StateM σ β) s = (xs.foldl step b, ((forIn xs b f : StateM σ β) s).2) := by
  obtain ⟨s', h⟩ := forIn_list_run step xs f hf b s
  simp only [StateT.run] at h
  rw [h]

/-- A list `forIn` whose steps keep an invariant of the state keeps it. -/
theorem forIn_state_inv (Inv : σ → Prop) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, Inv s → Inv ((f a b).run s).2) →
      ∀ b s, Inv s → Inv ((forIn l b f).run s).2
  | [], _, _, b, s, hs => hs
  | a :: l, f, hf, b, s, hs => by
    have h1 := hf a List.mem_cons_self b s hs
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f a b s = r at h1 ⊢
    obtain ⟨st, s'⟩ := r
    cases st with
    | done b' => exact h1
    | yield b' =>
      exact forIn_state_inv Inv l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

/-- A list `foldlM` whose steps keep an invariant of the state keeps it. -/
theorem foldlM_state_inv (Inv : σ → Prop) :
    ∀ (l : List α) (f : β → α → StateM σ β),
      (∀ a ∈ l, ∀ b s, Inv s → Inv ((f b a).run s).2) →
      ∀ b s, Inv s → Inv ((l.foldlM f b).run s).2
  | [], _, _, b, s, hs => hs
  | a :: l, f, hf, b, s, hs => by
    have h1 := hf a List.mem_cons_self b s hs
    simp only [List.foldlM_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f b a s = r at h1 ⊢
    obtain ⟨b', s'⟩ := r
    exact foldlM_state_inv Inv l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

/-- A `forIn` loop ends in a state satisfying `Inv` when it starts in one and every step
    keeps `Inv`. -/
theorem forIn_state_inv_of_eq (Inv : σ → Prop) {l : List α}
    {f : α → β → StateM σ (ForInStep β)} {b a : β} {s s' : σ}
    (heq : (forIn l b f : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, Inv s → Inv ((f a b).run s).2) (hs : Inv s) : Inv s' := by
  have h := forIn_state_inv Inv l f hf b s hs
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

/-- A monadic left fold ends in a state satisfying `Inv` when it starts in one and every
    step keeps `Inv`. -/
theorem foldlM_state_inv_of_eq (Inv : σ → Prop) {l : List α}
    {f : β → α → StateM σ β} {b a : β} {s s' : σ}
    (heq : (l.foldlM f b : StateM σ β) s = (a, s'))
    (hf : ∀ a ∈ l, ∀ b s, Inv s → Inv ((f b a).run s).2) (hs : Inv s) : Inv s' := by
  have h := foldlM_state_inv Inv l f hf b s hs
  simp only [StateT.run] at h
  rw [heq] at h
  exact h

/-- A list `forIn` whose steps all yield and keep a property of the accumulator keeps it. -/
theorem forIn_acc_inv (P : β → Prop) :
    ∀ (l : List α) (f : α → β → StateM σ (ForInStep β)),
      (∀ a ∈ l, ∀ b s, P b → ∃ b', ((f a b).run s).1 = ForInStep.yield b' ∧ P b') →
      ∀ b s, P b → P ((forIn l b f).run s).1
  | [], _, _, b, s, hb => hb
  | a :: l, f, hf, b, s, hb => by
    obtain ⟨b', hy, hb'⟩ := hf a List.mem_cons_self b s hb
    simp only [List.forIn_cons, StateT.run, bind, StateT.bind] at hy ⊢
    generalize f a b s = r at hy ⊢
    obtain ⟨st, s'⟩ := r
    simp only at hy
    subst hy
    exact forIn_acc_inv P l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' hb'

/-- A list `foldlM` whose steps keep a property of the accumulator keeps it. -/
theorem foldlM_acc_inv (P : β → Prop) :
    ∀ (l : List α) (f : β → α → StateM σ β),
      (∀ a ∈ l, ∀ b s, P b → P ((f b a).run s).1) →
      ∀ b s, P b → P ((l.foldlM f b).run s).1
  | [], _, _, b, s, hb => hb
  | a :: l, f, hf, b, s, hb => by
    have h1 := hf a List.mem_cons_self b s hb
    simp only [List.foldlM_cons, StateT.run, bind, StateT.bind] at h1 ⊢
    generalize f b a s = r at h1 ⊢
    obtain ⟨b', s'⟩ := r
    exact foldlM_acc_inv P l f (fun a ha => hf a (List.mem_cons_of_mem _ ha)) b' s' h1

end StateRuns
