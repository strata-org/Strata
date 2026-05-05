/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
/-! # List Utilities
-/

namespace List

/--
Remove duplicates in a list.
-/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
    let as := as.dedup
    if a ∈ as then as else a :: as

/--
Tail-recursive worker for `dedup`. Walks the input left-to-right,
skipping elements that still appear later, and collects kept elements
in reverse order.
-/
def dedupTR.go {α : Type} [DecidableEq α] :
    List α → List α → List α
  | [], acc => acc.reverse
  | a :: as, acc =>
    if a ∈ as then dedupTR.go as acc else dedupTR.go as (a :: acc)

/--
Tail-recursive implementation of `dedup`.
-/
def dedupTR {α : Type} [DecidableEq α] (l : List α) : List α :=
  dedupTR.go l []

/--
A deduplicated list satisfies `Nodup`.
-/
theorem nodup_dedup {α : Type} [DecidableEq α] (l : List α) :
  l.dedup.Nodup := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact ih
    · rename_i h; constructor
      · exact fun a' a_1 => Ne.symm (ne_of_mem_of_not_mem a_1 h)
      · exact ih

/--
The upper bound of the length of a deduplicated list is the length of the
original list.
-/
theorem length_dedup_le {α : Type} [DecidableEq α] (l : List α) :
  l.dedup.length ≤ l.length := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact Nat.le_succ_of_le ih
    · simp; exact ih

/--
The lower bound of the length of a deduplicated list with an element consed onto
it (i.e., `(a :: l)`) is the length of the deduplicated list `l`.
-/
theorem length_dedup_cons_le {α : Type} [DecidableEq α] (a : α) (l : List α) :
  l.dedup.length ≤ (a :: l).dedup.length := by
  induction l with
  | nil => simp [dedup]
  | cons a as ih =>
    simp [dedup]
    split
    · exact ih
    · rename_i a' h
      simp_all
      by_cases a' = a
      · simp_all
      · by_cases a' ∈ as.dedup <;> simp_all

theorem mem_dedup_of_mem {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l.dedup → a ∈ l := by
  induction l with
  | nil => simp [dedup]
  | cons b bs ih =>
    simp [dedup]
    split
    · intro h
      exact Or.symm (Or.intro_left (a = b) (ih h))
    · intro h
      cases h with
      | head => exact Or.symm (Or.inr rfl)
      | tail _ h' => exact Or.symm (Or.intro_left (a = b) (ih h'))

theorem mem_of_mem_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l → a ∈ l.dedup := by
  induction l with
  | nil => simp [dedup]
  | cons b bs ih =>
    simp [dedup]
    intro h; cases h
    · subst a
      by_cases b ∈ bs.dedup <;> simp_all
    · by_cases b ∈ bs.dedup <;> simp_all

/--
An element `a` is in a list `l` iff it is in the deduplicated version
of `l`.
-/
theorem mem_of_dedup {α : Type} [DecidableEq α]
  (l : List α) (a : α) : a ∈ l ↔ a ∈ l.dedup := by
  apply Iff.intro
  exact fun h => mem_of_mem_dedup l a h
  exact fun h => mem_dedup_of_mem l a h

theorem dedupTR.go_eq {α : Type} [DecidableEq α]
    (l acc : List α) :
    dedupTR.go l acc = acc.reverse ++ l.dedup := by
  induction l generalizing acc with
  | nil => simp [dedupTR.go, dedup]
  | cons a as ih =>
    simp only [dedupTR.go, dedup]
    by_cases h : a ∈ as
    · have h' : a ∈ as.dedup := mem_of_mem_dedup as a h
      simp [h, h', ih]
    · have h' : a ∉ as.dedup := by
        intro hc; exact h (mem_dedup_of_mem as a hc)
      simp [h, h', ih]

/--
`List.dedup` is equivalent to `dedupTR` at compile time.
-/
@[csimp] theorem dedup_eq_dedupTR : @List.dedup = @dedupTR := by
  funext α _ l
  simp [dedupTR, dedupTR.go_eq]

theorem length_dedup_cons_of_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) : (a :: l).dedup.length = l.dedup.length := by
  simp [dedup]
  have : a ∈ l.dedup := mem_of_mem_dedup l a h
  simp [this]

theorem length_dedup_cons_of_not_mem {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∉ l) : (a :: l).dedup.length = 1 + l.dedup.length := by
  induction l
  · simp_all [dedup]
  · rename_i head tail ih
    simp_all [dedup]
    obtain ⟨h1, h2⟩ := h
    split
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      omega
    · have := @mem_dedup_of_mem _ _ tail a
      simp_all
      omega

theorem mem_append_left_of_mem_dedup {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α)
  (h1 : ¬a ∈ l₂.dedup) (h2 : a ∈ (l₁ ++ l₂).dedup) :
  a ∈ l₁ := by
  have := @mem_dedup_of_mem _ _ (l₁ ++ l₂) a (by assumption)
  have := @mem_dedup_of_mem _ _ l₂ a
  simp_all; cases this
  · assumption
  · have := @mem_of_mem_dedup _ _ l₂ a (by assumption)
    contradiction

theorem mem_append_right_of_mem_dedup {α : Type} [DecidableEq α] (a : α) (l₁ l₂ : List α)
  (h1 : ¬a ∈ l₁.dedup) (h2 : a ∈ (l₁ ++ l₂).dedup) :
  a ∈ l₂ := by
  have := @mem_dedup_of_mem _ _ (l₁ ++ l₂) a (by assumption)
  have := @mem_dedup_of_mem _ _ l₁ a
  simp_all; cases this
  · have := @mem_of_mem_dedup _ _ l₁ a (by assumption)
    contradiction
  · assumption

theorem length_dedup_append_le_sum {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  (l₁ ++ l₂).dedup.length ≤ l₁.dedup.length + l₂.dedup.length := by
  induction l₁ generalizing l₂
  · simp_all
  · rename_i head tail ih
    simp [dedup]
    by_cases h1 : head ∈ tail.dedup
    · have : head ∈ (tail ++ l₂).dedup := by
        have := @mem_dedup_of_mem _ _ tail head h1
        have := @mem_of_mem_dedup _ _ (tail ++ l₂) head
        simp_all
      simp_all
    · simp_all
      by_cases h2 : head ∈ l₂.dedup
      · have : head ∈ (tail ++ l₂).dedup := by
          have := @mem_dedup_of_mem _ _ l₂ head  h2
          have := @mem_of_mem_dedup _ _ (tail ++ l₂) head
          simp_all
        simp_all
        have := ih l₂
        omega
      · have : head ∉ (tail ++ l₂).dedup := by
          have := @mem_dedup_of_mem _ _ (tail ++ l₂) head
          intro h
          simp_all
          have := @mem_of_mem_dedup _ _ tail head
          have := @mem_of_mem_dedup _ _ l₂ head
          simp_all
        simp_all
        have := ih l₂
        omega

theorem removeAll_of_cons {α : Type} [DecidableEq α] (x : α) (xs ys : List α)
  (h : x ∉ ys) :
  ((x :: xs).removeAll ys) = x :: (xs.removeAll ys) := by
  induction xs
  case nil => simp_all [removeAll]
  case cons a as ih =>
    simp_all [removeAll]

theorem length_dedup_of_removeAll {α : Type} [DecidableEq α] (a : α) (l : List α)
  (h : a ∈ l) :
  l.dedup.length = 1 + (l.removeAll [a]).dedup.length := by
  induction l
  case nil => simp_all
  case cons x xs ih =>
    simp [dedup]
    simp at h
    by_cases h : a = x
    case pos =>
      subst a
      split
      · rename_i h_x_xs
        have : x ∈ xs := by exact (mem_of_dedup xs x).mpr h_x_xs
        have ih' := ih this
        simp_all [removeAll]
      · simp [removeAll]
        have : x ∉ xs := by
          have := @mem_of_dedup _ _ xs x
          simp_all
        have : (filter (fun x_1 => !decide (x_1 = x)) xs) = xs := by
          simp_all
          intro a ha
          exact ne_of_mem_of_not_mem ha this
        rw [this]
        omega
    case neg =>
      rename_i h_a_x_xs
      simp_all
      split
      · rename_i hx
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_mem _ _ x (xs.removeAll [a])
        have : x ∈ xs.removeAll [a] := by
          simp [removeAll, h']
          exact (mem_of_dedup xs x).mpr hx
        simp_all
      · rename_i h_x_not_in_xs
        simp_all
        have := @removeAll_of_cons _ _ x xs [a]
        have h' : ¬x = a := by exact fun a_1 => h (id (Eq.symm a_1))
        simp [h'] at this
        rw [this]
        have := @length_dedup_cons_of_not_mem _ _ x (xs.removeAll [a])
        have : ¬ x ∈ xs.removeAll [a] := by
          simp [removeAll]
          have : x ∉ xs := by
            have := @mem_of_dedup _ _ xs x
            simp_all
          simp_all
        simp_all
        omega

theorem length_dedup_append_le_left {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  l₁.dedup.length ≤ (l₁ ++ l₂).dedup.length := by
  induction l₁ generalizing l₂
  case nil => simp [dedup]
  case cons a as ih =>
    simp [dedup]
    split
    · rename_i h
      have : a ∈ as := by exact (mem_of_dedup as a).mpr h
      have : a ∈ (as ++ l₂).dedup := by
        have : a ∈ as ++ l₂ := by simp_all
        exact (mem_of_dedup (as ++ l₂) a).mp this
      simp_all
    · by_cases ha : a ∈ (as ++ l₂).dedup
      case pos =>
        rename_i h_a_as
        simp_all
        have h_l2 : ∃ l, l = l₂.removeAll [a] := by simp_all
        obtain ⟨l, hl⟩ := h_l2
        simp_all
        have h_a_as_l2 : a ∈ as ++ l₂ := by exact (mem_of_dedup (as ++ l₂) a).mpr ha
        have h := @length_dedup_of_removeAll _ _ a (as ++ l₂) h_a_as_l2
        rw [h]
        have : ((as ++ l₂).removeAll [a]) = as ++ l := by
          simp [removeAll]
          have h_not_in_a_as : a ∉ as := by
            have := @mem_of_dedup _ _ as a
            simp_all
          have h_a_as : filter (fun x => !decide (x = a)) as = as := by
            simp_all
            intro a1 ha1
            exact ne_of_mem_of_not_mem ha1 h_not_in_a_as
          have h_a_l2 : filter (fun x => !decide (x = a)) l₂ = l := by
            rw [hl]
            simp [removeAll]
          simp_all
        rw [this]
        exact Nat.sub_le_iff_le_add'.mp (ih l)
      case neg =>
        simp_all

theorem length_dedup_append_all_in_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁.all (fun e => e ∈ l₂)) :
  (l₁ ++ l₂).dedup.length = l₂.dedup.length := by
  induction l₁
  · simp_all
  · rename_i head tail ih
    simp_all
    obtain ⟨h1, h2⟩ := h
    have h1' : head ∈ tail ++ l₂ := by simp_all
    simp [@length_dedup_cons_of_mem _ _ head (tail ++ l₂) h1']
    induction tail <;> try simp
    rename_i x xrest ih
    simp_all [dedup]
    have : x ∈ (xrest ++ l₂) := by simp_all
    have : x ∈ (xrest ++ l₂).dedup := by
      exact @mem_of_mem_dedup _ _ (xrest ++ l₂) x (by assumption)
    simp_all
    done

theorem length_dedup_append_subset_right {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) :
  (l₁ ++ l₂).dedup.length = l₂.dedup.length := by
  exact @length_dedup_append_all_in_right _ _ l₁ l₂ (by grind)

theorem length_dedup_append_all_in_left {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₂.all (fun e => e ∈ l₁)) :
  (l₁ ++ l₂).dedup.length = l₁.dedup.length := by
  induction l₂ generalizing l₁
  case nil => simp_all
  case cons x xs ih =>
    have h1 : (l₁ ++ x :: xs) = (l₁ ++ [x]) ++ xs := by exact append_cons l₁ x xs
    rw [h1]
    have ih' := ih (l₁ ++ [x])
    simp_all
    obtain ⟨hx, h_x_l1⟩ := h
    have h_1 := @length_dedup_of_removeAll _ _ x (l₁ ++ [x]) (by simp_all)
    have h_2 := @length_dedup_of_removeAll _ _ x (l₁) (by simp_all)
    have h_3 : ((l₁ ++ [x]).removeAll [x]) = l₁.removeAll [x] := by
      simp [removeAll]
    simp_all

theorem length_dedup_all_in_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁.all (fun e => e ∈ l₂))
  (h2 : l₂.all (fun e => e ∈ l₁)) :
  l₁.dedup.length = l₂.dedup.length := by
  have h_1 := @length_dedup_append_all_in_right _ _ l₁ l₂ h1
  have h_2 := @length_dedup_append_all_in_left _ _ l₁ l₂ h2
  simp_all

theorem length_dedup_subset_eq {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h1 : l₁ ⊆ l₂) (h2 : l₂ ⊆ l₁) :
  l₁.dedup.length = l₂.dedup.length := by
  have := @length_dedup_all_in_eq _ _ l₁ l₂
  grind

theorem length_dedup_append_le_right {α : Type} [DecidableEq α] (l₁ l₂ : List α) :
  l₂.dedup.length ≤ (l₁ ++ l₂).dedup.length := by
  have h_left := @length_dedup_append_le_left _ _ l₂ l₁
  have := @length_dedup_all_in_eq _ _ (l₁ ++ l₂) (l₂ ++ l₁)
  simp_all

theorem length_dedup_of_all_in_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁.all (fun e => e ∈ l₂)) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.dedup.length < l₂.dedup.length := by
  induction l₁ generalizing l₂ with
  | nil =>
    simp_all [dedup]
    have : a ∈ l₂.dedup := by
      have := @mem_of_dedup _ _ l₂ a
      simp_all
    exact length_pos_of_mem this
  | cons head tail ih =>
    simp at h1 ih
    simp [dedup]
    obtain ⟨h1_head_l2, h1⟩ := h1
    split
    · rename_i h_head_tail
      exact @ih l₂ h1 (by simp_all) h3
    · rename_i h_head_not_in_tail
      have h_head_tail := @length_dedup_cons_of_not_mem _ _ head tail
      by_cases h_head_in_tail : head ∈ tail
      case pos =>
        simp_all [@mem_of_dedup _ _ tail head]
      case neg =>
        have h_removeAll := @length_dedup_of_removeAll _ _ head l₂ h1_head_l2
        simp_all
        obtain ⟨h_a_head, h_a_tail⟩ := h2
        have h1' : ∀ (x : α), x ∈ tail → x ∈ l₂.removeAll [head] := by
          intro x hx
          have h_x_not_head : ¬ x = head := by exact ne_of_mem_of_not_mem hx h_head_in_tail
          have h_x_in_l2 := @h1 x hx
          simp_all [removeAll]
        have h_a_l2 : a ∈ l₂.removeAll [head] := by
          simp_all [removeAll]
        have ih' := @ih (l₂.removeAll [head]) h1' h_a_l2
        omega
  done

theorem length_dedup_of_subset_not_mem_lt {α : Type} [DecidableEq α] (l₁ l₂ : List α) (a : α)
  (h1 : l₁ ⊆ l₂) (h2 : a ∉ l₁) (h3 : a ∈ l₂) :
  l₁.dedup.length < l₂.dedup.length := by
  have := @length_dedup_of_all_in_not_mem_lt _ _ l₁ l₂ a
  grind

theorem length_dedup_of_subset_le {α : Type} [DecidableEq α] (l₁ l₂ : List α)
  (h : l₁ ⊆ l₂) : l₁.dedup.length ≤ l₂.dedup.length := by
  induction l₁ with
  | nil => simp_all [dedup]
  | cons head tail ih =>
    have h_tail_l2 : tail ⊆ l₂ := by simp_all
    have ih' := @ih h_tail_l2
    by_cases h_head : head ∈ tail
    case pos =>
      have := @length_dedup_cons_of_mem _ _ head tail h_head
      exact le_of_eq_of_le this (ih h_tail_l2)
    case neg =>
      simp_all
      have := @length_dedup_of_subset_not_mem_lt _ _ tail l₂ head h_tail_l2 h_head h
      have h_head_dedup : head ∉ tail.dedup := by
        have := @mem_of_dedup _ _ tail head
        simp_all
      simp_all [dedup]
      omega

theorem subset_nodup_length {α} {s1 s2: List α} (hn: s1.Nodup) (hsub: s1 ⊆ s2) : s1.length ≤ s2.length := by
  induction s1 generalizing s2 with
  | nil => simp
  | cons x t IH =>
    simp only[List.length]
    have xin: x ∈ s2 := by apply hsub; grind
    rw[List.mem_iff_append] at xin
    rcases xin with ⟨l1, ⟨l2, hs2⟩⟩; subst_vars
    have hsub1: t ⊆ (l1 ++ l2) := by grind
    grind


/-- Deduplicates l and counts the number of occurrences for each element. -/
def occurrences {α : Type} [DecidableEq α] (l : List α) : List (α × Nat) :=
  l.dedup.map (λ x => (x, l.count x))

theorem occurrences_len_eq_dedup {α} [DecidableEq α]:
  ∀ (l : List α), l.dedup.length = l.occurrences.length := by
  intros l
  unfold occurrences
  grind

theorem occurrences_find {α} [DecidableEq α] (l : List α) (x : α)
  (hx : x ∈ l)
  : l.occurrences.find? (fun ⟨k, _⟩ => k == x) = .some (x, l.count x) := by
  simp only [occurrences, find?_map, Option.map_eq_some_iff, Prod.mk.injEq]
  have : x ∈ l.dedup := by induction l <;> grind [dedup]
  generalize l.dedup = ld at *
  induction ld <;> simp [List.find?, Function.comp_apply] <;>
    (first | grind | split <;> grind)

/--
`foldlIdx f init l` folds `f` over `l` with an index.
-/
def foldlIdx (f : β → Nat → α → β) (init : β) (l : List α) : β :=
  ((List.range l.length).zip l).foldl (fun acc (i, a) => f acc i a) init

/-- If `P x → Q x` for all `x ∈ L`, then `(L.filter P).length ≤ (L.filter Q).length`. -/
theorem filter_length_le_of_imp {L : List α} {P Q : α → Bool}
    (h_imp : ∀ x ∈ L, P x = true → Q x = true) :
    (L.filter P).length ≤ (L.filter Q).length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    have ih' := ih (fun y hy => h_imp y (.tail x hy))
    simp only [List.filter]
    cases hPx : P x <;> cases hQx : Q x
    · exact ih'
    · simp; omega
    · have := h_imp x (.head xs) hPx; simp_all
    · simp; omega

/-- If `P x → Q x` for all `x ∈ L`, and there is a witness `a ∈ L` with `Q a` but `¬P a`,
    then `(L.filter P).length < (L.filter Q).length`. -/
theorem filter_length_lt_of_imp_witness {L : List α} {P Q : α → Bool}
    {a : α}
    (h_imp : ∀ x ∈ L, P x = true → Q x = true)
    (h_in : a ∈ L) (hQa : Q a = true) (hPa : ¬(P a = true)) :
    (L.filter P).length < (L.filter Q).length := by
  induction L with
  | nil => nomatch h_in
  | cons y ys ih =>
    have h_imp_ys : ∀ z ∈ ys, P z = true → Q z = true :=
      fun z hz => h_imp z (.tail y hz)
    simp only [List.filter]
    cases h_in with
    | head =>
      have hPa_false : P a = false := by
        cases h : P a
        · rfl
        · exact absurd h hPa
      simp only [hPa_false, hQa, List.length_cons]
      have := filter_length_le_of_imp h_imp_ys
      omega
    | tail _ h_in_ys =>
      cases hPy : P y <;> cases hQy : Q y
      · exact ih h_imp_ys h_in_ys
      · simp; have := ih h_imp_ys h_in_ys; omega
      · have := h_imp y (.head ys) hPy; simp_all
      · simp; have := ih h_imp_ys h_in_ys; omega

/-- If every element of `xs` is in `ys`, then `xs.removeAll ys = []`. -/
theorem removeAll_eq_nil_of_forall_mem [BEq α] [LawfulBEq α]
    {xs ys : List α} (h : ∀ x, x ∈ xs → x ∈ ys) :
    xs.removeAll ys = [] := by
  simp only [List.removeAll]
  rw [List.filter_eq_nil_iff]
  grind

theorem removeAll_not_mem [BEq α] [LawfulBEq α] {x : α} {xs : List α}
    (h : x ∉ xs) : xs.removeAll [x] = xs := by
  simp only [List.removeAll]
  rw [List.filter_eq_self]
  intro a ha
  simp only [List.elem_cons, List.elem_nil]
  split <;> simp_all

/-- `foldl` over a zipped subtype list equals `foldl` over the zipped projected list. -/
theorem foldl_subtype_zip_val
    {α β γ : Type _} (P : α → Prop)
    (f : γ → α → β → γ)
    (init : γ)
    (l₁ : List { x : α // P x }) (l₂ : List β) :
    List.foldl (fun acc (p : { x // P x } × β) => f acc p.1.val p.snd) init (l₁.zip l₂) =
    List.foldl (fun acc (p : α × β) => f acc p.1 p.2) init ((l₁.map Subtype.val).zip l₂) := by
  induction l₁ generalizing l₂ init with
  | nil => simp
  | cons a rest ih =>
    cases l₂ with
    | nil => simp
    | cons b rest₂ =>
      simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons]
      exact ih (f init a.val b) rest₂

/-- `foldl` over zipped lists is congruent when the function produces equal
results on corresponding elements. -/
theorem foldl_zip_congr
    {α β γ : Type _}
    (f : γ → α → β → γ)
    (l₁ l₁' : List α) (l₂ l₂' : List β)
    (h_len₁ : l₁.length = l₁'.length)
    (h_len₂ : l₂.length = l₂'.length)
    (h_f : ∀ (i : Nat) (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) (acc : γ),
        f acc (l₁[i]) (l₂[i]) = f acc (l₁'[i]'(h_len₁ ▸ hi₁)) (l₂'[i]'(h_len₂ ▸ hi₂)))
    (init : γ) :
    List.foldl (fun acc (p : α × β) => f acc p.1 p.2) init (l₁.zip l₂) =
    List.foldl (fun acc (p : α × β) => f acc p.1 p.2) init (l₁'.zip l₂') := by
  induction l₁ generalizing l₁' l₂ l₂' init with
  | nil =>
    have : l₁' = [] := by
      cases l₁' with
      | nil => rfl
      | cons _ _ => simp [List.length] at h_len₁
    subst this; simp
  | cons a₁ rest₁ ih_list =>
    cases l₁' with
    | nil => simp [List.length] at h_len₁
    | cons a₁' rest₁' =>
      cases l₂ with
      | nil =>
        cases l₂' with
        | nil => rfl
        | cons _ _ => simp [List.length] at h_len₂
      | cons a₂ rest₂ =>
        cases l₂' with
        | nil => simp [List.length] at h_len₂
        | cons a₂' rest₂' =>
          simp only [List.zip_cons_cons, List.foldl_cons, List.length_cons] at *
          have h_len₁_rest : rest₁.length = rest₁'.length := Nat.succ.inj h_len₁
          have h_len₂_rest : rest₂.length = rest₂'.length := Nat.succ.inj h_len₂
          have h_head : f init a₁ a₂ = f init a₁' a₂' := by
            have := h_f 0 (Nat.zero_lt_succ _) (Nat.zero_lt_succ _) init
            simp [List.getElem_cons_zero] at this
            exact this
          rw [h_head]
          refine ih_list rest₁' rest₂ rest₂' h_len₁_rest h_len₂_rest ?_ (f init a₁' a₂')
          intro i hi₁ hi₂ acc
          have := h_f (i + 1) (Nat.succ_lt_succ hi₁) (Nat.succ_lt_succ hi₂) acc
          simp [List.getElem_cons_succ] at this
          exact this

theorem nodup_map_injOn {α β : Type} [DecidableEq β] {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : f a = f b) : a = b := by
  induction l with
  | nil => exact nomatch ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    cases ha with
    | head => cases hb with
      | head => rfl
      | tail _ hb => exact absurd (hab ▸ List.mem_map.mpr ⟨_, hb, rfl⟩) hnd.1
    | tail _ ha => cases hb with
      | head => exact absurd (hab.symm ▸ List.mem_map.mpr ⟨_, ha, rfl⟩) hnd.1
      | tail _ hb => exact ih hnd.2 ha hb

/-- Filtering a list by `p` and its complement preserves total length. -/
theorem filter_compl_length (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (not ∘ p)).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih => simp [List.filter]; split <;> simp_all <;> omega

/-- `List.partition` preserves total length. -/
theorem partition_length (l : List α) (p : α → Bool) :
    (l.partition p).1.length + (l.partition p).2.length = l.length := by
  simp [partition_eq_filter_filter, filter_compl_length]

end List

/-! ### List.Forall₂ -/

/-- Pointwise relation between two lists. -/
inductive List.Forall₂ (R : α → β → Prop) : List α → List β → Prop where
  | nil : Forall₂ R [] []
  | cons : R a b → Forall₂ R as bs → Forall₂ R (a :: as) (b :: bs)

theorem List.Forall₂.head {R : α → β → Prop} (h : Forall₂ R (a :: as) (b :: bs)) : R a b := by
  cases h; assumption

theorem List.Forall₂.tail {R : α → β → Prop} (h : Forall₂ R (a :: as) (b :: bs)) : Forall₂ R as bs := by
  cases h; assumption

theorem List.Forall₂.length_eq {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Forall₂ R as bs) : as.length = bs.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem List.Forall₂.get? {R : α → β → Prop} {as : List α} {bs : List β}
    (h : Forall₂ R as bs) (i : Nat) (ha : as[i]? = some a) (hb : bs[i]? = some b)
    : R a b := by
  induction h generalizing i with
  | nil => simp at ha
  | cons h_head _ ih =>
    cases i with
    | zero => simp at ha hb; cases ha; cases hb; exact h_head
    | succ n => simp at ha hb; exact ih n ha hb

/-- If `Forall₂ R l1 l2` and `l1[i]? = some a`, then there exists `b` with
`l2[i]? = some b` and `R a b`. -/
theorem List.Forall₂.getElem?_some {R : α → β → Prop}
    {l1 : List α} {l2 : List β}
    (h : List.Forall₂ R l1 l2) {i : Nat} {a : α}
    (ha : l1[i]? = some a)
    : ∃ b, l2[i]? = some b ∧ R a b := by
  induction h generalizing i with
  | nil => simp at ha
  | cons hr _ ih =>
    cases i with
    | zero => simp at ha; subst ha; exact ⟨_, rfl, hr⟩
    | succ n => simp only [List.getElem?_cons_succ] at ha ⊢; exact ih ha

/-! ### Zip / map lemmas -/

theorem zip_map_fst_eq {α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.fst = l1 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all

theorem zip_map_snd_eq {α β: Type} (l1: List α) (l2: List β) :
  List.length l1 = List.length l2 →
  (l1.zip l2).map Prod.snd = l2 := by
  induction l1 generalizing l2 <;> cases l2 <;> simp_all

end
