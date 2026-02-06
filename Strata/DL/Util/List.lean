/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! # List Utilities
-/

namespace List

theorem List.subset_append_cons_right {α : Type} [DecidableEq α] {a b c : List α} {x : α}
  (h : a ⊆ (b ++ c)) : a ⊆ b ++ (x :: c) := by
  simp_all [List.instHasSubset, List.Subset]
  intro e he
  have := @h e he
  cases this <;> simp_all
  done

/--
Remove duplicates in a list.
-/
def dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
    let as := as.dedup
    if a ∈ as then as else a :: as

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
  simp_all [List.instHasSubset, List.Subset]
  exact @length_dedup_append_all_in_right _ _ l₁ l₂ (by simp_all)

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
  simp_all [List.instHasSubset, List.Subset]

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
  simp_all [List.instHasSubset, List.Subset]

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

theorem mem_cons_dedup {α} [DecidableEq α]:
  ∀ (l : List α) a, a ∈ l → (a::l).dedup = l.dedup := by
  intro l
  induction l
  case nil => grind
  case cons hd tl tl_IH =>
    intro a H
    conv => lhs; unfold dedup
    have Hmem : a = hd ∨ a ∈ tl := by grind
    cases Hmem
    case inl Heq =>
      subst a
      grind [List.mem_of_dedup]
    case inr Htl =>
      grind [List.mem_of_dedup]

theorem notmem_cons_dedup {α} [DecidableEq α]:
  ∀ (l : List α) a, ¬ (a ∈ l) → (a::l).dedup = a :: (l.dedup) := by
  intro l
  induction l
  case nil => intros; solve | simp [dedup]
  case cons hd tl tl_IH =>
    intro a H
    conv => lhs; unfold dedup
    simp only []
    rw [List.mem_of_dedup] at H
    grind

theorem count_map {α} [DecidableEq α]:
  ∀ (l' l: List α) h,
    l.map (fun k => (k, count k (h::l'))) =
    map (fun ⟨k,v⟩ => (k, if k == h then v+1 else v))
      (l.map (fun k => (k, count k l'))) := by
  intro l'
  induction l'
  case nil => simp; grind
  case cons hd tl tl_IH =>
    intro l h
    rw[List.map_map]
    unfold Function.comp
    simp only []
    have IH := tl_IH l hd
    clear tl_IH
    have HH: ∀ k, count k (h::hd::tl) = count k (hd::tl) + (if k == h then 1 else 0) :=
      by grind
    congr
    ext k
    · rw [HH]
    · simp only []
      rw [HH]
      grind

theorem map_notmem_if {α β} [DecidableEq α]:
  ∀ (f g : α → β) (l : List α) h,
  ¬ (h ∈ l) →
    map (fun x => (x, if (x == h) = true then f x else g x)) l =
    map (fun x => (x, g x)) l := by
  intro f g l
  induction l
  case nil => grind
  case cons hd tl tl_IH =>
    intro h Hnotmem
    have Hh: ¬ (h = hd) ∧ ¬ (h ∈ tl) := by grind
    rcases Hh with ⟨Hleft, Hright⟩
    grind

theorem occurrences_cons {α} [DecidableEq α]:
  ∀ (l : List α) (h : α),
    (h::l).occurrences =
      (if h ∈ l then
        l.occurrences.map (fun ⟨k,v⟩ => if k == h then ⟨k,(v+1)⟩ else ⟨k,v⟩)
      else ((h,1)::l.occurrences)) := by
  intro l
  induction l
  case nil =>
    solve | simp[occurrences,dedup]
  case cons hd tl tl_IH =>
    have Hhd_in_tl: (hd ∈ tl) ∨ ¬ (hd ∈ tl) := by grind
    cases Hhd_in_tl
    case inl Hhd_in_tl =>
      have IH_hd := tl_IH hd
      clear tl_IH
      intro h
      have Hh_in_tl: (h ∈ tl) ∨ ¬ (h ∈ tl) := by grind
      cases Hh_in_tl
      case inl Hh_in_tl =>
        have H: h ∈ hd :: tl := by grind
        simp [H]
        simp [Hhd_in_tl] at IH_hd
        rw [IH_hd]
        unfold occurrences
        have Hdedup : (h :: hd :: tl).dedup = tl.dedup := by
          rw [mem_cons_dedup] <;> try assumption
          rw [mem_cons_dedup] <;> try assumption
        rw [Hdedup]
        rw [count_map]
        rw [count_map]
        repeat rw[List.map_map]
        unfold Function.comp
        simp only []
        congr
        ext k <;> grind
      case inr Hh_nin_tl =>
        have Hh_eq_hd : h = hd ∨ ¬ (h = hd) := by grind
        cases Hh_eq_hd
        case inl Hh_eq_hd =>
          subst h
          simp
          unfold occurrences
          have Hhdhd: (hd :: hd :: tl).dedup = (hd :: tl).dedup := by grind
          rw [Hhdhd]
          rw [count_map]
          grind
        case inr Hh_neq_hd =>
          have Hh_nin_hd_tl : ¬ (h ∈ hd :: tl) := by grind
          simp [Hh_nin_hd_tl]
          unfold occurrences
          conv => lhs; unfold dedup
          simp only []
          have Hh_nin_hd_tl : ¬ (h ∈ (hd :: tl).dedup) := by
            rw [← List.mem_of_dedup]
            grind
          simp only [Hh_nin_hd_tl, if_false]
          conv => lhs; unfold map
          conv => lhs; rhs; rw [count_map]
          rw [map_map]
          unfold Function.comp
          simp only []
          congr 1
          · rw [count_cons_self, count_cons_of_ne, count_eq_zero_of_not_mem]
            · assumption
            · grind
          · rw [map_notmem_if]
            grind
    case inr Hhd_nin_tl =>
      intro h
      have Hh_eq_hd : h = hd ∨ ¬ (h = hd) := by grind
      cases Hh_eq_hd
      case inl Heq =>
        subst h
        -- Split the 'hd ∈ hd :: tl' if condition
        split <;> try grind
        unfold occurrences
        have Htmp : (hd :: hd :: tl).dedup = (hd :: tl).dedup := by
          apply List.mem_cons_dedup; grind
        rw [Htmp]
        conv => lhs; rw [count_map]
        grind
      case inr Hne =>
        have Hcases: h ∈ tl ∨ ¬ (h ∈ tl) := by grind
        cases Hcases
        case inl Hh_in_tl =>
          have Htmp: h ∈ hd::tl := by grind
          simp only [Htmp, if_true]
          unfold occurrences
          have Htmp : (h :: hd :: tl).dedup = (hd :: tl).dedup := by
            rw [mem_cons_dedup]
            grind
          rw [Htmp]
          conv => lhs; rw [count_map]
          grind
        case inr Hh_nin_tl =>
          have Htmp : ¬ (h ∈ hd :: tl) := by grind
          simp only [Htmp, if_false]
          unfold occurrences
          rw [notmem_cons_dedup] <;> try assumption
          simp only [map]
          congr 1
          · rw [count_cons_self, count_cons_of_ne, count_eq_zero_of_not_mem]
            · assumption
            · grind
          · have Htmp: (∀ x (k:Bool) (a:Nat) b,
              x + (if k then a else b) = if k then (x + a) else (x + b)) := by grind
            conv =>
              -- This is bad; why should I do this to rewrite to the body of abs?
              lhs; lhs; ext x; rw [List.count_cons, Htmp]
            simp []
            intro a
            rw [← List.mem_of_dedup]
            grind

theorem occurrences_find {α} [DecidableEq α]:
  ∀ (l : List α) (x : α),
      x ∈ l → l.occurrences.find? (fun ⟨k,_⟩ => k == x) = .some (x, l.count x)
:= by
  intro l
  induction l
  case nil => grind
  case cons hd tl tl_IH =>
    intro x
    have Hx_is_hd : (x = hd) ∨ ¬ (x = hd) := by grind
    cases Hx_is_hd
    case inl Heq =>
      subst x
      intro _H
      rw [occurrences_cons]
      have Hhd_mem_tl : hd ∈ tl ∨ ¬ (hd ∈ tl) := by grind
      cases Hhd_mem_tl
      case inl Hmem =>
        have IH := tl_IH hd Hmem
        clear tl_IH
        simp only [Hmem, if_true]
        rw [List.find?_map]
        unfold Function.comp
        simp only []
        grind
      case inr Hnotmem =>
        simp only [Hnotmem, if_false]
        simp
        apply List.count_eq_zero_of_not_mem
        grind
    case inr Hneq =>
      intro Htmp
      have Hx_mem_tl: x ∈ tl := by grind
      have IH := tl_IH x Hx_mem_tl
      clear tl_IH
      rw [occurrences_cons]
      have Hhd_mem_tl: hd ∈ tl ∨ ¬ (hd ∈ tl) := by grind
      cases Hhd_mem_tl
      case inl Hhd_mem_tl =>
        simp only [Hhd_mem_tl, if_true]
        rw [List.find?_map]
        unfold Function.comp
        simp only []
        grind
      case inr Hhd_notmem_tl =>
        simp only [Hhd_notmem_tl, if_false]
        grind

end List
