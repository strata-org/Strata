/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
/-! ## List Properties Utilities
  This file contains miscellaneous utilities for manipulating lists and
  properties on lists.
-/

/-- Two predicates `P` and `Q` are disjoint, that is, they cannot both hold on a
    same instance of type `α` -/
def PredDisjoint (P Q : α → Prop) : Prop := ∀ a, P a → Q a → False

/-- Predicate `P` implies predicate `Q` -/
def PredImplies (P Q : α → Prop) : Prop := ∀ a, P a → Q a

/--
  A list with global properties (`π`) and element-wise properties (`πs`). The
  `split` method detaches the element-wise property of the first element from the
  global property.

  Usually, the global property makes use of the `Forall` predicate.
 -/
class ListP {α : Type} (π : α → Prop) (πs : List α → Prop) where
  split : ∀ {a : α} , πs (a :: as) → π a ×' πs as

/-- A `mapM` function that keeps track of the fact that the function is applied
to an argument that's an element of the original list. Useful for proving
termination. -/
def mapM₁ {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}
  (xs : List α) (f : {x : α // x ∈ xs} → m β) : m (List β) :=
  xs.attach.mapM f

/--
  Enable attaching the instance itself to properties about the instance.
  See `WFProcedure` and `WFProgram`.
-/
class Wrapper (α : Type) where
  self : α

open List

/-
Taken from mathlib4
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Defs.lean#L131-L137
https://github.com/leanprover-community/mathlib4/blob/d7a4adb961ed411dbec6ff6857cfc771859ec83f/Mathlib/Data/List/Basic.lean#L1203-L1206
-/
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

@[simp]
theorem List.Forall_cons (p : α → Prop) (x : α) : ∀ l : List α, Forall p (x :: l) ↔ p x ∧ Forall p l
  | [] => (and_iff_left_of_imp fun _ ↦ trivial).symm
  | _ :: _ => Iff.rfl

theorem List.Forall_mem_iff : ∀ {l : List α}, Forall p l ↔ ∀ x ∈ l, p x
  | [] => (iff_true_intro <| forall_mem_nil _).symm
  | x :: l => by rw [List.forall_mem_cons, List.Forall_cons, List.Forall_mem_iff]

theorem List.Forall_append : Forall P (a ++ b) ↔ Forall P a ∧ Forall P b := by
  apply Iff.intro
  . induction a <;> simp [Forall]
    case cons h t ih =>
    intros Hp Hfa
    specialize ih Hfa
    exact ⟨⟨Hp, ih.1⟩, ih.2⟩
  . induction a <;> simp [Forall]
    case cons h t ih =>
    intros Hp Hfa1 Hfa2
    specialize ih ⟨Hfa1, Hfa2⟩
    exact ⟨Hp, ih⟩

/--
`O(|l|)`. `replace l a b` replaces **all** element in the list equal to `a` with `b`.

* `replace [1, 4, 2, 3, 3, 7] 3 6 = [1, 4, 2, 6, 6, 7]`
* `replace [1, 4, 2, 3, 3, 7] 5 6 = [1, 4, 2, 3, 3, 7]`
Adapted from List.replace
-/
def List.replaceAll [BEq α] : List α → α → α → List α
  | [],    _, _ => []
  | a::as, b, c => match b == a with
    | true  => c :: replaceAll as b c
    | false => a :: replaceAll as b c


/-- `Disjoint l₁ l₂` means that `l₁` and `l₂` have no elements in common.
Taken from https://github.com/leanprover-community/batteries/blob/3613427d66262c4e25e19b40a6a49242e94ba072/Batteries/Data/List/Basic.lean#L512-L514
-/
def List.Disjoint (l₁ l₂ : List α) : Prop :=
  ∀ ⦃a⦄, a ∈ l₁ → a ∈ l₂ → False

theorem List.removeAll_Sublist [BEq α] {xs ys : List α}:
  (xs.removeAll ys).Sublist xs := by
  induction xs
  case nil => simp_all
  case cons h t ih => simp [List.removeAll]

theorem List.removeAll_Disjoint  [BEq α] [LawfulBEq α] {xs ys : List α}:
  (xs.removeAll ys).Disjoint ys := by
  induction xs <;> simp [removeAll, Disjoint] at *

theorem List.Disjoint.mono (h₁ : a.Sublist b) (h₂ : c.Sublist d) :
  Disjoint b d → Disjoint a c := λ Hdis _ Hin1 Hin2 ↦
  Hdis (Sublist.mem Hin1 h₁) (Sublist.mem Hin2 h₂)

theorem List.Disjoint.mono_left (h : a.Sublist b) :
  Disjoint b c → Disjoint a c := λ Hdis ↦ mono h (Sublist.refl c) Hdis

theorem List.Disjoint.mono_right (h : c.Sublist d) :
  Disjoint a d → Disjoint a c := λ Hdis ↦ mono (Sublist.refl a) h Hdis

theorem List.Disjoint.removeAll [BEq α] [LawfulBEq α ] {xs ys zs: List α} :
  Disjoint xs ys → Disjoint (zs ++ xs) (ys.removeAll zs) := by
  intros Hdisj a Hin1 Hin2
  simp_all only [mem_append]
  apply @Hdisj a
  . cases Hin1 with
    | inl Hin =>
      simp [List.removeAll] at Hin2
      have HH := List.elem_eq_true_of_mem Hin
      simp_all
    | inr Hin => assumption
  . have Hsub := List.removeAll_Sublist (xs:=ys) (ys:=zs)
    exact Sublist.mem Hin2 Hsub

theorem List.Disjoint_cons_head : (h :: t).Disjoint l → ¬h ∈ l := by
  intros Hdis Hin
  simp [Disjoint] at Hdis
  exact Hdis.1 Hin

theorem List.Disjoint_cons_tail : (h :: t).Disjoint l → t.Disjoint l := by
  intros Hdis Hin
  simp [Disjoint] at Hdis
  exact Hdis.2 Hin

theorem List.Disjoint_app :
  List.Disjoint l1 l ∧ l2.Disjoint l ↔ (l1 ++ l2).Disjoint l := by
  apply Iff.intro
  . induction l1
    case nil => simp [Disjoint]
    case cons h t ih =>
    intros Hnin x Hin1 Hin2
    specialize ih ⟨List.Disjoint_cons_tail Hnin.1, Hnin.2⟩
    simp at Hin1
    cases Hin1 with
    | inl Hin =>
      simp_all
      exact Disjoint_cons_head Hnin.1 Hin2
    | inr Hin =>
      cases Hin with
    | inl Hin =>
      apply ih ?_ Hin2
      exact mem_append_left l2 Hin
    | inr Hin =>
      exact Hnin.2 Hin Hin2
  . induction l1
    case nil => simp [Disjoint]
    case cons h t ih =>
    intros Hnin
    refine ⟨?_, ?_⟩
    . intros x Hin1 Hin2
      apply Hnin _ Hin2
      exact mem_append_left l2 Hin1
    . specialize ih (Disjoint_cons_tail Hnin)
      exact ih.2

theorem List.Disjoint_Nodup_iff :
List.Nodup a ∧ b.Nodup ∧ a.Disjoint b ↔ (a ++ b).Nodup := by
apply Iff.intro
. intros H
  refine nodup_append.mpr ?_
  refine ⟨H.1, H.2.1, ?_⟩
  intros a Ha b Hb Heq
  simp_all
  exact H.2.2 Ha Hb
. intros Hnd
  have H := nodup_append.mp Hnd
  refine ⟨H.1, H.2.1, ?_⟩
  intros a Ha Hb
  exact H.2.2 _ Ha _ Hb rfl

@[simp]
theorem List.Subset.empty : [].Subset s := by
  intros a Hin
  cases Hin

/-- From Mathlib4
    https://github.com/leanprover-community/mathlib4/blob/ccca47289b3f94a9572a38975e0876c139690a21/Mathlib/Data/List/Lattice.lean#L39-L40
    -/
theorem List.Disjoint.symm : Disjoint a b → Disjoint b a := fun H _ Hin1 Hin2 => H Hin2 Hin1

theorem List.Disjoint.symm_app (d : Disjoint l (l₁ ++ l₂))
  : Disjoint l (l₂ ++ l₁) := fun _ Hin1 Hin2 => d Hin1
        (mem_append.mpr $ Or.symm (mem_append.mp Hin2))

theorem List.Disjoint_Subset_right : Disjoint vs ks → ks'.Subset ks → vs.Disjoint ks' := by
  intros Hdis Hsub
  simp [Disjoint, List.Subset] at *
  intros a Hin1 Hin2
  specialize Hdis Hin1
  simp_all

theorem List.Disjoint_Subset_left : Disjoint vs ks → List.Subset vs' vs → vs'.Disjoint ks := by
  intros Hdis Hsub
  apply List.Disjoint.symm
  apply Disjoint_Subset_right (Disjoint.symm Hdis) Hsub

theorem List.Disjoint_Subsets : Disjoint vs ks → List.Subset vs' vs → List.Subset ks' ks → vs'.Disjoint ks' := by
  intros Hdis Hsub1 Hsub2
  exact List.Disjoint_Subset_left (Disjoint_Subset_right Hdis Hsub2) Hsub1

theorem List.DisjointAppLeft' :
  Disjoint vs (ks ++ ks') → Disjoint vs ks' := by
  intros Hdist h
  simp [Disjoint] at *
  intros Hin1 Hin2
  specialize Hdist Hin1
  simp_all

theorem List.DisjointAppRight' :
  List.Disjoint vs (ks ++ ks') → List.Disjoint vs ks := by
  intros Hdist
  have Hdist' := List.Disjoint.symm_app Hdist
  exact List.DisjointAppLeft' Hdist'

theorem List.Subset.subset_app_of_or_2 {l: List α}: l ⊆ l1 ∨ l ⊆ l2 → l ⊆ l1 ++ l2  := by
  simp [Subset, List.Subset]
  intro H a Ha
  cases H <;> simp_all

theorem List.Subset.subset_app_of_or_3 {l: List α}: l ⊆ l1 ∨ l ⊆ l2 ∨ l ⊆ l3 → l ⊆ l1 ++ l2 ++ l3  := by
  simp [Subset, List.Subset]
  intro H a Ha
  cases H <;> try (rename_i H; cases H)
  any_goals simp_all

theorem List.Subset.subset_app_of_or_4 {l: List α}: l ⊆ l1 ∨ l ⊆ l2 ∨ l ⊆ l3 ∨ l ⊆ l4 → l ⊆ l1 ++ l2 ++ l3 ++ l4 := by
  simp [Subset, List.Subset]
  intro H a Ha
  cases H <;> try (rename_i H; cases H <;> try (rename_i H; cases H))
  any_goals simp_all

theorem List.Subset.assoc {l: List α}: l ⊆ l1 ++ l2 ++ l3 ↔ l ⊆ l1 ++ (l2 ++ l3) := by
  simp [Subset, List.Subset]

theorem List.replaceAll_app {α : Type} [DecidableEq α] {h h' : α} {as bs : List α}:
  List.replaceAll as h h' ++ List.replaceAll bs h h' = List.replaceAll (as ++ bs) h h' := by
  induction as generalizing bs
  case nil => simp [List.replaceAll]
  case cons hh t ih =>
    simp [List.replaceAll]
    rw [← ih]
    split <;> simp_all

/-- Taken from https://github.com/leanprover/lean4/blob/master/src/Init/Data/List/Lemmas.lean -/
theorem cons_removeAll [BEq α] {x : α} {xs ys : List α} :
    (x :: xs).removeAll ys =
      if ys.contains x = false then
        x :: xs.removeAll ys
      else
        xs.removeAll ys := by
  simp [List.removeAll, List.filter_cons]

theorem List.app_removeAll {α : Type} [BEq α] {xs₁ xs₂ ys : List α}:
  (xs₁ ++ xs₂).removeAll ys =
  (xs₁.removeAll ys) ++ (xs₂.removeAll ys) := by
  induction xs₁ <;> simp_all
  . simp [cons_removeAll]
    split <;> simp_all

theorem removeAll_nil [BEq α] {xs : List α} : xs.removeAll [] = xs := by
  simp [List.removeAll]

theorem List.removeAll_app {α : Type} [BEq α] {xs₁ xs₂ ys : List α}:
  ys.removeAll (xs₁ ++ xs₂) =
  (ys.removeAll xs₁).removeAll xs₂ := by
  induction ys
  case nil => simp [removeAll]
  case cons h t ih =>
    simp [cons_removeAll]
    split <;> simp_all
    . next HH =>
      simp [cons_removeAll]
      exact HH.2
    . next HH =>
      split <;> simp_all
      simp [cons_removeAll]
      exact HH

theorem List.removeAll_comm {α : Type} [BEq α] {xs₁ xs₂ ys : List α}:
  (ys.removeAll xs₂).removeAll xs₁ =
  (ys.removeAll xs₁).removeAll xs₂
  := by
  induction ys
  case nil => simp [removeAll]
  case cons h t ih =>
    simp [cons_removeAll]
    split
    . next HH =>
      simp [cons_removeAll]
      split <;> simp_all
      simp [cons_removeAll]
      exact HH
    . next HH =>
      split <;> simp_all
      simp [cons_removeAll]
      exact HH

/-- From Mathlib4 https://github.com/leanprover-community/mathlib4/blob/e70dc4ede17dd5fcda9926c84268e0f270147cba/Mathlib/Data/List/Zip.lean#L32-L37 -/
@[simp]
theorem zip_swap : ∀ (l₁ : List α) (l₂ : List β), (List.zip l₁ l₂).map Prod.swap = List.zip l₂ l₁
  | [], _ => List.zip_nil_right.symm
  | l₁, [] => by rw [List.zip_nil_right]; rfl
  | a :: l₁, b :: l₂ => by
    simp only [List.zip_cons_cons, List.map_cons, zip_swap l₁ l₂, Prod.swap_prod_mk]

theorem replaceAll_mem {α : Type u} [BEq α] [LawfulBEq α] {h h' k : α} {t: List α}:
  k ∈ (t.replaceAll h h') → k ∈ t ∨ k = h' := by
  intros Hr
  induction t generalizing k h h' <;> simp [List.replaceAll] at *
  case cons h t ih =>
    split at Hr <;> simp_all
    . cases Hr with
    | inl heq => simp_all
    | inr hin =>
      specialize ih hin
      cases ih <;> simp_all
    . cases Hr with
    | inl heq => simp_all
    | inr hin =>
      specialize ih hin
      cases ih <;> simp_all

theorem zip_self_eq :
(k1, k2) ∈ List.zip ks ks → k1 = k2 := by
  intros Hin
  induction ks <;> simp_all
  case cons h t ih =>
  cases Hin <;> simp_all

theorem zip_self_eq' :
k ∈ ks → (k, k) ∈ List.zip ks ks := by
  intros Hin
  induction ks <;> simp_all
  case cons h t ih =>
  cases Hin <;> simp_all

theorem in_replaceAll_removeAll {α : Type u} [BEq α] [LawfulBEq α] {h h' k2 : α} {vs t: List α}:
  k2 ∈ (vs.replaceAll h h').removeAll t → k2 = h' ∨ k2 ∈ vs.removeAll t := by
  intros H
  induction vs generalizing k2 <;> simp [List.removeAll, List.replaceAll] at *
  case cons h t ih =>
    split at H
    . next x heq =>
      have H := H.1
      cases H <;> simp_all
      case tail Hmem =>
        have Hor := replaceAll_mem Hmem
        cases Hor <;> simp_all
    . have H := H.1
      cases H <;> simp_all
      next Hin =>
      have Hor := replaceAll_mem Hin
      cases Hor <;> simp_all

theorem removeAll_cons {α : Type u} [BEq α] [LawfulBEq α] {k h : α} {vs t : List α} :
  k ≠ h →
  k ∈ List.removeAll vs t →
  k ∈ List.removeAll vs (h :: t) := by
  intros Hne Hin
  induction vs <;> simp [List.removeAll] at *
  case cons h' t' ih =>
    simp_all

theorem removeAll_sublist {α : Type u} [BEq α] [LawfulBEq α] (as bs : List α):
  (List.removeAll as bs).Sublist as := by
  induction as <;> simp [List.removeAll]

theorem replaceAll_not_mem {α : Type u} [BEq α] [LawfulBEq α] {h h' : α} {vs : List α}:
  h ≠ h' →
  ¬ h ∈ (vs.replaceAll h h') := by
  intros Hne Hin
  induction vs
  case nil => simp [List.replaceAll] at *
  case cons h t ih =>
    simp [List.replaceAll] at Hin
    split at Hin
    next heq =>
      have heq := beq_iff_eq.1 heq
      simp [heq] at *
      cases Hin <;> simp_all
    next hne =>
      have hne := ne_of_beq_false hne
      simp_all

theorem List.mem_zip_1 {l₁ : List α} {l₂ : List β}  :
l₁.length = l₂.length →
a ∈ l₁ → ∃ b, (a, b) ∈ l₁.zip l₂ := by
intros Hlen Hin
induction l₁ generalizing l₂ <;> simp_all
case cons h t ih =>
  cases l₂ <;> simp_all
  case cons h' t' =>
  cases Hin with
  | inl Hin => simp_all
  | inr Hin =>
  specialize @ih t' rfl Hin
  cases ih with
  | intro b Hin =>
  refine ⟨b, Or.inr Hin⟩

theorem List.mem_zip_2 {l₁ : List α} {l₂ : List β}  :
l₁.length = l₂.length →
b ∈ l₂ → ∃ a, (a, b) ∈ l₁.zip l₂ := by
intros Hlen Hin
induction l₂ generalizing l₁ <;> simp_all
case cons h t ih =>
  cases l₁ <;> simp_all
  case cons h' t' =>
  cases Hin with
  | inl Hin => simp_all
  | inr Hin =>
  specialize @ih t' Hlen Hin
  cases ih with
  | intro b Hin =>
  refine ⟨b, Or.inr Hin⟩

theorem List.PredDisjoint_comm :
  PredDisjoint P Q → PredDisjoint Q P := fun H x Hq Hp => H x Hp Hq

theorem List.PredDisjoint_Disjoint :
  Forall P as →
  Forall Q bs →
  PredDisjoint P Q →
  Disjoint as bs := by
intros H1 H2 Hdis x Hin1 Hin2
apply Hdis x
. exact (List.Forall_mem_iff.mp H1) x Hin1
. exact (List.Forall_mem_iff.mp H2) x Hin2

theorem List.Forall_PredImplies :
  Forall P as → PredImplies P Q → Forall Q as := by
  intros Hp Hpq
  apply List.Forall_mem_iff.mpr
  intros x Hin
  exact Hpq _ (List.Forall_mem_iff.mp Hp x Hin)

theorem List.PredDisjoint_PredImplies_left :
  PredDisjoint R Q → PredImplies P R → PredDisjoint P Q := by
  intros Hdis Himp a Hp Hq
  exact Hdis a (Himp a Hp) Hq

theorem List.PredDisjoint_PredImplies_right :
  PredDisjoint P R → PredImplies Q R → PredDisjoint P Q := by
  intros Hdis Himp a Hp Hq
  exact Hdis a Hp (Himp a Hq)

theorem List.Forall_filter :
  Forall (P ·) (List.filter P l) := by
  apply Forall_mem_iff.mpr
  intros x Hin
  simp at Hin
  exact Hin.2

theorem List.Forall_flatMap :
  Forall (fun x => Forall P (f x)) ls ↔ Forall P (List.flatMap f ls) := by
  apply Iff.intro
  . induction ls <;> simp [Forall]
    case cons h t ih =>
    intros Hfa1 Hfa2
    apply List.Forall_append.mpr
    exact ⟨Hfa1, ih Hfa2⟩
  . induction ls <;> simp [Forall]
    case cons h t ih =>
    intros Hfa
    have Hfa := List.Forall_append.mp Hfa
    exact ⟨Hfa.1, ih Hfa.2⟩
end
