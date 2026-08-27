/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.ListUtils
import all Strata.Util.ListUtils

/-!
# Properties of list utilities

Miscellaneous list lemmas: `Forall`/`Forall₂`, `Disjoint`, `Subset`,
`removeAll`/`replaceAll`, `dedup`, and `zip`/`map` results.

## Key theorems

* `List.Forall_mem_iff`, `List.Forall_append`, `List.Forall_flatMap`
* `List.Disjoint_app`, `List.Disjoint_Nodup_iff`
* `List.nodup_dedup`, `List.length_dedup_of_subset_le`
* `List.length_eq_of_nodup_of_mem_iff`, `List.inj_implies_nodup`, `List.sum_size_le`
-/

public section
open List

@[simp, grind =]
theorem List.Forall_nil {α} (p : α → Prop) : Forall p [] ↔ True := by
  simp [Forall]


@[simp, grind =]
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


/-- The empty list is disjoint from anything. -/
theorem List.Disjoint_nil_left (l : List α) : List.Disjoint [] l := by
  intro a ha _; simp at ha


/-- A singleton is disjoint from `l` iff its element is not in `l`. -/
theorem List.Disjoint_singleton_left {a : α} {l : List α} :
    List.Disjoint [a] l ↔ a ∉ l := by
  constructor
  · intro h hmem; exact h (by simp) hmem
  · intro h b hb hbl
    rw [List.mem_singleton] at hb; exact h (hb ▸ hbl)


/-- Disjointness on a `cons` splits into head-membership and tail-disjointness. -/
theorem List.Disjoint_cons_left {a : α} {l₁ l₂ : List α} :
    List.Disjoint (a :: l₁) l₂ ↔ a ∉ l₂ ∧ List.Disjoint l₁ l₂ := by
  constructor
  · intro h
    refine ⟨fun hmem => h (List.mem_cons_self ..) hmem, ?_⟩
    intro b hb hbl; exact h (List.mem_cons_of_mem _ hb) hbl
  · intro h b hb hbl
    rw [List.mem_cons] at hb
    cases hb with
    | inl he => exact h.1 (he ▸ hbl)
    | inr hm => exact h.2 hm hbl

end -- public section

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


/-- Decompose `List.mapM` on a cons list into head and tail results. -/
theorem List.mapM_cons_some {f : α → Option β} {a : α} {as : List α} {bs : List β}
    (h : (a :: as).mapM f = some bs) :
    ∃ b bs', f a = some b ∧ as.mapM f = some bs' ∧ bs = b :: bs' := by
  simp only [List.mapM_cons, bind, Option.bind] at h
  cases hfa : f a with
  | none => simp [hfa] at h
  | some b =>
    simp [hfa] at h
    cases hrest : as.mapM f with
    | none => simp [hrest] at h
    | some bs' =>
      simp [hrest] at h
      exact ⟨b, bs', rfl, rfl, h.symm⟩


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

/-! ### Nodup / membership length lemmas -/

/-- Two duplicate-free lists with the same membership have equal length. -/
public theorem List.length_eq_of_nodup_of_mem_iff [BEq κ] [LawfulBEq κ]
    {l₁ l₂ : List κ}
    (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) (hmem : ∀ a, a ∈ l₁ ↔ a ∈ l₂) :
    l₁.length = l₂.length := by
  have hperm : List.Perm l₁ l₂ := by
    rw [List.perm_iff_count]
    intro a
    rw [d₁.count, d₂.count]
    simp only [hmem a]
  exact hperm.length_eq

public theorem List.inj_implies_nodup {α} (l : List α)
  (p : ∀(i j : Nat) (p : i < l.length) (q : j < l.length), l[i] = l[j] → i = j)  :
     l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons h l ind =>
    rw [List.nodup_cons]
    constructor
    · intro hmem
      rw [List.mem_iff_getElem] at hmem
      obtain ⟨k, hk, hval⟩ := hmem
      have := p 0 (k + 1) (by simp) (by simp [hk]) (by simp [hval])
      omega
    · exact ind (fun i j hi hj heq => by
        have := p (i + 1) (j + 1) (by simp [hi]) (by simp[hj]) (by simpa using heq)
        omega)

/-- An element's measure is bounded by the sum of the mapped measures. -/
public theorem List.sum_size_le (f : α → Nat) {l : List α} {x : α} (x_in : x ∈ l) :
    f x ≤ List.sum (l.map f) := by
  induction l; simp_all; grind

public section
namespace List

/-- Monotonicity of list `⊆` under `++`. -/
theorem append_subset_append {α} {a a' b b' : List α}
    (ha : a ⊆ a') (hb : b ⊆ b') : a ++ b ⊆ a' ++ b' := by
  intro x hx
  rcases List.mem_append.mp hx with h | h
  · exact List.mem_append.mpr (Or.inl (ha h))
  · exact List.mem_append.mpr (Or.inr (hb h))


/-- Values in the `snd` projection of a `zip` are members of the second list. -/
theorem mem_map_snd_zip {α β} (l₁ : List α) (l₂ : List β) (v : β)
    (h : v ∈ (l₁.zip l₂).map Prod.snd) : v ∈ l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a l₁ ih =>
    cases l₂ with
    | nil => simp at h
    | cons b l₂ =>
      simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons_of_mem _ (ih l₂ h)


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


/-- If a list of pairs has unique keys (Nodup), then membership implies
the key can be looked up to find the corresponding value. -/
theorem lookup_of_mem_nodup
    {α β : Type} [BEq α] [LawfulBEq α] (l : List (α × β))
    (h_nodup : (l.map Prod.fst).Nodup)
    (k : α) (v : β)
    (h_mem : (k, v) ∈ l) :
    l.lookup k = some v := by
  induction l with
  | nil => cases h_mem
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    rw [List.mem_cons] at h_mem
    rcases h_mem with h_eq | h_tl
    · simp [List.lookup]; injection h_eq with h1 h2; subst h1; subst h2; simp
    · simp at h_nodup
      obtain ⟨h_not_in, h_nodup_tl⟩ := h_nodup
      have h_neq : ¬(k == k') = true := by
        intro h_eq
        rw [beq_iff_eq] at h_eq
        subst h_eq
        exact h_not_in v h_tl
      simp [List.lookup, h_neq]
      exact ih h_nodup_tl h_tl

end List

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


/-- If `find?` returns a pair from a zipped list, its second component belongs to the
    second input list. -/
theorem zip_find_mem_snd [BEq α] (l1 : List α) (l2 : List β)
    (x : α) (p : α × β)
    (h : (List.zip l1 l2).find? (fun p => p.1 == x) = some p) :
    p.2 ∈ l2 := by
  have h_mem := List.mem_of_find?_eq_some h
  exact (List.of_mem_zip h_mem).2


/-- `(a ++ b) ++ (c ++ d)` is a permutation of `(a ++ c) ++ (b ++ d)`. -/
theorem perm_append_swap_middle {α : Type _} (a b c d : List α) :
    List.Perm ((a ++ b) ++ (c ++ d)) ((a ++ c) ++ (b ++ d)) := by
  have h1 : List.Perm ((a ++ b) ++ (c ++ d)) (a ++ (b ++ (c ++ d))) := by
    simp [List.append_assoc]
  have h2 : List.Perm (a ++ (b ++ (c ++ d))) (a ++ (c ++ (b ++ d))) := by
    refine List.Perm.append_left a ?_
    have e1 : List.Perm (b ++ (c ++ d)) ((b ++ c) ++ d) := by simp [List.append_assoc]
    have e2 : List.Perm ((b ++ c) ++ d) ((c ++ b) ++ d) := List.Perm.append_right d List.perm_append_comm
    have e3 : List.Perm ((c ++ b) ++ d) (c ++ (b ++ d)) := by simp [List.append_assoc]
    exact (e1.trans e2).trans e3
  have h3 : List.Perm (a ++ (c ++ (b ++ d))) ((a ++ c) ++ (b ++ d)) := by simp [List.append_assoc]
  exact (h1.trans h2).trans h3

end
