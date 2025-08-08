/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-! ## No Duplication Properties
  This file contains theormes related to `List.Nodup` property. The main theorem
  is that the resulting list from `eraseDups` does not contain any duplicates
  (see `eraseDups_Nodup`). It also contains other theorems such as `Nodup` is
  preserved across filtering.

  These theorems are essential for the call elimination correctness proof.
  -/

section Nodup

theorem nodup_shrink : ∀ α {h : α} {l l' : List α} [BEq α],
  (l ++ h :: l').Nodup → (l ++ l').Nodup := by
  unfold List.Nodup
  intros α h l l' inst
  induction l
  case nil =>
    intros Hp
    simp [List.nil_append] at *
    exact Hp.2
  case cons head tail tail_ih =>
    intros Hp
    cases Hp with
    | cons H a =>
      specialize tail_ih a
      constructor
      . intros a' Ha'
        apply H
        cases (List.mem_append.mp Ha') with
        | inl hh => exact List.mem_append_left (h::l') hh
        | inr hh => apply List.mem_append_right; exact List.mem_cons_of_mem h hh
      . assumption

theorem nodup_insert : ∀ α {h : α} {l l' : List α} [BEq α],
  ¬h ∈ l → ¬h ∈ l' →
  (l ++ l').Nodup →
  (l ++ h :: l').Nodup := by
  intros α h l l' Hinst Hnotin1 Hnotin2 Hnodup
  induction l
  case nil => simp_all
  case cons h' t ih =>
    unfold List.Nodup at *
    simp at *
    apply And.intro
    intros a' Hcond
    cases Hcond with
    | inl Hcond => apply Hnodup.1; left; assumption
    | inr Hcond => cases Hcond with
      | inl Hcond => simp [Hcond]; exact fun a => Hnotin1.1 (Eq.symm a)
      | inr Hcond => apply Hnodup.1; right; assumption
    simp_all

theorem nodup_notin : (l ++ h :: l').Nodup → ¬h ∈ l ∧ ¬ h ∈ l' := by
  intros Hnodup
  simp [List.Nodup] at Hnodup
  induction l
  case nil =>
    simp_all
    cases Hnodup with
    | intro left right => exact fun a => left h a rfl
  case cons h' t ih =>
    simp_all
    cases Hnodup with
    | intro left right =>
    specialize left h'
    unfold Not; intros Heq; simp_all

theorem nodup_swap :
  List.Nodup (l ++ l') → List.Nodup (l' ++ l) := by
  intros Hnodup
  simp [List.Nodup] at *
  refine (List.pairwise_append_comm ?_).mp Hnodup
  exact fun {x y} a a_1 => a (Eq.symm a_1)

theorem nodup_swap' :
  List.Nodup (l ++ l') = List.Nodup (l' ++ l) := propext ⟨nodup_swap, nodup_swap⟩

theorem nodup_reverse :
  List.Nodup l → List.Nodup l.reverse := by
  intros Hnodup
  simp [List.Nodup] at *
  apply List.pairwise_reverse.mpr
  induction l <;> simp_all
  case cons h t _ =>
  intros a' Ha'
  cases Hnodup with
  | intro left _ => exact fun a => left a' Ha' (Eq.symm a)

theorem nodup_reverse' :
  List.Nodup l.reverse → List.Nodup l:= by
  intros Hnodup
  rw [← @List.reverse_reverse _ l]
  exact nodup_reverse Hnodup

theorem nodup_middle:
  List.Nodup (l ++ h :: l') → List.Nodup (h :: (l ++ l')) := by
  intros Hnodup
  simp only [List.Nodup] at *
  refine (List.pairwise_middle fun {x y} a => (Ne.symm a)).mp ?_
  simp_all

theorem nodup_middle':
  List.Nodup (h :: (l ++ l')) → List.Nodup (l ++ h :: l') := by
  intros Hnodup
  simp only [List.Nodup] at *
  refine (List.pairwise_middle fun {x y} a => (Ne.symm a)).mpr ?_
  simp_all

theorem loop_middle_nodup : ∀ α {h: α} {t l l' : List α} [BEq α] [LawfulBEq α],
(List.eraseDupsBy.loop (· == ·) t (l' ++ h :: l)).Nodup →
(List.eraseDupsBy.loop (· == ·) t (h :: (l' ++ l))).Nodup := by
    intros α h t l l' inst inst2 H
    induction t generalizing l l' h <;> simp [List.eraseDupsBy.loop] at *
    case nil =>
      -- rw [← List.append_assoc]; simp
      apply nodup_swap; simp
      apply nodup_middle'
      rw [← List.cons_append]
      apply nodup_swap
      assumption
    case cons h' t t_ih =>
      by_cases Heq : (h' == h)
      . rw [eq_of_beq Heq] at H ⊢
        simp at H
        by_cases (h ∈ l)
        case pos hh => simp; exact t_ih H
        case neg hh =>
          split
          . exact t_ih H
          . next x heq => simp_all
      . split
        . simp_all
          apply t_ih
          split at H <;> simp_all
          grind
        . next x heq =>
          simp_all
          have Heq1 : (h' :: h :: (l' ++ l)) = (h' :: [h] ++ (l' ++ l)) := by rfl
          rw [Heq1]
          apply t_ih; simp
          have Heq2 : (h :: h' :: (l' ++ l)) = (h :: (h' :: l') ++ l) := by simp
          rw [Heq2]
          apply t_ih; simp
          grind

theorem in_reverse : h ∈ l ↔ (h ∈ List.reverse l) := by simp_all
theorem not_in_reverse : ¬h ∈ l ↔ ¬h ∈ List.reverse l := by simp at *

theorem loop_shrink_nodup : ∀ α {h: α} {t l l' : List α} [BEq α] [LawfulBEq α],
  (List.eraseDupsBy.loop (· == ·) t (l' ++ h :: l)).Nodup →
  (List.eraseDupsBy.loop (· == ·) t (l' ++ l)).Nodup := by
    intros α h t l l' inst inst2 H
    induction t generalizing h l' l <;> simp [List.eraseDupsBy.loop] at *
    case nil => exact nodup_shrink α H
    case cons h' t t_ih =>
      split at H <;> simp_all
      . split <;> simp_all
        . apply t_ih <;> assumption
        . apply loop_middle_nodup
          grind
      . have Heq1 : (h' :: (l' ++ h :: l)) = ((h' :: l') ++ h :: l) := by rfl
        rw [Heq1] at H
        have Heq2 : (h' :: (l' ++ l)) = ((h' :: l') ++ l) := by rfl
        rw [Heq2]
        split <;> try simp_all
        . grind
        . apply t_ih <;> assumption

theorem loop_insert_nodup : ∀ α {h : α} {t l l': List α} [BEq α] [LawfulBEq α],
  ¬ h ∈ l → ¬ h ∈ l' →
  (List.eraseDupsBy.loop (· == ·) t (l ++ l')).Nodup →
  (List.eraseDupsBy.loop (· == ·) t (l ++ h :: l')).Nodup := by
  intros α h t l l' inst inst2 Hnotin1 Hnotin2 Hnodup
  induction t generalizing l l' h <;> simp [List.eraseDupsBy.loop] at *
  case nil =>
    apply nodup_insert
    . exact not_in_reverse.mp Hnotin2
    . exact not_in_reverse.mp Hnotin1
    . assumption
  case cons h' t ih =>
    split at Hnodup
    next x heq =>
      split <;> simp_all
      next x' heq' =>
      cases heq
      case inl Hin =>
        have contra := heq'.1 h' Hin
        simp_all
      case inr Hin =>
        have contra := heq'.2.2 h' Hin
        simp_all
    next x heq =>
    split
    . next x' heq' =>
      simp_all
      apply ih <;> try assumption
      have Heq : (l ++ l') = ([] ++ (l ++ l')) := by rfl
      rw [Heq]
      apply loop_shrink_nodup <;> assumption
    . next x' heq' =>
      simp_all
      have Heq : (h' :: (l ++ h :: l')) = ((h' :: l) ++ h :: l') := by rfl
      rw [Heq]
      apply ih <;> try assumption
      simp_all
      exact fun a => heq' (Eq.symm a)

theorem eraseDups_Nodup : ∀ α {l : List α} [BEq α] [LawfulBEq α], l.eraseDups.Nodup := by
  intros α l inst inst2
  simp [List.eraseDups]
  induction l
  case nil => simp_all
  case cons h t t_ih =>
    simp at *
    induction t
    case nil =>
      simp [List.eraseDupsBy, List.eraseDupsBy.loop] at *
    case cons h' t' t_ih' =>
      simp [List.eraseDupsBy, List.eraseDupsBy.loop] at *
      by_cases Heq : (h' == h)
      . simp [Heq]
        simp at *
        rw [←Heq]
        exact t_ih
      . simp [Heq]
        have Heq' : [h',h] = [] ++ h' :: [h] := by rfl
        rw [Heq']
        apply loop_insert_nodup <;> simp_all
        apply t_ih'
        have Heq' : [h'] = [] ++ h' :: [] := by rfl
        rw [Heq'] at t_ih
        have Heq'' : (([]: List α) = ([] ++ [])) := by rfl
        rw [Heq'']
        apply loop_shrink_nodup _ t_ih

end Nodup

theorem eraseDupsBy.loop_mem_bs {α : Type u} [BEq α] [LawfulBEq α] {h : α} {as bs : List α}:
  h ∈ bs → h ∈ List.eraseDupsBy.loop (· == ·) as bs := by
  intros Hin
  induction as generalizing bs <;> simp [List.eraseDupsBy.loop]
  case nil => assumption
  case cons h t ih => split <;> simp_all

theorem eraseDupsBy.loop_mem_as {α : Type u} [BEq α] [LawfulBEq α] {h : α} {as bs : List α}:
  ¬ h ∈ bs → h ∈ as → h ∈ List.eraseDupsBy.loop (· == ·) as bs := by
  intros Hnin Hin
  induction as generalizing bs <;> simp [List.eraseDupsBy.loop]
  case nil => cases Hin
  case cons h t ih =>
    split <;> simp_all
    . cases Hin <;> simp_all
    . cases Hin <;> simp_all
      . next b hnin heq =>
        exact loop_mem_bs List.mem_cons_self
      . next h' b hnin hin =>
        by_cases h = h'
        case pos heq =>
          simp_all
          exact loop_mem_bs List.mem_cons_self
        case neg hne =>
          apply ih
          exact List.not_mem_cons_of_ne_of_not_mem (fun a => hne (Eq.symm a)) Hnin

theorem eraseDupsBy.sound {α : Type u} [BEq α] [LawfulBEq α] {a : α} {as : List α}:
a ∈ as → a ∈ as.eraseDups := by
intros Hin
simp [List.eraseDups]
generalize Hbs : ([] : List α) = bs
induction as
case nil => cases Hin
case cons h t ih =>
  simp [List.eraseDupsBy] at *
  unfold List.eraseDupsBy.loop
  split <;> simp_all
  cases Hin
  case inl x eq =>
    simp [eq]
    exact loop_mem_bs (List.mem_singleton.mpr rfl)
  case inr x eq =>
    by_cases a = h
    case pos =>
      simp_all
      exact loop_mem_bs (List.mem_singleton.mpr rfl)
    case neg ne =>
      apply loop_mem_as ?_ eq
      simp_all

theorem filter_nodup : as.Nodup → (List.filter p as).Nodup := by
  intros H
  induction as <;> simp [List.filter]
  case cons h t ih =>
  split <;> simp_all
