/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LSort
import all Strata.DL.Lambda.LSort
import all Strata.DL.Lambda.LTy

/-! ## Properties of sorts

Induction on sorts (`LSort.ind`); `LSort_eqb` decides equality (`LSort_eqb_eq`,
`LSort_eqb_refl`), which gives the `DecidableEq LSort` instance; the type naming a sort has no
free type variables (`LSort.toMonoTy_freeVars`); and `LMonoTy.toSort?` inverts
`LSort.toMonoTy` (`LMonoTy.toSort?_toMonoTy`, with `LMonoTy.toSortList?_toMonoTy` on lists).
-/

namespace Lambda

/-- Induction on sorts with the hypothesis on the arguments of a constructor stated by list
    membership. -/
public theorem LSort.ind (P : LSort → Prop)
    (htcons : ∀ name args, (∀ x, x ∈ args → P x) → P (.tcons name args))
    (hbitvec : ∀ n, P (.bitvec n)) : ∀ s, P s
  | .tcons name args => htcons name args (fun x _ => ind P htcons hbitvec x)
  | .bitvec n => hbitvec n

/-- Lists of sorts that `LSort_eqb` relates elementwise, when it decides equality of each
    element of the first list, are equal. -/
private theorem LSort_eqb_list_eq
    (ih : ∀ x ∈ a1, ∀ s2, LSort_eqb x s2 = true → x = s2)
    (heq : LSort_eqb.LSort_eqb_list a1 a2 = true) : a1 = a2 := by
  induction a1 generalizing a2 with
  | nil => cases a2 <;> simp_all [LSort_eqb.LSort_eqb_list]
  | cons h t iht =>
    cases a2 with
    | nil => simp [LSort_eqb.LSort_eqb_list] at heq
    | cons h2 t2 =>
      simp only [LSort_eqb.LSort_eqb_list, Bool.and_eq_true] at heq
      obtain ⟨hh, ht⟩ := heq
      congr 1
      · exact ih h (List.mem_cons_self ..) h2 hh
      · exact iht (fun x hx => ih x (List.mem_cons_of_mem _ hx)) ht

/-- `LSort_eqb` holds only of equal sorts. -/
public theorem LSort_eqb_eq {s1 s2} (heq: LSort_eqb s1 s2 = true) :
  s1 = s2 := by
  induction s1 using LSort.ind generalizing s2 with
  | htcons n1 a1 ih =>
    cases s2 with
    | bitvec => simp [LSort_eqb] at heq
    | tcons n2 a2 =>
      simp only [LSort_eqb, Bool.and_eq_true, beq_iff_eq] at heq
      obtain ⟨hn, ha⟩ := heq
      subst_vars; congr 1
      exact LSort_eqb_list_eq ih ha
  | hbitvec n1 =>
    cases s2 with
    | tcons => simp [LSort_eqb] at heq
    | bitvec => simp only [LSort_eqb, beq_iff_eq] at heq; exact congrArg _ heq

/-- `LSort_eqb` holds of every sort and itself. -/
public theorem LSort_eqb_refl : ∀ a : LSort, LSort_eqb a a = true := by
  intro a; induction a using LSort.ind with
  | htcons n args ih =>
    simp only [LSort_eqb, BEq.rfl, Bool.true_and]
    induction args with
    | nil => simp [LSort_eqb.LSort_eqb_list]
    | cons x xs ihxs =>
      simp only [LSort_eqb.LSort_eqb_list, Bool.and_eq_true]
      exact ⟨ih x (List.mem_cons_self ..), ihxs (fun z hz => ih z (List.mem_cons_of_mem _ hz))⟩
  | hbitvec => simp [LSort_eqb]

/-- Decidable equality of sorts, by `LSort_eqb`. Equality tests on sorts (`==`) use it, through
    `instBEqOfDecidableEq`. -/
public instance : DecidableEq LSort := fun a b =>
  if h : LSort_eqb a b then isTrue (LSort_eqb_eq h)
  else isFalse (fun heq => h (heq ▸ LSort_eqb_refl a))

/-- The monomorphic type naming a sort has no free type variables. -/
public theorem LSort.toMonoTy_freeVars (s : LSort) : s.toMonoTy.freeVars = [] := by
  induction s using LSort.ind with
  | htcons name args ih =>
    simp only [LSort.toMonoTy, LMonoTy.freeVars]
    induction args with
    | nil => rfl
    | cons a as iha =>
      simp only [LSort.toMonoTy.map, LMonoTys.freeVars_of_cons, List.append_eq_nil_iff]
      exact ⟨ih a List.mem_cons_self, iha fun x hx => ih x (List.mem_cons_of_mem _ hx)⟩
  | hbitvec n => rfl

mutual
/-- `toSort?` inverts `LSort.toMonoTy`. -/
public theorem LMonoTy.toSort?_toMonoTy : ∀ {t : LMonoTy} {s : LSort},
    t.toSort? = some s → s.toMonoTy = t
  | .ftvar _, _, h => by simp [LMonoTy.toSort?] at h
  | .bitvec n, s, h => by
    simp only [LMonoTy.toSort?, Option.some.injEq] at h; subst h; rfl
  | .tcons name args, s, h => by
    simp only [LMonoTy.toSort?] at h
    obtain ⟨ss, hss, rfl⟩ := Option.map_eq_some_iff.mp h
    simp only [LSort.toMonoTy, LMonoTy.tcons.injEq, true_and]
    exact LMonoTy.toSortList?_toMonoTy hss
/-- `toSort?.toSortList?` inverts `LSort.toMonoTy.map`. -/
public theorem LMonoTy.toSortList?_toMonoTy : ∀ {ts : List LMonoTy} {ss : List LSort},
    LMonoTy.toSort?.toSortList? ts = some ss → LSort.toMonoTy.map ss = ts
  | [], ss, h => by
    simp only [LMonoTy.toSort?.toSortList?, Option.some.injEq] at h; subst h; rfl
  | t :: ts, ss, h => by
    simp only [LMonoTy.toSort?.toSortList?] at h
    split at h
    · rename_i s ss' hs hss
      simp only [Option.some.injEq] at h; subst h
      simp only [LSort.toMonoTy.map, List.cons.injEq]
      exact ⟨LMonoTy.toSort?_toMonoTy hs, LMonoTy.toSortList?_toMonoTy hss⟩
    · cases h
end

end Lambda
