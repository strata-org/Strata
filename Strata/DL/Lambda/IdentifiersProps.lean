/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.DL.Lambda.Identifiers
import all Strata.DL.Lambda.Identifiers
import Std.Data.HashMap.Lemmas

/-!
## Properties of `Lambda.Identifiers`

Theorems about inserting into an `Identifiers` map via `addWithError` /
`addListWithError`.

- `addWithErrorNotin` / `addListWithErrorNotin` — a successful insert means the
  element(s) were absent from the map beforehand.
- `addWithErrorContains` / `addListWithErrorContains` — characterize `contains`
  on the resulting map after a successful insert (the new element(s), plus
  whatever was already present).
- `addListWithErrorNoDup` — a successful `addListWithError` implies the inserted
  list is duplicate-free.
-/

namespace Lambda
open Std (ToFormat Format format)
open Strata

theorem Identifiers.addWithErrorNotin {IDMeta} [DecidableEq IDMeta] {m m': Identifiers IDMeta} {x: Identifier IDMeta}: m.addWithError x f = .ok m' → m.contains x = false := by
  unfold addWithError contains
  simp
  grind

theorem Identifiers.addWithErrorContains {IDMeta} [DecidableEq IDMeta] {m m': Identifiers IDMeta} {x: Identifier IDMeta}: m.addWithError x f = .ok m' → ∀ y, m'.contains y ↔ x = y ∨ m.contains y := by
  unfold addWithError contains;
  have m_contains := (Std.HashMap.containsThenInsertIfNew_fst (m:=m) (k:=x.name) (v:=x.metadata));
  have m'_def := (Std.HashMap.containsThenInsertIfNew_snd (m:=m) (k:=x.name) (v:=x.metadata));
  revert m_contains m'_def
  rcases (Std.HashMap.containsThenInsertIfNew m x.name x.metadata) with ⟨b, m''⟩; simp; intros b_eq m''_eq; subst b m'';
  split <;> intros m_contains; contradiction
  injection m_contains; subst m'; intros y; rw[Std.HashMap.getElem?_insertIfNew]
  cases name_eq: (x.name == y.name); grind
  rw[beq_iff_eq] at name_eq
  rename_i m_contains
  have name_notin : ¬ x.name ∈ m := by grind
  simp; rw[ite_eq_right name_notin]
  cases meta_eq: (x.metadata == y.metadata); grind
  rw[beq_iff_eq] at meta_eq
  constructor
  . intros _; apply Or.inl; cases x; cases y; grind
  . rw[meta_eq]; intros _; simp

theorem Identifiers.addListWithErrorNotin {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → Message}:
  m.addListWithError l f = .ok m' → forall x, x ∈ l → m.contains x = false := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    intros x
    rw[List.mem_cons]
    rename_i Heq
    have Hin := Identifiers.addWithErrorNotin Heq
    have := addWithErrorContains Heq x; grind

theorem Identifiers.addListWithErrorContains {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → Message}: m.addListWithError l f = .ok m' → ∀ y, m'.contains y ↔ y ∈ l ∨ m.contains y := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp; intros Heq; cases Heq; grind
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    intros x
    rw[List.mem_cons]
    rename_i Heq
    have Hcont := Identifiers.addWithErrorContains Heq x
    have Hin := Identifiers.addWithErrorNotin Heq
    grind

theorem Identifiers.addListWithErrorNoDup {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → Message}: m.addListWithError l f = .ok m' → l.Nodup := by
  unfold addListWithError
  induction l generalizing m m' with
  | nil => simp
  | cons h t IH =>
    simp only[List.foldlM, bind, Except.bind]
    split <;> intros Hid; try contradiction
    apply List.nodup_cons.mpr
    constructor <;> try grind
    intros h_in_t
    rename_i Hadd
    have := Identifiers.addWithErrorContains Hadd h
    have := Identifiers.addListWithErrorNotin Hid h
    grind

/-! ### Identifier conditions as name membership -/

/-- A name registered in the map has a lookup, and conversely. -/
theorem Identifiers.containsName_eq_true_iff_mem {IDMeta} [DecidableEq IDMeta]
    (m : Identifiers IDMeta) (n : String) :
    Identifiers.containsName m n = true ↔ n ∈ m := by
  unfold Identifiers.containsName
  rw [← Std.HashMap.contains_eq_isSome_getElem?]
  exact Std.HashMap.contains_iff_mem

/-- With `Unit` metadata, membership of an identifier and of its name agree. -/
theorem Identifiers.contains_eq_containsName_unit (m : Identifiers Unit)
    (x : Identifier Unit) :
    Identifiers.contains m x = Identifiers.containsName m x.name := by
  unfold Identifiers.contains Identifiers.containsName
  split
  · rename_i v hv; simp [hv]
  · rename_i hv; simp [hv]

/-- A successful registration inserts the new name into the map. -/
theorem Identifiers.addWithError_ok_eq {IDMeta}
    {m m' : Identifiers IDMeta} {x : Identifier IDMeta} {f : Message}
    (h : m.addWithError x f = .ok m') : m' = m.insertIfNew x.name x.metadata := by
  simp only [Identifiers.addWithError] at h
  generalize hgen : m.containsThenInsertIfNew x.name x.metadata = p at h
  cases hb : p.fst with
  | true => simp only [hb, reduceIte, reduceCtorEq] at h
  | false =>
    simp only [hb, Bool.false_eq_true, ite_false, Except.ok.injEq] at h
    rw [← h, ← hgen]
    exact Std.HashMap.containsThenInsertIfNew_snd

/-- A successful registration keeps every name the map held. -/
theorem Identifiers.addWithError_mem_mono {IDMeta}
    {m m' : Identifiers IDMeta} {x : Identifier IDMeta} {f : Message}
    (h : m.addWithError x f = .ok m') : ∀ n : String, n ∈ m → n ∈ m' := by
  intro n hn
  rw [Identifiers.addWithError_ok_eq h]
  exact Std.HashMap.mem_insertIfNew.mpr (Or.inr hn)

/-- A successful registration holds only the new name and the names the map held. -/
theorem Identifiers.addWithError_mem_inv {IDMeta}
    {m m' : Identifiers IDMeta} {x : Identifier IDMeta} {f : Message}
    (h : m.addWithError x f = .ok m') : ∀ n : String, n ∈ m' → n = x.name ∨ n ∈ m := by
  intro n hn
  rw [Identifiers.addWithError_ok_eq h] at hn
  rcases Std.HashMap.mem_insertIfNew.mp hn with hEq | hMem
  · exact Or.inl (beq_iff_eq.mp hEq).symm
  · exact Or.inr hMem

/-- A successful list registration keeps every name the map held. -/
theorem Identifiers.addListWithError_mem_mono {IDMeta}
    {m m' : Identifiers IDMeta} {l : List (Identifier IDMeta)}
    {f : Identifier IDMeta → Message}
    (h : m.addListWithError l f = .ok m') : ∀ n : String, n ∈ m → n ∈ m' := by
  unfold Identifiers.addListWithError at h
  induction l generalizing m with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact fun n hn => hn
  | cons a rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · exact absurd h (by simp)
    · rename_i m1 hm1
      exact fun n hn => ih h n (Identifiers.addWithError_mem_mono hm1 n hn)

/-- A successful list registration records the name of every identifier it was given. -/
theorem Identifiers.addListWithError_mem_new {IDMeta} [DecidableEq IDMeta]
    {m m' : Identifiers IDMeta} {l : List (Identifier IDMeta)}
    {f : Identifier IDMeta → Message}
    (h : m.addListWithError l f = .ok m') : ∀ x ∈ l, x.name ∈ m' := by
  intro x hx
  have hc := (Identifiers.addListWithErrorContains h x).mpr (Or.inl hx)
  unfold Identifiers.contains at hc
  cases hlk : m'[x.name]? with
  | none => rw [hlk] at hc; exact absurd hc (by simp)
  | some v =>
    rw [← Std.HashMap.contains_iff_mem, Std.HashMap.contains_eq_isSome_getElem?, hlk]
    rfl

/-- A name a successful registration accepted was absent from the map beforehand. -/
theorem Identifiers.addListWithError_not_mem {m m' : Identifiers Unit}
    {l : List (Identifier Unit)} {f : Identifier Unit → Message}
    (h : m.addListWithError l f = .ok m') : ∀ x ∈ l, x.name ∉ m := by
  intro x hx hmem
  have hc := Identifiers.addListWithErrorNotin h x hx
  rw [Identifiers.contains_eq_containsName_unit] at hc
  have hyes := (Identifiers.containsName_eq_true_iff_mem m x.name).mpr hmem
  rw [hc] at hyes
  exact absurd hyes (by simp)

/-- A successful registration keeps every lookup the map answered before. -/
theorem Identifiers.addWithError_getElem?_mono {IDMeta} (m m' : Identifiers IDMeta)
    (x : Identifier IDMeta) (f : Message)
    (h : m.addWithError x f = .ok m') :
    ∀ (ref : String) (n : IDMeta), m[ref]? = some n → m'[ref]? = some n := by
  intro ref n hn
  simp only [Identifiers.addWithError, Std.HashMap.containsThenInsertIfNew_fst,
    Std.HashMap.containsThenInsertIfNew_snd] at h
  split at h
  · simp at h
  · rename_i hc
    simp only [Except.ok.injEq] at h
    subst h
    rw [Std.HashMap.getElem?_insertIfNew]
    split
    · rename_i hcond
      obtain ⟨heq, hnm⟩ := hcond
      rw [beq_iff_eq] at heq
      subst heq
      exact absurd (Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [hn]; rfl)) hnm
    · exact hn

end Lambda
