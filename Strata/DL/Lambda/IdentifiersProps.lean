/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

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
  simp; rw[if_neg name_notin]
  cases meta_eq: (x.metadata == y.metadata); grind
  rw[beq_iff_eq] at meta_eq
  constructor
  . intros _; apply Or.inl; cases x; cases y; grind
  . rw[meta_eq]; intros _; simp

theorem Identifiers.addListWithErrorNotin {IDMeta} [DecidableEq IDMeta]
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}:
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
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}: m.addListWithError l f = .ok m' → ∀ y, m'.contains y ↔ y ∈ l ∨ m.contains y := by
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
  {m m': Identifiers IDMeta} {l: List (Identifier IDMeta)} {f: Identifier IDMeta → DiagnosticModel}: m.addListWithError l f = .ok m' → l.Nodup := by
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

end Lambda
