/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.NameSets
import Strata.Util.NameProofs

/-! # Properties of the name sets of a program

Key results:
- `Program.not_startsWith_of_noConflict` — when the known prefixes of a program cover its
  internal names and none is comparable with a prefix, no internal name starts with that prefix,
  so a pass may number names with it without looking at the program's names.
- `Program.identPrefixesCovered_of_none` — a program that records no prefixes is covered by the
  prefixes collected on demand.
- `Program.addIdentPrefixes_decls` — recording prefixes keeps the declarations.
-/

public section

namespace Core

/-! ## Recorded prefixes of internal names -/

/-- Recording prefixes keeps the declarations. -/
@[simp] theorem Program.addIdentPrefixes_decls (p : Program) (pfxs : List String) :
    (p.addIdentPrefixes pfxs).decls = p.decls := rfl

/-- The prefix (`Strata.Name.internalPrefixOf`) of every internal name of `p` is among the
    prefixes `collectIdentPrefixes` lists. -/
private theorem Program.internalPrefixOf_mem_collect {p : Program} {n : String}
    (hn : n ∈ p.internalNames) :
    Strata.Name.internalPrefixOf n ∈ p.collectIdentPrefixes := by
  unfold Program.collectIdentPrefixes
  rw [Std.HashSet.mem_toList]
  have key : ∀ (l : List String) (s : Std.HashSet String),
      (n ∈ l ∨ Strata.Name.internalPrefixOf n ∈ s) →
      Strata.Name.internalPrefixOf n ∈
        l.foldl (fun s n => s.insert (Strata.Name.internalPrefixOf n)) s := by
    intro l
    induction l with
    | nil => intro s h; simpa using h
    | cons x xs ih =>
      intro s h
      apply ih
      rcases h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact Or.inr (Std.HashSet.mem_insert_self ..)
        · exact Or.inl h
      · exact Or.inr (Std.HashSet.mem_insert.mpr (Or.inr h))
  exact key _ _ (Or.inl hn)

/-- Every name `Program.internalNames` lists is internal. -/
private theorem Program.isInternal_of_mem_internalNames {p : Program} {n : String}
    (hn : n ∈ p.internalNames) : Strata.Name.isInternal n = true :=
  (List.mem_filter.mp hn).2

/-- A program that records no prefixes is covered by the prefixes collected on demand
    (`Program.knownIdentPrefixes`): a pass that receives it never takes the fast path on an
    unchecked claim. -/
theorem Program.identPrefixesCovered_of_none {p : Program} (h : p.usedIdentPrefixes = none) :
    p.identPrefixesCovered = true := by
  unfold Program.identPrefixesCovered Program.knownIdentPrefixes
  rw [h, Option.getD_none, List.all_eq_true]
  intro n hn
  exact List.any_eq_true.mpr ⟨_, Program.internalPrefixOf_mem_collect hn,
    Strata.Name.startsWith_internalPrefixOf (Program.isInternal_of_mem_internalNames hn)⟩

/-- When the used prefixes of `p` cover its internal names and none is comparable with `pfx`, no
    internal name of `p` starts with `pfx`: a pass may number its names with `pfx` without looking
    at the program's names. -/
theorem Program.not_startsWith_of_noConflict {p : Program} {pfx : String}
    (hcov : p.identPrefixesCovered = true) (hfree : p.identPrefixConflicts pfx = [])
    {n : String} (hn : n ∈ p.internalNames) : n.startsWith pfx = false := by
  unfold Program.identPrefixesCovered at hcov
  obtain ⟨q, hq, hnq⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcov n hn)
  have hnc : Strata.Name.prefixesComparable pfx q = false := by
    cases h : Strata.Name.prefixesComparable pfx q
    · rfl
    · have : q ∈ p.identPrefixConflicts pfx := List.mem_filter.mpr ⟨hq, h⟩
      simp [hfree] at this
  cases hp : n.startsWith pfx
  · rfl
  · exfalso
    have h1 := (String.startsWith_string_iff ..).mp hp
    have h2 := (String.startsWith_string_iff ..).mp hnq
    rcases List.prefix_or_prefix_of_prefix h1 h2 with h | h
    · have : Strata.Name.prefixesComparable pfx q = true := by
        simp [Strata.Name.prefixesComparable, (String.startsWith_string_iff ..).mpr h]
      simp [this] at hnc
    · have : Strata.Name.prefixesComparable pfx q = true := by
        simp [Strata.Name.prefixesComparable, (String.startsWith_string_iff ..).mpr h]
      simp [this] at hnc

end Core

end -- public section
