/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Pipeline.PhaseContract

/-! # Properties of fact sets and phase contracts

Key results:

* `mem_factSetOfList` — a set built from a list holds exactly that list's facts,
  whatever order or duplicates the list had.
* `mem_factSetUnion`, `mem_factSetInter` — membership in a union and an
  intersection, from which everything about `applyPhase` follows.
* `mem_applyPhase` — what a pipeline knows after a phase: the facts the phase
  establishes, and those it was handed and preserves. This is the theorem the
  composition check rests on.
* `applyPhase_emptyFactSet_preserves` — a phase preserving nothing leaves exactly
  what it establishes, which is the safe default doing its job.
* `emptyFactSet_subset` — every set supplies the empty one, so a phase requiring
  nothing composes anywhere.
* `missingFacts_eq_nil_iff` — the diagnostic reports nothing missing exactly when
  the requirement is met, which is what lets a rejection be described by listing
  what is missing.

Kept apart from the definitions, following the `…Props.lean` convention. Two
results stay with them because instances there are built from them:
`factSet_ext`, which decidable equality on sets uses, and the canonicity lemmas
in `FactSet.lean`, which the default `FactAlgebra` instance is built from. -/

namespace Strata.Pipeline

public section

variable {F : Type} [FactVocabulary F] [FactAlgebra F]

/-- Membership in a set is membership in the facts it lists. -/
@[simp] theorem mem_factsOf {f : F} {σ : FactSet F} : f ∈ factsOf σ ↔ f ∈ σ := Iff.rfl

/-- A set built from a list holds exactly that list's facts. -/
@[simp] theorem mem_factSetOfList {f : F} {l : List F} : f ∈ factSetOfList (F := F) l ↔ f ∈ l :=
  FactAlgebra.mem_toList f l

/-- The empty set holds no fact. -/
@[simp] theorem not_mem_emptyFactSet {f : F} : f ∉ emptyFactSet (F := F) := by
  simp [emptyFactSet]

/-- The full set holds every fact of the vocabulary. -/
@[simp] theorem mem_allFactSet {f : F} : f ∈ allFactSet (F := F) := by
  simp [allFactSet, FactVocabulary.all_complete f]

/-- A fact is in a union exactly when it is in one of the two sets. -/
@[simp] theorem mem_factSetUnion {f : F} {σ₁ σ₂ : FactSet F} :
    f ∈ factSetUnion σ₁ σ₂ ↔ f ∈ σ₁ ∨ f ∈ σ₂ :=
  FactAlgebra.mem_union σ₁ σ₂ f

/-- A fact is in an intersection exactly when it is in both sets. -/
@[simp] theorem mem_factSetInter {f : F} {σ₁ σ₂ : FactSet F} :
    f ∈ factSetInter σ₁ σ₂ ↔ f ∈ σ₁ ∧ f ∈ σ₂ :=
  FactAlgebra.mem_inter σ₁ σ₂ f

/-- Every set supplies the empty one, so a phase that requires nothing composes
    anywhere. -/
@[simp] theorem emptyFactSet_subset (σ : FactSet F) : emptyFactSet (F := F) ⊑ σ := by
  intro f hf
  simp [emptyFactSet] at hf

/-- A fact is known after a phase when the phase establishes it, or when it was
    known before and the phase preserves it. Anything else is dropped. -/
@[simp] theorem mem_applyPhase {f : F} {establishes preserves σ : FactSet F} :
    f ∈ applyPhase establishes preserves σ ↔
      f ∈ establishes ∨ (f ∈ σ ∧ f ∈ preserves) := by
  simp [applyPhase]

/-- A phase that preserves nothing leaves the pipeline knowing exactly what that
    phase establishes, whatever it knew before. This is correct behaviour, not a
    bug: declaring no `preserves` drops incoming facts. -/
@[simp] theorem applyPhase_emptyFactSet_preserves (establishes σ : FactSet F) :
    applyPhase establishes emptyFactSet σ = establishes := by
  apply factSet_ext
  intro f
  simp

/-- Rebuilding a set from the facts it lists gives the same set back, so the two
    ways of constructing one agree wherever both apply. -/
theorem factSetOfList_factsOf (σ : FactSet F) : factSetOfList (factsOf σ) = σ := by
  apply factSet_ext
  intro f
  simp

/-- The diagnostic reports nothing missing exactly when the requirement is met,
    which is what makes it safe to describe a rejection by listing what it
    returns. -/
theorem missingFacts_eq_nil_iff {needed σ : FactSet F} :
    missingFacts needed σ = [] ↔ needed ⊑ σ := by
  unfold missingFacts factSetSubset
  rw [List.filter_eq_nil_iff]
  simp

end -- public section

end Strata.Pipeline
