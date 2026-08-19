/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramFactSet

/-! # Properties of Core fact sets

The set-theoretic properties — membership in a set built from a list,
extensionality, what `applyPhase` reports — are properties of any fact set and
live with the machinery in `Strata/Pipeline/PhaseContract.lean`. What is left
here is what only makes sense for Core, where a fact *means* something about a
`Core.Program`:

* `ProgramFactSet.holds_of_subset` — a smaller fact set asserts less, so facts
  carried forward stay true.
* `ProgramFactSet.holds_applyPhase` — everything `applyPhase` reports really does
  hold on the output program: the bridge between the framework's set bookkeeping
  and what the facts mean on a program.

Two generic results keep a Core-side name because Core code names them:
`ProgramFactSet.mem_ofList`, which the asserting phase's obligation is proved
with, and `ProgramFactSet.ext_of_mem_iff`, which is what the test on canonical
uniqueness reads. The rest are used through the generic statements directly. -/

namespace Core

open Strata.Pipeline

public section

/-- A fact set built from a list holds exactly that list's facts. -/
@[simp] theorem ProgramFactSet.mem_ofList {f : ProgramFact} {l : List ProgramFact} :
    f ∈ ProgramFactSet.ofList l ↔ f ∈ l := mem_factSetOfList

/-- **Canonical representations are unique.** Extensionally equal fact sets are
    *equal*. This is the property that makes `ProgramFactSet` usable as a type
    index: it is what lets two pipelines meet at a shared intermediate fact
    set. -/
theorem ProgramFactSet.ext_of_mem_iff {σ₁ σ₂ : ProgramFactSet}
    (h : ∀ f, f ∈ σ₁ ↔ f ∈ σ₂) : σ₁ = σ₂ := factSet_ext h


---------------------------------------------------------------------

/-- A smaller fact set asserts less: when every fact of `σ₂` holds on a program
    and `σ₁` is included in `σ₂`, every fact of `σ₁` holds on it. -/
theorem ProgramFactSet.holds_of_subset {σ₁ σ₂ : ProgramFactSet} {p : Program}
    (h : σ₁ ⊑ σ₂) (hσ₂ : ProgramFactSet.holds σ₂ p) : ProgramFactSet.holds σ₁ p := by
  intro f hf; exact hσ₂ f (h f hf)

/-- Everything `applyPhase` reports really does hold on the output program, given
    the phase's own obligations. This is the bridge between the framework's set
    bookkeeping and what the facts mean on a program. -/
theorem ProgramFactSet.holds_applyPhase {establishes preserves σ : ProgramFactSet}
    {p : Program} (hest : ProgramFactSet.holds establishes p)
    (hpres : ProgramFactSet.holds σ p) :
    ProgramFactSet.holds (applyPhase establishes preserves σ) p := by
  intro f hf
  rcases mem_applyPhase.mp hf with h | ⟨h, _⟩
  · exact hest f h
  · exact hpres f h

end -- public section

end Core
