/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Statement
import Strata.DL.Util.LabelGen
import Strata.DL.Util.StringGen
import Strata.DL.Util.ListUtils
open Core Lambda Imperative

/-! ## Strata Core Identifier Generator
  This file contains a Strata Core Identifier generator `CoreGenState.gen`, where the
  uniqueness of the generated identifiers is designed to be provable. It relies on a
  `StringGenState` to generate unique strings (See `StringGen.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
-/

namespace Core

structure CoreGenState where
  cs : StringGenState
  generated : List CoreIdent := []

def CoreGenState.WF (σ : CoreGenState)
  := StringGenState.WF σ.cs ∧
    List.map Core.CoreIdent.temp σ.cs.generated.unzip.snd = σ.generated ∧
    σ.generated.Nodup ∧
    Forall (CoreIdent.isTemp ·) σ.generated

instance : HasSubset CoreGenState where
  Subset σ₁ σ₂ := σ₁.generated.Subset σ₂.generated

@[simp]
def CoreGenState.emp : CoreGenState := { cs := .emp, generated := [] }

/-- A CoreIdent generator
    NOTE: we need to wrap the prefix into a CoreIdent in order to conform with the interface of UniqueLabelGen.gen
    TODO: Maybe use genIdent or genIdents?
    -/
def CoreGenState.gen (pf : CoreIdent) (σ : CoreGenState)
  : CoreIdent × CoreGenState :=
  let (s, cs') := StringGenState.gen pf.name σ.cs
  let newState : CoreGenState := { cs := cs', generated := (.temp s) :: σ.generated }
  ((.temp s), newState)

theorem genCoreIdentTemp :
  CoreGenState.gen pf s = (l, s') → CoreIdent.isTemp l := by
  intros Hgen
  simp [CoreGenState.gen] at Hgen
  rw [← Hgen.1]
  constructor

theorem CoreGenState.WFMono' :
  CoreGenState.WF s →
  CoreGenState.gen pf s = (l, s') →
  CoreGenState.WF s' := by
  intros Hwf Hgen
  unfold CoreGenState.WF at Hwf
  simp [gen] at Hgen
  simp [← Hgen]
  generalize h1 : (StringGenState.gen pf.name s.cs).fst = st
  generalize h2 : (StringGenState.gen pf.name s.cs).snd = stg
  have Hstrgen: StringGenState.gen pf.name s.cs = (st, stg) := by simp [← h1, ← h2]
  have Hwf':= StringGenState.WFMono Hwf.left Hstrgen
  simp [StringGenState.gen] at Hstrgen
  constructor <;> simp [*]
  constructor
  simp_all
  simp [← Hwf.right.left, ← Hgen.left, ← Hstrgen.right, ← Hstrgen.left]
  constructor <;> try simp [CoreIdent.isTemp]
  simp [← Hwf.right.left]
  intro x str Hx
  false_or_by_contra
  have: str = st := by injections
  have Hnodup := Hwf'.right.right.left
  simp [← Hstrgen.right, Hstrgen.left] at Hnodup
  have Hnodup := Hnodup.left x
  simp_all

theorem CoreGenState.WFMono : ∀ (γ γ' : CoreGenState) (pf l : CoreIdent),
  CoreGenState.gen pf γ = (l, γ') → WF γ → WF γ' ∧ l ∈ γ'.generated ∧ γ ⊆ γ' := by
  intros γ γ' pf l Hgen Hwf
  have Hwf':= WFMono' Hwf Hgen
  simp [gen] at Hgen
  refine ⟨?_, ?_, ?_⟩
  assumption
  simp [← Hgen.right, ← Hgen.left]
  simp [Subset, ← Hgen.right]
  apply List.subset_cons_self

/-- CoreLabelGen guarantees that all labels are .temp -/
instance : LabelGen.WFLabelGen CoreIdent CoreGenState where
  emp := .emp
  gen := CoreGenState.gen
  generated := CoreGenState.generated
  wf := CoreGenState.WF
  wf_emp := by
    simp [CoreGenState.WF, StringGenState.WF, Counter.WF]
    constructor
  wf_gen := CoreGenState.WFMono

abbrev CoreGenM := StateM CoreGenState

end Core
