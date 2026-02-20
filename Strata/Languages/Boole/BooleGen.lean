/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.Boole
import Strata.DL.Util.LabelGen
import Strata.DL.Util.StringGen
import Strata.DL.Util.ListUtils

open Strata Boole Lambda Imperative

/-! ## Boole Identifier Generator
  This file contains a Boole Identifier generator `BooleGenState.gen`, where the
  uniqueness of the generated identifiers is designed to be provable. It relies on a
  `StringGenState` to generate unique strings (See `StringGen.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
-/
namespace Strata.Boole.Names

def initVarValue (id : BooleIdent) : Expression.Expr :=
  .fvar () (BooleIdent.unres ("init_" ++ id.name)) none

end Boole.Names

namespace Boole

structure BooleGenState where
  cs : StringGenState
  generated : List BooleIdent := []

def BooleGenState.WF (σ : BooleGenState)
  := StringGenState.WF σ.cs ∧
    List.map Boole.BooleIdent.temp σ.cs.generated.unzip.snd = σ.generated ∧
    σ.generated.Nodup ∧
    Forall (BooleIdent.isTemp ·) σ.generated

instance : HasSubset BooleGenState where
  Subset σ₁ σ₂ := σ₁.generated.Subset σ₂.generated

@[simp]
def BooleGenState.emp : BooleGenState := { cs := .emp, generated := [] }

/-- A BooleIdent generator
    NOTE: we need to wrap the prefix into a BooleIdent in order to conform with the interface of UniqueLabelGen.gen
    TODO: Maybe use genIdent or genIdents?
    -/
def BooleGenState.gen (pf : BooleIdent) (σ : BooleGenState)
  : BooleIdent × BooleGenState :=
  let (s, cs') := StringGenState.gen pf.name σ.cs
  let newState : BooleGenState := { cs := cs', generated := (.temp s) :: σ.generated }
  ((.temp s), newState)

theorem genBooleIdentTemp :
  BooleGenState.gen pf s = (l, s') → BooleIdent.isTemp l := by
  intros Hgen
  simp [BooleGenState.gen] at Hgen
  rw [← Hgen.1]
  constructor

theorem BooleGenState.WFMono' :
  BooleGenState.WF s →
  BooleGenState.gen pf s = (l, s') →
  BooleGenState.WF s' := by
  intros Hwf Hgen
  unfold BooleGenState.WF at Hwf
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
  constructor <;> try simp [BooleIdent.isTemp]
  simp [← Hwf.right.left]
  intro x str Hx
  false_or_by_contra
  have: str = st := by injections
  have Hnodup := Hwf'.right.right.left
  simp [← Hstrgen.right, Hstrgen.left] at Hnodup
  have Hnodup := Hnodup.left x
  simp_all

theorem BooleGenState.WFMono : ∀ (γ γ' : BooleGenState) (pf l : BooleIdent),
  BooleGenState.gen pf γ = (l, γ') → WF γ → WF γ' ∧ l ∈ γ'.generated ∧ γ ⊆ γ' := by
  intros γ γ' pf l Hgen Hwf
  have Hwf':= WFMono' Hwf Hgen
  simp [gen] at Hgen
  refine ⟨?_, ?_, ?_⟩
  assumption
  simp [← Hgen.right, ← Hgen.left]
  simp [Subset, ← Hgen.right]
  apply List.subset_cons_self

/-- BooleLabelGen guarantees that all labels are .temp -/
instance : LabelGen.WFLabelGen BooleIdent BooleGenState where
  emp := .emp
  gen := BooleGenState.gen
  generated := BooleGenState.generated
  wf := BooleGenState.WF
  wf_emp := by
    simp [BooleGenState.WF, StringGenState.WF, Counter.WF]
    constructor
  wf_gen := BooleGenState.WFMono

abbrev BooleGenM := StateM BooleGenState

end Strata.Boole
