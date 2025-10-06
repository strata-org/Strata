/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Statement
import Strata.DL.Util.LabelGen
import Strata.DL.Util.StringGen
import Strata.DL.Util.ListUtils
open Boogie Lambda Imperative

/-! ## Boogie Identifier Generator
  This file contains a Boogie Identifier generator `BoogieGenState.gen`, where the
  uniqueness of the generated identifiers is designed to be provable. It relies on a
  `StringGenState` to generate unique strings (See `StringGen.lean`).

  Also see `LabelGen.lean` for the generic type class for a unique label generator.
-/
namespace Names

def initVarValue (id : BoogieIdent) : Expression.Expr :=
  .fvar ("init_" ++ id.2) none

end Names

namespace Boogie

structure BoogieGenState where
  cs : StringGenState
  generated : List BoogieIdent := []

def BoogieGenState.WF (σ : BoogieGenState)
  := StringGenState.WF σ.cs ∧
    List.map Boogie.BoogieIdent.temp σ.cs.generated.unzip.snd = σ.generated ∧
    σ.generated.Nodup ∧
    Forall (BoogieIdent.isTemp ·) σ.generated

instance : HasSubset BoogieGenState where
  Subset σ₁ σ₂ := σ₁.generated.Subset σ₂.generated

@[simp]
def BoogieGenState.emp : BoogieGenState := { cs := .emp, generated := [] }

/-- A BoogieIdent generator
    NOTE: we need to wrap the prefix into a BoogieIdent in order to conform with the interface of UniqueLabelGen.gen
    TODO: Maybe use genIdent or genIdents?
    -/
def BoogieGenState.gen (pf : BoogieIdent) (σ : BoogieGenState)
  : BoogieIdent × BoogieGenState :=
  let (s, cs') := StringGenState.gen pf.2 σ.cs
  let newState : BoogieGenState := { cs := cs', generated := (.temp s) :: σ.generated }
  ((.temp s), newState)

theorem genBoogieIdentTemp :
  BoogieGenState.gen pf s = (l, s') → BoogieIdent.isTemp l := by
  intros Hgen
  simp [BoogieGenState.gen] at Hgen
  rw [← Hgen.1]
  constructor

theorem BoogieGenState.WFMono' :
  BoogieGenState.WF s →
  BoogieGenState.gen pf s = (l, s') →
  BoogieGenState.WF s' := by
  intros Hwf Hgen
  unfold BoogieGenState.WF at Hwf
  simp [gen] at Hgen
  simp [← Hgen]
  generalize h1 : (StringGenState.gen pf.snd s.cs).fst = st
  generalize h2 : (StringGenState.gen pf.snd s.cs).snd = stg
  have Hstrgen: StringGenState.gen pf.snd s.cs = (st, stg) := by simp [← h1, ← h2]
  have Hwf':= StringGenState.WFMono Hwf.left Hstrgen
  simp [StringGenState.gen] at Hstrgen
  constructor <;> simp [*]
  constructor
  simp_all
  simp [← Hwf.right.left, ← Hgen.left, ← Hstrgen.right, ← Hstrgen.left]
  constructor <;> try simp [BoogieIdent.isTemp]
  simp [← Hwf.right.left]
  intro x str Hx
  false_or_by_contra
  have: str = st := by injections
  have Hnodup := Hwf'.right.right.left
  simp [← Hstrgen.right, Hstrgen.left] at Hnodup
  have Hnodup := Hnodup.left x
  simp_all

theorem BoogieGenState.WFMono : ∀ (γ γ' : BoogieGenState) (pf l : BoogieIdent),
  BoogieGenState.gen pf γ = (l, γ') → WF γ → WF γ' ∧ l ∈ γ'.generated ∧ γ ⊆ γ' := by
  intros γ γ' pf l Hgen Hwf
  have Hwf':= WFMono' Hwf Hgen
  simp [gen] at Hgen
  refine ⟨?_, ?_, ?_⟩
  assumption
  simp [← Hgen.right, ← Hgen.left]
  simp [Subset, ← Hgen.right]
  apply List.subset_cons_self

/-- BoogieLabelGen guarantees that all labels are .temp -/
instance : LabelGen.WFLabelGen BoogieIdent BoogieGenState where
  emp := .emp
  gen := BoogieGenState.gen
  generated := BoogieGenState.generated
  wf := BoogieGenState.WF
  wf_emp := by
    simp [BoogieGenState.WF, StringGenState.WF, Counter.WF]
    constructor
  wf_gen := BoogieGenState.WFMono

abbrev BoogieGenM := StateM BoogieGenState

end Boogie
