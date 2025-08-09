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
  simp [gen] at Hgen
  refine ⟨?_, ?_, ?_⟩
  . -- StringGen WF
    rw [← Hgen.2]
    simp_all
    cases Hwf with
    | intro left right =>
    apply StringGenState.WFMono (n:=(StringGenState.gen pf.snd s.cs).fst)
    exact left
    rfl
  . -- nodup
    simp [← Hgen]
    have Hwfs : StringGenState.WF (StringGenState.gen pf.snd s.cs).snd := by
      apply StringGenState.WFMono
      simp [WF] at Hwf
      apply Hwf.1
      rfl
    simp [StringGenState.WF] at Hwfs
    /- The generated Boogie identifier does not occur in the list of already
    generated identifiers -/
    sorry
  . -- is temp
    refine List.Forall_mem_iff.mpr ?_
    intros x Hin
    rw [← Hgen.2] at Hin
    simp at Hin
    cases Hin
    case inl HH =>
      simp [HH]
      constructor
    case inr HH =>
    . simp [WF] at Hwf
      exact List.Forall_mem_iff.mp Hwf.2.2 _ HH

theorem BoogieGenState.WFMono : ∀ (γ γ' : BoogieGenState) (pf l : BoogieIdent),
  BoogieGenState.gen pf γ = (l, γ') → WF γ → WF γ' ∧ l ∈ γ'.generated ∧ γ ⊆ γ' := by
  intros γ γ' pf l Hgen Hwf
  refine ⟨?_, ?_, ?_⟩
  . exact WFMono' Hwf Hgen
  . /- The generated Boogie identifier is in the new state, should be provable by
    propagating this fact from StringGen and Counter generator -/
    sorry
  . /- After generating a new Boogie identifier, the new state is a super set of
    the old state -/
    sorry

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
