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
    List.map (fun s => (⟨s, ()⟩ : CoreIdent)) σ.cs.generated.unzip.snd = σ.generated ∧
    σ.generated.Nodup

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
  let newIdent : CoreIdent := ⟨s, ()⟩
  let newState : CoreGenState := { cs := cs', generated := newIdent :: σ.generated }
  (newIdent, newState)

theorem CoreGenState.WFMono' :
  CoreGenState.WF s →
  CoreGenState.gen pf s = (l, s') →
  CoreGenState.WF s' := by
  intros Hwf Hgen
  simp [gen] at Hgen
  simp [CoreGenState.WF, ← Hgen]
  generalize h1 : (StringGenState.gen pf.name s.cs).fst = st
  generalize h2 : (StringGenState.gen pf.name s.cs).snd = stg
  have Hstrgen : StringGenState.gen pf.name s.cs = (st, stg) := by simp [← h1, ← h2]
  have Hwf' := StringGenState.WFMono Hwf.left Hstrgen
  simp [StringGenState.gen] at Hstrgen
  refine ⟨Hwf', ?_, ?_⟩
  · simp [← Hwf.right.left, ← Hstrgen.right, ← Hstrgen.left]
  · have hnodup_old := Hwf.right.right
    have hst_fresh : ⟨st, ()⟩ ∉ s.generated := by
      intro hmem
      rw [← Hwf.right.left] at hmem
      have hst_in_snd : st ∈ s.cs.generated.unzip.snd := by
        simp only [List.mem_map] at hmem
        obtain ⟨s', hs', heq⟩ := hmem
        have : s' = st := by simp [Lambda.Identifier.mk.injEq] at heq; exact heq
        rw [← this]; exact hs'
      have hnodup_new := Hwf'.right.right.left
      simp [← Hstrgen.right, Hstrgen.left] at hnodup_new
      have : ∃ x, (x, st) ∈ s.cs.generated := by
        simp only [List.unzip_snd, List.mem_map] at hst_in_snd
        obtain ⟨p, hp, heq⟩ := hst_in_snd
        exact ⟨p.1, by cases p; simp_all⟩
      obtain ⟨x, hx⟩ := this
      exact hnodup_new.left x hx
    exact ⟨hst_fresh, hnodup_old⟩

theorem CoreGenState.WFMono : ∀ (γ γ' : CoreGenState) (pf l : CoreIdent),
  CoreGenState.gen pf γ = (l, γ') → WF γ → WF γ' ∧ l ∈ γ'.generated ∧ γ ⊆ γ' := by
  intros γ γ' pf l Hgen Hwf
  have Hwf':= WFMono' Hwf Hgen
  simp [gen] at Hgen
  refine ⟨?_, ?_, ?_⟩
  · assumption
  · simp [← Hgen.right, ← Hgen.left]
  · simp only [Subset, ← Hgen.right]
    exact List.subset_cons_self _ _

/-- CoreLabelGen guarantees that all labels are .temp -/
instance : LabelGen.WFLabelGen CoreIdent CoreGenState where
  emp := .emp
  gen := CoreGenState.gen
  generated := CoreGenState.generated
  wf := CoreGenState.WF
  wf_emp := by
    simp [CoreGenState.WF, StringGenState.WF, Counter.WF]
  wf_gen := CoreGenState.WFMono

abbrev CoreGenM := StateM CoreGenState

end Core
