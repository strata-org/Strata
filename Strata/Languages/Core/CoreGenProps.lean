/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.CoreGen
import all Strata.Languages.Core.CoreGen
import all Strata.DL.Util.StringGen
import all Strata.DL.Util.Counter
import Std.Tactic.BVDecide.Normalize.Prop
open Core Lambda

/-! ## Properties of the Strata Core Identifier Generator

  Well-formedness of `CoreGenState` is preserved by `CoreGenState.gen` and holds of
  `CoreGenState.emp`, which makes `CoreGenState` a `LabelGen.WFLabelGen`.
-/

namespace Core
public section

theorem CoreGenState.WFMono' :
  CoreGenState.WF s →
  CoreGenState.gen pf s = (l, s') →
  CoreGenState.WF s' := by
  intros Hwf Hgen
  simp [gen] at Hgen
  simp only [WF, ← Hgen, List.unzip_snd, List.map_map, List.nodup_cons]
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
        have : s' = st := by simp only [Identifier.mk.injEq, and_true] at heq; exact heq
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

/-- The empty generator state is well formed: a transformation run from
    `Transform.CoreTransformState.emp` starts from a well-formed generator state. -/
theorem CoreGenState.wf_emp : CoreGenState.emp.WF := by
  simp [CoreGenState.WF, StringGenState.WF, Counter.WF]

/-- CoreLabelGen guarantees that all labels are .temp -/
instance : LabelGen.WFLabelGen CoreIdent CoreGenState where
  emp := .emp
  gen := CoreGenState.gen
  generated := CoreGenState.generated
  wf := CoreGenState.WF
  wf_emp := CoreGenState.wf_emp
  wf_gen := CoreGenState.WFMono

end
end Core
