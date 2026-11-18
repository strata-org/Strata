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
import Std.Data.HashSet.Lemmas
open Core Lambda

/-! ## Properties of the Strata Core Identifier Generator

  Well-formedness of `CoreGenState` is preserved by `CoreGenState.gen` and holds of
  `CoreGenState.emp`, which makes `CoreGenState` a `LabelGen.WFLabelGen`. `genAvoiding_spec`
  states that a name from `genAvoiding` is new and not in `taken`, and the state stays well formed.
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

/-- One draw of `CoreGenState.gen` from a well-formed state gives a well-formed state whose
    generated names are exactly the drawn name consed onto the old ones, and the drawn name is
    not among the old ones. -/
private theorem CoreGenState.gen_spec {pf : CoreIdent} {γ γ' : CoreGenState} {n : CoreIdent}
    (hwf : γ.WF) (h : CoreGenState.gen pf γ = (n, γ')) :
    γ'.WF ∧ γ'.generated = n :: γ.generated ∧ n ∉ γ.generated := by
  have hwf' := CoreGenState.WFMono' hwf h
  have hgen : γ'.generated = n :: γ.generated := by
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (·.2.generated) h
    simp only [CoreGenState.gen] at h1 h2
    rw [← h2, ← h1]
  have hnd := hwf'.2.2
  rw [hgen] at hnd
  exact ⟨hwf', hgen, (List.nodup_cons.mp hnd).1⟩

/-- One draw of `gen` from a well-formed state gives a well-formed state in which the drawn name
    is new, is among the new generated names, and the old names are kept. Some state draws that
    name first. -/
private theorem CoreGenState.gen_draw {pf : CoreIdent} {γ γ' : CoreGenState} {n : CoreIdent}
    (hwf : γ.WF) (h : CoreGenState.gen pf γ = (n, γ')) :
    γ'.WF ∧ n ∈ γ'.generated ∧ n ∉ γ.generated ∧ γ.generated ⊆ γ'.generated ∧
      ∃ γ₀ : CoreGenState, (CoreGenState.gen pf γ₀).1 = n := by
  obtain ⟨hwf', hgen, hfresh⟩ := CoreGenState.gen_spec hwf h
  refine ⟨hwf', ?_, hfresh, ?_, γ, congrArg Prod.fst h⟩
  · rw [hgen]; exact List.mem_cons_self
  · rw [hgen]; exact List.subset_cons_self _ _

/-- `genAvoiding.go` returns a name outside `taken` when its fuel plus the number of distinct
    names of `taken` the generator has already drawn is at least the size of `taken`: every draw
    is new, so the draws cannot all be names of `taken`. -/
private theorem CoreGenState.genAvoiding_go_not_mem (taken : Std.HashSet String)
    (pf : CoreIdent) (fuel : Nat) :
    ∀ {γ γ' : CoreGenState} {n : CoreIdent} (drawn : List String), γ.WF → drawn.Nodup →
      (∀ d ∈ drawn, d ∈ taken ∧ (⟨d, ()⟩ : CoreIdent) ∈ γ.generated) →
      taken.size ≤ fuel + drawn.length →
      CoreGenState.genAvoiding.go taken pf fuel γ = (n, γ') → n.name ∉ taken := by
  induction fuel with
  | zero =>
    intro γ γ' n drawn hwf hnd hdrawn hsize h hmem
    simp only [CoreGenState.genAvoiding.go] at h
    obtain ⟨-, -, hfresh⟩ := CoreGenState.gen_spec hwf h
    have hnot : n.name ∉ drawn := fun hd => hfresh (hdrawn _ hd).2
    have hnodup : (n.name :: drawn).Nodup := List.nodup_cons.mpr ⟨hnot, hnd⟩
    have hsub : (n.name :: drawn) ⊆ taken.toList := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Std.HashSet.mem_toList.mpr hmem
      · exact Std.HashSet.mem_toList.mpr (hdrawn x hx).1
    have hlen := List.Nodup.length_le_of_subset hnodup hsub
    simp only [List.length_cons, Std.HashSet.length_toList] at hlen
    omega
  | succ fuel ih =>
    intro γ γ' n drawn hwf hnd hdrawn hsize h
    simp only [CoreGenState.genAvoiding.go, bind, StateT.bind, pure] at h
    generalize hg : CoreGenState.gen pf γ = r at h
    obtain ⟨n1, γ1⟩ := r
    obtain ⟨hwf1, hgen, hfresh⟩ := CoreGenState.gen_spec hwf hg
    split at h
    · rename_i hcont
      have hmem1 : n1.name ∈ taken := Std.HashSet.contains_iff_mem.mp hcont
      have hnot : n1.name ∉ drawn := fun hd => hfresh (hdrawn _ hd).2
      refine ih (n1.name :: drawn) hwf1 (List.nodup_cons.mpr ⟨hnot, hnd⟩) ?_ ?_ h
      · intro d hd
        rw [hgen]
        rcases List.mem_cons.mp hd with rfl | hd
        · exact ⟨hmem1, List.mem_cons_self⟩
        · exact ⟨(hdrawn d hd).1, List.mem_cons_of_mem _ (hdrawn d hd).2⟩
      · simp only [List.length_cons]
        omega
    · rename_i hcont
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact fun hmem => hcont (Std.HashSet.contains_iff_mem.mpr hmem)

/-- A name `genAvoiding` draws is one `CoreGenState.gen` draws: it is new, the generator stays
    well formed, and the generated names only grow. The name is also not in `taken`; this is a
    standalone guarantee, which keeps a generated name apart from names the caller passes as
    `taken`, such as the type names a program declares. -/
theorem CoreGenState.genAvoiding_spec (taken : Std.HashSet String) (pf : CoreIdent)
    {γ γ' : CoreGenState} {n : CoreIdent} (hwf : γ.WF)
    (h : CoreGenState.genAvoiding taken pf γ = (n, γ')) :
    γ'.WF ∧ n ∈ γ'.generated ∧ n ∉ γ.generated ∧ γ.generated ⊆ γ'.generated ∧
      n.name ∉ taken ∧ ∃ γ₀ : CoreGenState, (CoreGenState.gen pf γ₀).1 = n := by
  unfold CoreGenState.genAvoiding at h
  have hnotTaken : n.name ∉ taken :=
    CoreGenState.genAvoiding_go_not_mem taken pf taken.size [] hwf List.nodup_nil
      (fun _ hd => absurd hd List.not_mem_nil) (Nat.le_add_right _ _) h
  generalize taken.size = fuel at h
  induction fuel generalizing γ with
  | zero =>
    simp only [CoreGenState.genAvoiding.go] at h
    obtain ⟨hwf', hmem, hfresh, hsub, hform⟩ := CoreGenState.gen_draw hwf h
    exact ⟨hwf', hmem, hfresh, hsub, hnotTaken, hform⟩
  | succ fuel ih =>
    simp only [CoreGenState.genAvoiding.go, bind, StateT.bind, pure] at h
    generalize hg : CoreGenState.gen pf γ = r at h
    obtain ⟨n1, γ1⟩ := r
    obtain ⟨hwf1, hgen, -⟩ := CoreGenState.gen_spec hwf hg
    split at h
    · obtain ⟨hwf', hmem, hnot, hsub, hnt, hform⟩ := ih hwf1 h
      refine ⟨hwf', hmem, fun hn => hnot (hgen ▸ List.mem_cons_of_mem _ hn), ?_, hnt, hform⟩
      exact fun x hx => hsub (hgen ▸ List.mem_cons_of_mem _ hx)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      obtain ⟨hwf', hmem, hfresh, hsub, hform⟩ := CoreGenState.gen_draw hwf hg
      exact ⟨hwf', hmem, hfresh, hsub, hnotTaken, hform⟩

end
end Core
