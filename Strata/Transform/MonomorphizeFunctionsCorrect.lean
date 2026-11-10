/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.MonomorphizeFunctions
public import Strata.Languages.Core.Analysis.DeductiveVerificationProps
public import Strata.Languages.Core
public import Strata.Languages.Core.Analysis.FragmentFactory
public import Strata.DL.Lambda.LFuncEvalSound
import all Strata.Languages.Core
import all Strata.Languages.Core.PipelinePhase
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import Strata.DL.Lambda.LTyUnifyProps
import Strata.DL.Lambda.LTyProps
import Strata.Util.ListMapProps
import Strata.Util.ListUtilsProps
import all Strata.DL.Lambda.LExprTraversal
import Strata.DL.Lambda.LExprTraversalProps
import Std.Data.HashMap.Lemmas
import all Strata.Transform.MonomorphizeFunctions
import all Strata.Util.Worklist
import all Init.Data.Queue
import all Strata.Transform.CoreTransform
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LFuncEvalSound
public import Strata.DL.Lambda.LExprRenameOps
public import Strata.Transform.MonomorphizeBasics
public import Strata.Transform.MonomorphizeWorklist
public import Strata.Transform.MonomorphizeInstances
import all Strata.DL.Lambda.LExprRenameOps
import all Strata.Transform.MonomorphizeBasics
import all Strata.Transform.MonomorphizeWorklist
import all Strata.Transform.MonomorphizeInstances

/-! # `MonomorphizeFunctions` reflects lemma entries

`MonomorphizeFunctions` renames every reference to a polymorphic function `f` at a ground
instantiation `τs` to `$__mono#f#τs`, adds a copy of `f` at `τs` under that name, and drops
the polymorphic originals. A model of the old runtime factory gives a model of the new one
that reads every renamed operator `$__mono#f#…` as `f` (`demangleName`): the copy of `f` at
`τs` is `f`'s definition at that instance, so it is consistent with `f`'s interpretation at
the instance's sort.

## Key results

- `Core.MonomorphizeFunctions.monomorphizeFunctions_reflectsLemmas` — the phase carries
  every lemma entry to one with the same name and metadata and the same value, under
  `MonoPre`
- `Core.MonomorphizeFunctions.monomorphizeFunctions_overapproximates` — the same, as the
  shared contract over every entry (`PhaseOverapproximatesFrom`)
- `Core.MonomorphizeFunctions.monomorphizeFunctions_noProcedures` — its output declares no
  procedure when its input declares none
- `Lambda.LExpr.denoteEval_renameOps` — renaming operators keeps an expression's value under
  the model that reads each new name as the old one

Correctness is stated with the shared predicate `PhaseReflectsLemmas`
(`Strata/Languages/Core/Analysis/DeductiveVerification.lean`), the spec for transformations of
lemma programs; procedure bodies are outside it.
-/

namespace Core.MonomorphizeFunctions

open Lambda Core.NameMangling Strata.PtrCache

/-! ## The phase reflects lemma entries -/

section Main

open Core.Specification.Analysis

/-- The model of a factory of instances, as a runtime factory. -/
noncomputable def instModel (M : ModeledFactory CoreLParams) {F' : Lambda.Factory CoreLParams}
    (hrel : ∀ n (hn : n ∈ F'), ∃ o, ∃ ho : o ∈ M.factory, FnInstance (M.factory[o]'ho) (F'[n]'hn))
    (hnat : ConcreteEvalsCommuteDemangle M.factory)
    (hconstr : ∀ f' ∈ F'.toArray, f'.isConstr = true →
      f' ∈ M.factory.toArray ∧ demangleName f'.name.name = f'.name.name) :
    ModeledFactory CoreLParams :=
  ⟨F', Interp.ofInstances M.model hrel hnat hconstr, M.tyVarVal⟩

/-- Renaming the operators of an expression without `#` keeps its value from the old model to
    the model of instances. -/
private theorem eval_instModel {g : CoreIdent → Option LMonoTy → CoreIdent} (hg : RenOK g)
    (M : ModeledFactory CoreLParams) {F' : Lambda.Factory CoreLParams} {hrel hnat hconstr}
    (σ : ValStore CoreLParams) {e : Expression.Expr} (he : OpsUnmangled e) :
    (e.renameOps g).denoteEval (instModel M (F' := F') hrel hnat hconstr) σ = e.denoteEval M σ := by
  refine LExpr.denoteEval_renameOps (M := M) (M' := instModel M hrel hnat hconstr) g σ e
    rfl HEq.rfl rfl ?_
  intro q hq
  show HEq (M.model.opInterp (demangleName (g q.1 (some q.2)).name)) _
  rw [hg _ _ (he _ (mem_getOps_of_opAnnots hq))]

/-- The disequality of two expressions whose operators have no `#` has no operator with `#`. -/
private theorem opsUnmangled_distinctPairExpr {a b : Expression.Expr} (ha : OpsUnmangled a)
    (hb : OpsUnmangled b) : OpsUnmangled (distinctPairExpr a b) := by
  intro o ho
  simp only [distinctPairExpr, LExpr.getOps, LExpr.boolConst, List.append_nil,
    List.mem_append] at ho
  rcases ho with ho | ho
  · exact ha o ho
  · exact hb o ho

/-- **`monomorphizeFunctions` reflects the declarations entry** from every state and program
    `MonoPre` admits: the model of the output's runtime factory reads each copy as the
    original at its instance, every lemma keeps its position among the lemmas, and every
    axiom, `distinct` declaration and lemma has the value it had. -/
public theorem monomorphizeFunctions_reflectsLemmas :
    PhaseReflectsLemmas MonoPre Strata.Core.passMonomorphizeFunctions := by
  intro s p s' p' hpre hrun ρ hentry
  have hnp : ∀ d ∈ p.decls, d.kind ≠ .proc := hpre.noProcs
  obtain ⟨hnu, st, hinv, hdecls, hfac⟩ := run_ok hnp (passMono_runs hrun)
  obtain ⟨hfac0, hstore⟩ := hentry
  have hg : RenOK (monoRen (collectPolymorphicFuncDecls p s.factory) s.factory) :=
    monoRen_ok _ _
  generalize monoRen (collectPolymorphicFuncDecls p s.factory) s.factory = g at hg hinv hdecls hfac
  generalize collectPolymorphicFuncDecls p s.factory = P at hfac
  have hops : ∀ d ∈ p.decls, ∀ e ∈ d.ownExprs, OpsUnmangled e :=
    fun d hd e he => opsUnmangled_of_namesUnmangled hnu hd he
  have htakeN : p.decls.take p.decls.length = p.decls := List.take_length
  have hzlen : (p.decls.map (topDecl g)).zipIdx.take p.decls.length =
      (p.decls.map (topDecl g)).zipIdx := List.take_of_length_le (by simp)
  have hdist : ((contributed s.factory p.decls).map (·.name.name)).Nodup := hpre.distinct
  obtain ⟨store, ⟨F, M, tv⟩⟩ := ρ
  dsimp only at hfac0 hstore ⊢
  subst hfac0
  have hsrc : ∀ f', f' ∈ (runtimeFactoryOf s'.factory p'.decls).toArray →
      ∃ lf ∈ contributed s.factory p.decls, FnInstance lf f' ∧ (f'.isConstr = true → f' = lf) := by
    intro f' h
    have hc := mem_contributed_of_runtimeFactoryOf h
    rw [hfac, hdecls, ← hzlen] at hc
    have := newFn_source hpre hg hinv p.decls.length hc
    rwa [htakeN] at this
  have hrel : ∀ n (hn : n ∈ runtimeFactoryOf s'.factory p'.decls),
      ∃ o, ∃ ho : o ∈ runtimeFactoryOf s.factory p.decls,
        FnInstance ((runtimeFactoryOf s.factory p.decls)[o]'ho) (_[n]'hn) := by
    intro n hn
    obtain ⟨lf, hlf, hinst, -⟩ := hsrc _ (getElem_mem_toArray _ n hn)
    have hget := getElem?_runtimeFactoryOf_of_contributed hdist hlf
    exact ⟨lf.name.name, Lambda.Factory.getElem?_some_implies_mem hget, by
      rw [Lambda.Factory.getElem?_some_getElem hget]; exact hinst⟩
  have hnat : ConcreteEvalsCommuteDemangle (runtimeFactoryOf s.factory p.decls) := by
    intro o ho c hc
    exact hpre.evals _ (mem_contributed_of_runtimeFactoryOf (getElem_mem_toArray _ o ho)) c hc
  have hconstr : ∀ f' ∈ (runtimeFactoryOf s'.factory p'.decls).toArray, f'.isConstr = true →
      f' ∈ (runtimeFactoryOf s.factory p.decls).toArray ∧
        demangleName f'.name.name = f'.name.name := by
    intro f' hf' hc
    obtain ⟨lf, hlf, -, heq⟩ := hsrc f' hf'
    rw [heq hc]
    exact ⟨Lambda.Factory.getElem?_is_some_implies_mem
        (getElem?_runtimeFactoryOf_of_contributed hdist hlf),
      demangleName_of_not_hash (hpre.unmangled lf hlf).1⟩
  let M₀ : ModeledFactory CoreLParams := ⟨runtimeFactoryOf s.factory p.decls, M, tv⟩
  have hev : ∀ e, OpsUnmangled e → ∀ σ,
      (e.renameOps g).denoteEval (instModel M₀ hrel hnat hconstr) σ = e.denoteEval M₀ σ :=
    fun e he σ => eval_instModel hg M₀ σ he
  refine ⟨⟨store, instModel M₀ hrel hnat hconstr⟩, ⟨rfl, hstore⟩, ?_⟩
  intro i l md hl hval hfacts
  have hlops : OpsUnmangled l.e :=
    hops _ (List.mem_of_getElem? hl) l.e (by simp [Decl.ownExprs])
  have hLi : ((p.decls.map (topDecl g)).zipIdx)[i]? =
      some (.lemma { l with e := l.e.renameOps g } md, i) := by
    simp [List.getElem?_zipIdx, hl, topDecl]
  obtain ⟨hidx, htake⟩ := flatMap_index _ (updDecl g (specsByFnOf st.specializedFnsInProg)) hLi
    (b := .lemma { l with e := l.e.renameOps g } md) (by simp [updDecl])
  rw [← hdecls] at hidx htake
  refine ⟨_, { l with e := l.e.renameOps g }, hidx, rfl, ?_, ?_, ?_⟩
  · show ((l.e.renameOps g).denoteEval _ store).isSome
    rw [hev _ hlops]; exact hval
  · rw [htake]
    intro d hd c hc
    obtain ⟨⟨dT, j⟩, hx, hdx⟩ := List.mem_flatMap.mp hd
    obtain ⟨hj, hdT⟩ := mem_take_zipIdx hx
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hdT
    obtain ⟨d0, hd0, rfl⟩ := hdT
    have hd0m : d0 ∈ p.decls := List.mem_of_getElem? hd0
    have hf0 := hfacts d0 (mem_take_of_getElem? hj hd0)
    cases d0 with
    | ax a md' =>
      simp only [topDecl, updDecl, List.mem_singleton] at hdx
      subst hdx
      simp only [declAssumes, List.mem_singleton] at hc
      subst hc
      have h0 := hf0 (declArg ⟨store, M₀⟩ a.name a.e md')
        (by simp only [declAssumes, List.mem_singleton]; rfl)
      simp only [declArg] at h0 ⊢
      change (a.e.renameOps g).denoteEval _ store = _
      rw [hev _ (hops _ hd0m a.e (by simp [Decl.ownExprs]))]
      exact h0
    | distinct n es md' =>
      simp only [topDecl, updDecl, List.mem_singleton] at hdx
      subst hdx
      simp only [declAssumes, List.orderedPairs_map, List.map_map, List.mem_map] at hc
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := hc
      obtain ⟨ha, hb⟩ := List.mem_orderedPairs hab
      have h0 := hf0 (declArg ⟨store, M₀⟩ (toString n) (distinctPairExpr a b) md')
        (by simp only [declAssumes, List.mem_map]; exact ⟨(a, b), hab, rfl⟩)
      simp only [declArg, Function.comp_apply] at h0 ⊢
      change ((distinctPairExpr a b).renameOps g).denoteEval _ store = _
      rw [hev _ (opsUnmangled_distinctPairExpr
        (hops _ hd0m a (by simpa [Decl.ownExprs] using ha))
        (hops _ hd0m b (by simpa [Decl.ownExprs] using hb)))]
      exact h0
    | func f md' =>
      simp only [topDecl, updDecl] at hdx
      split at hdx
      · simp only [List.mem_singleton] at hdx; subst hdx; simp [declAssumes] at hc
      · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hdx; simp [declAssumes] at hc
    | recFuncBlock fs md' =>
      simp only [topDecl, updDecl] at hdx
      split at hdx
      · simp at hdx
      · simp only [List.mem_singleton] at hdx; subst hdx; simp [declAssumes] at hc
    | _ =>
      simp only [topDecl, updDecl, List.mem_singleton] at hdx
      subst hdx; simp [declAssumes] at hc
  · intro h
    simp only [lemmaEvent, declArg] at h ⊢
    change (l.e.renameOps g).denoteEval _ store = _ at h
    rw [hev _ hlops] at h
    exact h

/-- **`monomorphizeFunctions` overapproximates every entry** (`PhaseOverapproximatesFrom`,
    the shared contract over every entry) on the programs `MonoPre` admits, which have no
    procedures. -/
public theorem monomorphizeFunctions_overapproximates :
    PhaseOverapproximatesFrom (fun s p => MonoPre s p ∧ NoProcedures p)
      Strata.Core.passMonomorphizeFunctions :=
  monomorphizeFunctions_reflectsLemmas.overapproximates

/-- **`monomorphizeFunctions` keeps programs free of procedures.** -/
public theorem monomorphizeFunctions_noProcedures {s s' : Transform.CoreTransformState}
    {p p' : Program} (hnp : NoProcedures p)
    (hrun : Strata.Core.passMonomorphizeFunctions.Runs s p s' p') : NoProcedures p' := by
  obtain ⟨-, st, -, hdecls, -⟩ := run_ok hnp (passMono_runs hrun)
  intro d hd
  rw [hdecls] at hd
  obtain ⟨⟨dT, j⟩, hx, hdx⟩ := List.mem_flatMap.mp hd
  have hxm := List.mem_zipIdx_iff_getElem?.mp hx
  simp only [List.getElem?_map, Option.map_eq_some_iff] at hxm
  obtain ⟨d0, hd0, rfl⟩ := hxm
  have hk := hnp d0 (List.mem_of_getElem? hd0)
  cases d0 with
  | proc => exact absurd rfl hk
  | func f md =>
    simp only [topDecl, updDecl] at hdx
    split at hdx
    · simp only [List.mem_singleton] at hdx; subst hdx; simp [Decl.kind]
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hdx; simp [Decl.kind]
  | recFuncBlock fs md =>
    simp only [topDecl, updDecl] at hdx
    split at hdx
    · simp at hdx
    · simp only [List.mem_singleton] at hdx; subst hdx; simp [Decl.kind]
  | _ =>
    simp only [topDecl, updDecl, List.mem_singleton] at hdx
    subst hdx; simp [Decl.kind]

end Main

end Core.MonomorphizeFunctions
