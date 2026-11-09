/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.SSA.SSACoreProgramProps
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.Specification
public import Strata.Languages.Core.Verifier
public import Strata.Transform.DeadDefElimCoreCorrect
import all Strata.Transform.SSA.SSACoreProgramProps
import Strata.DL.Imperative.BigStep.Adequacy
import Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.Verifier
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform
import Strata.Languages.Core.InstExprTyping

/-! # The SSA phase over-approximates the traces of a guarded statement list

Over Core's event language for statement lists (`EventLang.coreBlock`), the SSA phase
(`ssaEntry`) on a guarded statement list `ss₀` is a trace over-approximation in the general form
`OverapproximatesTracesUptoWhen` (`ssa_overapproximatesTraces`):

* the initial environments are related by the entry renaming of `ss₀` (`SSAEntryRel`): the
  target store holds, under the entry name of each free variable of `ss₀`, the source value of
  that variable, and binds nothing else; and the type annotations of the output agree with a
  typing of the target store;
* a source trace and its target trace correspond event by event under evaluation to `true`
  (`Trace.WeakensAssumes evalInterp`): each assertion and cover keeps its label and metadata and
  holds exactly when the source's does; each assumption is kept, with its label and metadata and
  holding whenever the source's holds, or dropped;
* final environments have the same factory;
* the output satisfies the initial-environment gate `BlockInitEnvWF` wherever the input does and
  the environments are related.

The precondition asks that the list be in tree form (`Block.treeForm`), that every arm of every
`ite *` contain an assertion or a cover (`Block.armsHaveChecks`: the phase then drops no arm, so
a run of the taken arm is replayed without running the other arm's definitions), and that every
free variable be a parameter or an alias.  The reserved prefixes of the gate contain no `@`
(`hp`), the character of every name the phase introduces.

The entry renaming depends on the statement list (its fresh names avoid the identifiers of the
list), while the framework fixes the input relation before the statement list; the statement is
therefore one per statement list `ss₀`, with the precondition `· = ss₀`.

The executable pass the phase runs on a procedure `q` is `ssaLoopFree G q`, which is `ssaEntry`
with the parameter types, the parameters and the `old` aliases of `q`
(`ssaLoopFree_overapproximatesTraces`).  A successful run of the pipeline phase
`ssaPipelinePhase` runs the SSA phase of the program (`ssaPipelinePhase_ok`).

TODO: state the soundness of `ssaPipelinePhase` as `OverapproximatesTracesUptoWhen` on each
procedure body it rewrites.

Key theorems: `ssa_overapproximatesTraces`, `ssaLoopFree_overapproximatesTraces`,
`ssaPipelinePhase_ok`.

Key definitions: `ssaEntryRenOf`, `SSAEntryRel`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.Specification.Transform Core.Logic
  Strata.Logic Imperative.DeadDefElim Core.DeadDefElim

public section

/-! ## The entry relation -/

/-- The entry renaming the SSA phase computes for the statement list `ss` (`ssaEntry`, from
    `ssaEntryRen`): each parameter of `xs` to its entry name, each alias of `al` to the entry
    name of the parameter it denotes. -/
@[expose] def ssaEntryRenOf (G : IdSet Expression) (tys : Tys Expression)
    (xs : List Expression.Ident) (al : List (Expression.Ident × Expression.Ident))
    (ss : Statements) : Ren Expression :=
  (ssaEntryRen (inputAvoid G tys ss) xs al 0).1

/-- The initial environment `ρ'` of the SSA output of `ss₀` corresponds to the initial
    environment `ρ` of `ss₀`.  The entry renaming is `ρ0 = ssaEntryRenOf G tys xs al ss₀`. -/
structure SSAEntryRel (G : IdSet Expression) (tys : Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (ss₀ : Statements)
    (ρ ρ' : Imperative.Env Expression) : Prop where
  /-- The two environments have the same factory. -/
  factory : ρ'.factory = ρ.factory
  /-- Every free variable `x` of `ss₀` is defined in the source store, with the value the
      target store gives the entry name `ρ0.get x`. -/
  entry : ∀ x ∈ Block.freeVars ss₀,
    ρ.store x = ρ'.store ((ssaEntryRenOf G tys xs al ss₀).get x) ∧ (ρ.store x).isSome
  /-- Every parameter is defined in the source store. -/
  params : ∀ x ∈ xs, (ρ.store x).isSome
  /-- Every free variable of `ss₀` has its type of `tys` in the source store. -/
  tyOK : TyOK ρ.factory tys (Block.freeVars ss₀) (Block.freeVars ss₀) ρ.store
  /-- The target store binds only the entry names of the free variables of `ss₀`. -/
  dom : ∀ y, (ρ'.store y).isSome →
    ∃ x ∈ Block.freeVars ss₀, y = (ssaEntryRenOf G tys xs al ss₀).get x

/-- The typing of the entry names: an entry name has the type `tys` records for a free variable
    of `ss` the entry renaming `ren` renames to it. -/
private def entryTyping (ren : Ren Expression) (tys : Tys Expression) (ss : Statements) :
    VarTyping Expression := fun y =>
  ((Block.freeVars ss).find? fun x => ren.get x == y && (tys.get? x).isSome).bind tys.get?

/-- **The SSA output agrees with a typing of the target store.**  Let the source and target
    environments be related by the entry renaming of `ssaEntry` (`hrel`: the target store holds
    the source values of the free variables of `ss₀` under their entry names, with the types
    `tys` records), let every alias rename to a parameter (`hal`), and let every free variable
    of `ss₀` be a parameter or an alias (`hfv`).  If `ssaEntry` succeeds, there is a typing that
    the target store conforms to and that the annotations of its output agree with: the typing
    giving each entry name the type `tys` records for the free variable renamed to it. -/
private theorem ssa_outAnnotated {G : IdSet Expression} {tys : Tys Expression}
    {xs : List Expression.Ident} {al : List (Expression.Ident × Expression.Ident)}
    {ss₀ : Statements} {ρ ρ' : Imperative.Env Expression}
    (hrel : SSAEntryRel G tys xs al ss₀ ρ ρ') (hal : ∀ q ∈ al, q.2 ∈ xs)
    (hfv : ∀ x ∈ Block.freeVars ss₀, x ∈ xs ∨ x ∈ al.map (·.1)) {ρ0 : Ren Expression}
    {so : SOut Expression} (hss : ssaEntry G tys xs al ss₀ = .ok (ρ0, so)) :
    ∃ Γ, StoreHasTyping ρ'.factory ρ'.store Γ ∧ Block.fvarTypesWellAnnotated Γ so.out := by
  obtain ⟨rfl, -⟩ := ssaEntry_ok hss
  have hfind : ∀ y T, entryTyping (ssaEntryRenOf G tys xs al ss₀) tys ss₀ y = some T →
      ∃ x ∈ Block.freeVars ss₀, (ssaEntryRenOf G tys xs al ss₀).get x = y ∧
        tys.get? x = some T := by
    intro y T h
    cases hf : (Block.freeVars ss₀).find?
        (fun x => (ssaEntryRenOf G tys xs al ss₀).get x == y && (tys.get? x).isSome) with
    | none => simp [entryTyping, hf] at h
    | some x =>
      simp only [entryTyping, hf, Option.bind_some] at h
      have hx := List.find?_some hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hx
      exact ⟨x, List.mem_of_find?_eq_some hf, hx.1, h⟩
  -- The value at an entry name has the type `tys` records for each free variable renamed to it.
  have hval : ∀ x ∈ Block.freeVars ss₀, ∀ T, tys.get? x = some T →
      ∃ v, ρ'.store ((ssaEntryRenOf G tys xs al ss₀).get x) = some v ∧
        HasVal.valueOfTy ρ'.factory v T := fun x hx T hT => by
    obtain ⟨he, hs⟩ := hrel.entry x hx
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨v, he ▸ hv, hrel.factory ▸ hrel.tyOK x hx hx T hT v hv⟩
  refine ⟨entryTyping (ssaEntryRenOf G tys xs al ss₀) tys ss₀, fun y T hy => ?_,
    ssaEntry_fvarTypesWellAnnotated hss hal hfv (fun x hx T hT => ?_) fun y hy => ?_⟩
  · obtain ⟨x, hx, rfl, hT⟩ := hfind y T hy
    exact hval x hx T hT
  · have hsome : ((Block.freeVars ss₀).find? fun z =>
        (ssaEntryRenOf G tys xs al ss₀).get z == (ssaEntryRenOf G tys xs al ss₀).get x &&
          (tys.get? z).isSome).isSome :=
      List.find?_isSome.2 ⟨x, hx, by simp [hT]⟩
    obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hsome
    have hzp := List.find?_some hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hzp
    obtain ⟨U, hU⟩ := Option.isSome_iff_exists.1 hzp.2
    obtain ⟨v, hv, hvT⟩ := hval x hx T hT
    obtain ⟨w, hw, hwU⟩ := hval z (List.mem_of_find?_eq_some hz) U hU
    rw [hzp.1, hv] at hw
    cases hw
    change ((Block.freeVars ss₀).find? fun z =>
        (ssaEntryRenOf G tys xs al ss₀).get z == (ssaEntryRenOf G tys xs al ss₀).get x &&
          (tys.get? z).isSome).bind tys.get? = some T
    rw [hz, Option.bind_some, hU]
    exact congrArg some (Core.valueOfTy_unique hwU hvT)
  · obtain ⟨T, hT⟩ := Option.isSome_iff_exists.1 hy
    obtain ⟨x, hx, rfl, -⟩ := hfind y T hT
    exact ⟨x, hx, rfl⟩

/-! ## The trace over-approximation -/

/-- **The SSA phase over-approximates the traces of a guarded statement list.**  For a Core
    statement list `ss₀` in tree form, with an assertion or a cover in every arm of every `ite *`
    and its free variables among the parameters `xs` and the aliases of `al`, on which
    `ssaEntry G tys xs al` succeeds with the output `out`, every reserved prefix of `params` being free of `@`, every alias of `al`
    denoting a parameter of `xs`, and all initial environments `ρ₀` of `ss₀` and `ρ₀'` of `out`
    related by `SSAEntryRel` with `ρ₀` satisfying `BlockInitEnvWF params ss₀`:
    * every finite trace of `ss₀` from `ρ₀` has a trace of `out` from `ρ₀'` whose assumptions are
      weakened (`Trace.WeakensAssumes evalInterp`);
    * every terminating run of `ss₀` from `ρ₀` has a terminating run of `out` from `ρ₀'` with
      such a trace and the same factory (`ss₀` has no exiting run);
    * `out` satisfies `BlockInitEnvWF params` at `ρ₀'`. -/
theorem ssa_overapproximatesTraces (π : String → Option Procedure) (params : InitEnvWFParams)
    (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList) (G : IdSet Expression)
    (tys : Tys Expression) (xs : List Expression.Ident)
    (al : List (Expression.Ident × Expression.Ident)) (hal : ∀ q ∈ al, q.2 ∈ xs)
    (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp)
      (SSAEntryRel G tys xs al ss₀) (fun ρ ρ' => ρ'.factory = ρ.factory)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => (ssaEntry G tys xs al ss).toOption.map (·.2.out))
      (fun ss => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ xs ∨ x ∈ al.map (·.1)) params params := by
  intro ss out hT ⟨rfl, htf, harm, hfv⟩ ρ₀ ρ₀' hrel hwf
  obtain ⟨⟨ρ0, so⟩, hss, rfl⟩ : ∃ r, ssaEntry G tys xs al ss = .ok r ∧ r.2.out = out := by
    cases h : ssaEntry G tys xs al ss with
    | error => simp only [Except.toOption, h, Option.map] at hT; nomatch hT
    | ok r =>
      simp only [Except.toOption, h, Option.map] at hT
      cases hT
      exact ⟨r, rfl, rfl⟩
  have hgate := ssaEntry_blockInitEnvWF hp hal hss htf hfv hrel.factory hrel.entry hrel.params
    hrel.tyOK hrel.dom hwf (ssa_outAnnotated hrel hal hfv hss)
  obtain ⟨rfl, -⟩ := ssaEntry_ok hss
  obtain ⟨σ₀, F⟩ := ρ₀
  obtain ⟨σ₀', F'⟩ := ρ₀'
  obtain rfl : F = F' := hrel.factory.symm
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hWB := hwf.bool
  have hnl : Block.noLoops ss = true :=
    Block.treeForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) htf
  have hnc : Statements.noCalls ss = true :=
    Block.treeForm_allSubstmts (fun _ => rfl) (fun _ _ _ => rfl) htf
  have hsim := ssaEntry_sim hwf.var hwf.val
    (coreEvaluator_WellFormedSemanticEvalSubstLits F)
    hss hal (σL := σ₀) (σS := σ₀') hrel.entry hrel.tyOK hC
    (fun y v hy => by
      obtain ⟨x, hx, rfl⟩ := hrel.dom y (by simp [hy])
      exact hC x v ((hrel.entry x hx).1.trans hy))
    (D := (Block.freeVars ss).map (ssaEntryRenOf G tys xs al ss).get)
    (fun y hy => (hrel.dom y hy).elim fun x ⟨hx, he⟩ => he ▸ List.mem_map_of_mem hx)
    (fun y hy => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
      obtain ⟨q, hq, he⟩ := Ren.get_mem ((ssaEntryRen_spec _ xs al 0 hal).2.2 x (hfv x hx))
      exact .inl (he ▸ List.mem_map_of_mem hq))
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_, hgate⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨tr', hw, rfl | hb⟩ := hsim.1 (star_breach_noLoops hnl h' htr)
    · exact ⟨_, [], .refl _, hw⟩
    obtain ⟨cfg', hc⟩ := breach_star hWB hb
    exact ⟨cfg', tr', star_core π hc, hw⟩
  · have h' := star_evalE h hnc
    obtain ⟨σL', -, tr', σS', hb, hw⟩ := hsim.2 harm ((star_brun_noLoops hnl).1 h')
    exact ⟨_, tr', star_core π (brun_star hWB hb), starE_preserves_factory h', hw⟩
  · obtain ⟨σL', ho, -⟩ := hsim.2 harm ((star_brun_noLoops hnl).2 (star_evalE h hnc))
    cases ho

/-- **The executable pass over-approximates traces**: `ssa_overapproximatesTraces` for
    `ssaLoopFree G q`, the pass the SSA phase runs on each procedure `q` (`ssaProc`). -/
theorem ssaLoopFree_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) (hp : ∀ p ∈ params.prefixIdents, '@' ∉ p.toList)
    (G : IdSet Expression) (q : Procedure) (ss₀ : Statements) :
    OverapproximatesTracesUptoWhen (Trace.WeakensAssumes evalInterp)
      (SSAEntryRel G q.paramTys q.entryParams q.oldAliases ss₀)
      (fun ρ ρ' => ρ'.factory = ρ.factory)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => (ssaLoopFree G q ss).toOption.map (·.2.out))
      (fun ss => ss = ss₀ ∧ Block.treeForm ss = true ∧ Block.armsHaveChecks ss = true ∧
        ∀ x ∈ Block.freeVars ss, x ∈ q.entryParams ∨ x ∈ q.oldAliases.map (·.1))
      params params :=
  ssa_overapproximatesTraces π params hp G _ _ _ (Procedure.oldAliases_mem q) ss₀

/-! ## The pipeline phase -/

/-- A successful run of `ssaPipelinePhase` on `program` returns the obligation program of
    `program` for the names of the functions of the factory `moreFns` extends. -/
theorem ssaPipelinePhase_ok {m : Lambda.Factory CoreLParams}
    {program out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((ssaPipelinePhase m).transform program).run s = (.ok (b, out), s')) :
    ∃ fac, Core.Factory.addFactory m = .ok fac ∧
      ssaProgram (fac.toArray.toList.map (·.name)) program = .ok out := by
  simp only [ssaPipelinePhase, modelPreservingPipelinePhase, Transform.liftDiag] at h
  rcases hw : ssaProgramOf program m with _ | mid <;> rw [hw] at h <;> cases h
  simp only [ssaProgramOf, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hw
  repeat (split at hw <;> try cases hw)
  exact ⟨_, ‹_›, by assumption⟩

end -- public section

end WP
end Core
