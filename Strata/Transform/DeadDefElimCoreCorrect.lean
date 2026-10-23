/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DeadDefElimCorrect
public import Strata.Transform.DeadDefElimProps
public import Strata.Languages.Core.Logic.LangDef
public import Strata.Transform.SpecificationProps
import all Strata.Transform.DeadDefElim
import all Strata.Languages.Core.PipelinePhase

/-! # The dead-definition phase over-approximates

For Core: a successful run of the transform `deadDefElimProgram` keeps every failure of each
obligation procedure (`deadDefElimProgram_over`).  The pipeline framework states no semantic
obligation per phase (a phase's contract is the facts it requires, establishes and preserves),
so the property is also stated for the runs of `deadDefElimPipelinePhase`, which are the runs of
`deadDefElimProgram` (`deadDefElimPipelinePhase_ok`): every failure of a loop-free procedure
body of its input is a failure of the body of the same procedure in its output
(`deadDefElimPipelinePhase_over`).

Over Core's event language for statement lists (`EventLang.coreBlock`), erasing unread
`init`s (`deadDefElim []`) from a list without loops (`Block.noLoops`) and procedure calls
(`Statements.noCalls`) is a trace over-approximation in the general form
`OverapproximatesTracesUptoWhen` (`deadDefElim_overapproximatesTraces`): the initial
environments are equal; a source trace and its target trace correspond event by event
(`List.Rel₂ DDEventRel`: same kind, factory, label, condition and metadata, the target store
being the source store with some bindings removed and agreeing with it on the condition's free
variables); final environments correspond by `DDOut`; and the output satisfies the initial-
environment gate `BlockInitEnvWF` wherever the input does.  Consequently assertion validity on
the traces of the output, under a store-local interpretation such as evaluation to `true`, is
validity on the traces of the input (`deadDefElim_assertValid`).

The proof runs a Core trace of the call-free list as a trace over `EvalE` (`star_evalE`), turns
it into a big-step reach or run (`star_breach_noLoops`, `star_brun_noLoops`), replays it on the
output (`deadDefElim_reach_rel`, `deadDefElim_run_rel`) and turns the replay back into a Core
trace (`breach_star`, `brun_star`, `star_core`).

The executable pass `deadDefElimH`, which the phase runs, has the same two properties
(`deadDefElimH_overapproximatesTraces`, `deadDefElimH_assertValid`), through `deadDefElimH_eq`.

Key theorems: `deadDefElimProgram_over`, `deadDefElimPipelinePhase_ok`,
`deadDefElimPipelinePhase_over`, `deadDefElim_overapproximatesTraces`, `deadDefElim_assertValid`,
`deadDefElimH_overapproximatesTraces`, `deadDefElimH_assertValid`. -/

namespace Core
namespace DeadDefElim

open Imperative Imperative.BigStep Imperative.DeadDefElim Imperative.Specification
  Imperative.Specification.Transform Core.Logic Strata.Logic

public section

/-- **The dead-definition transform over-approximates.**  Let a run of `deadDefElimProgram` on
    the program `prog` succeed with `out`, and let `q` be a procedure of `prog` with structured
    body `ss`.  Then `out` contains the procedure with body `deadDefElimH [] ss`, and, if `ss`
    has no loops and fails the target `t` from the value-valued store `σ` under the reference
    event semantics, so does that body, from `σ`, for every factory evaluating alike on
    well-formed stores agreeing on the free variables (`WellFormedSemanticEvalExprCongr`) and
    evaluating Boolean guards to Booleans. -/
theorem deadDefElimProgram_over {prog out : Program} {s s' : Transform.CoreTransformState}
    {b : Bool} (h : (deadDefElimProgram prog).run s = (.ok (b, out), s')) {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    (hb : q.body = .structured ss) :
    Decl.proc { q with body := .structured (deadDefElimH [] ss) } md ∈ out.decls ∧
      ∀ {F : Expression.Factory}, WellFormedSemanticEvalExprCongr (P := Expression) F →
        WellFormedSemanticEvalBool (P := Expression) F → Block.noLoops ss = true →
        ∀ {σ : SemanticStore Expression}, WellFormedStore σ F →
        ∀ {t : AssertId Expression} {hf : Bool},
        FailsE F hf ss σ t → ∀ hf' : Bool, FailsE F hf' (deadDefElimH [] ss) σ t := by
  cases h
  refine ⟨?_, fun hF hWB hss _ hC _ _ h hf' => deadDefElimH_failsE hF hWB _ hss hC h hf'⟩
  simp only [List.map_map, List.mem_map]
  exact ⟨_, hq, by simp [deadDefElimDecl, hb]⟩

/-- A run of `deadDefElimPipelinePhase` on `program` is a run of `deadDefElimProgram`. -/
theorem deadDefElimPipelinePhase_ok (program : Program) (s : Transform.CoreTransformState) :
    (deadDefElimPipelinePhase.transform program).run s = (deadDefElimProgram program).run s :=
  (rfl)

/-- **The dead-definition phase over-approximates.**  Let a run of `deadDefElimPipelinePhase`
    on `program` succeed with `out`, and let `q` be a procedure of `program` with structured
    body `ss`.  Then `out` contains the procedure with body `deadDefElimH [] ss`, and, if `ss`
    has no loops and fails the target `t` from the value-valued store `σ` under the reference event
    semantics, so does that body, from `σ`, for every factory evaluating alike on well-formed
    stores agreeing on the free variables (`WellFormedSemanticEvalExprCongr`) and evaluating
    Boolean guards to Booleans. -/
theorem deadDefElimPipelinePhase_over {program out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (deadDefElimPipelinePhase.transform program).run s = (.ok (b, out), s'))
    {q : Procedure} {md : Imperative.MetaData Expression} {ss : Statements}
    (hq : Decl.proc q md ∈ program.decls) (hb : q.body = .structured ss) :
    Decl.proc { q with body := .structured (deadDefElimH [] ss) } md ∈ out.decls ∧
      ∀ {F : Expression.Factory}, WellFormedSemanticEvalExprCongr (P := Expression) F →
        WellFormedSemanticEvalBool (P := Expression) F → Block.noLoops ss = true →
        ∀ {σ : SemanticStore Expression}, WellFormedStore σ F →
        ∀ {t : AssertId Expression} {hf : Bool},
        FailsE F hf ss σ t → ∀ hf' : Bool, FailsE F hf' (deadDefElimH [] ss) σ t :=
  deadDefElimProgram_over (deadDefElimPipelinePhase_ok program s ▸ h) hq hb

/-! ## The trace over-approximation -/

/-- **Erasing unread definitions over-approximates the traces of a Core statement list.**
    For a Core statement list `ss` without loops (`Block.noLoops`) and procedure calls (`noCalls`),
    and every initial environment `ρ₀` satisfying `BlockInitEnvWF params ss`:
    * every finite trace of `ss` from `ρ₀` corresponds event by event (`DDEventRel`) to a
      trace of `deadDefElim [] ss` from `ρ₀`;
    * every terminating or exiting run of `ss` from `ρ₀` has a run of `deadDefElim [] ss` from
      `ρ₀` ending in the same way, with corresponding events and a final environment
      corresponding to the source's (`DDOut`);
    * `deadDefElim [] ss` satisfies `BlockInitEnvWF params` at `ρ₀`. -/
theorem deadDefElim_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen (List.Rel₂ DDEventRel) (· = ·) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (deadDefElim [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true) params params := by
  intro ss st' hT ⟨hss, hnc⟩ ρ₀ _ rfl hwf
  cases hT
  obtain ⟨σ₀, F, hf⟩ := ρ₀
  have hC : WellFormedStore σ₀ F := hwf.storeWellDefined
  have hcong := hwf.exprCongr
  have hWB := hwf.bool
  refine ⟨fun cfg trace h => ?_, fun ρ' trace h => ?_, fun l ρ' trace h => ?_,
    blockInitEnvWF_dd hss hnc hwf⟩
  · have h' := star_evalE h hnc
    by_cases htr : trace = []
    · subst htr
      exact ⟨_, [], .refl _, .nil⟩
    obtain ⟨evs', hb, hm⟩ := deadDefElim_reach_rel hcong []
      (star_breach_noLoops hss h' htr) htr hC
    obtain ⟨cfg', hc⟩ := breach_star hWB hb hf
    exact ⟨cfg', evs', star_core π hc, hm⟩
  · have h' := star_evalE h hnc
    have hE := star_getEnv h'
    obtain ⟨evs', o', hb, hm, hO⟩ :=
      deadDefElim_run_rel hcong [] ((star_brun_noLoops hss).1 h') hC
    rcases o' with σ' | _ <;> simp only [DDOutcomeRel] at hO
    exact ⟨_, evs', star_core π (brun_star hWB hb hf), ⟨hE.1.symm, hE.2.symm, hO⟩, hm⟩
  · have h' := star_evalE h hnc
    have hE := star_getEnv h'
    obtain ⟨evs', o', hb, hm, hO⟩ :=
      deadDefElim_run_rel hcong [] ((star_brun_noLoops hss).2 h') hC
    rcases o' with _ | ⟨l', σ'⟩ <;> simp only [DDOutcomeRel] at hO
    obtain ⟨rfl, hO⟩ := hO
    exact ⟨_, evs', star_core π (brun_star hWB hb hf), ⟨hE.1.symm, hE.2.symm, hO⟩, hm⟩

/-- **Assertion validity transported back through erasure.**  For a store-local
    interpretation `I` (`StoreLocal`, such as evaluation to `true`: `evalInterp_storeLocal`)
    and a Core statement list `ss` without loops and procedure calls: if every occurrence of
    the assertion `aid` holds under its preceding assumptions on every trace of
    `deadDefElim [] ss` from every environment satisfying `BlockInitEnvWF params` of that list,
    the same holds for `ss` from every environment satisfying `BlockInitEnvWF params ss`. -/
theorem deadDefElim_assertValid (π : String → Option Procedure) (params : InitEnvWFParams)
    {I : ConditionInterp Expression} (hI : StoreLocal I) {ss : Statements}
    (hss : Block.noLoops ss = true) (hnc : Statements.noCalls ss = true) {aid : AssertId Expression}
    (h : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF params (deadDefElim [] ss)) (deadDefElim [] ss) aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF params ss) ss aid :=
  overapproximatesTracesUptoWhen_assertValid I _ DDOut (EventLang.coreBlock π)
    (EventLang.coreBlock π) (fun ss => some (deadDefElim [] ss))
    (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true) params params
    (dd_assertValid_reflect hI) (deadDefElim_overapproximatesTraces π params) rfl ⟨hss, hnc⟩ h

/-- **The executable pass over-approximates traces**: `deadDefElim_overapproximatesTraces` for
    `deadDefElimH`, the pass the phase runs. -/
theorem deadDefElimH_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) :
    OverapproximatesTracesUptoWhen (List.Rel₂ DDEventRel) (· = ·) DDOut
      (EventLang.coreBlock π) (EventLang.coreBlock π) (fun ss => some (deadDefElimH [] ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true) params params := by
  simp only [deadDefElimH_eq]
  exact deadDefElim_overapproximatesTraces π params

/-- **Assertion validity transported back through the executable pass**:
    `deadDefElim_assertValid` for `deadDefElimH`. -/
theorem deadDefElimH_assertValid (π : String → Option Procedure) (params : InitEnvWFParams)
    {I : ConditionInterp Expression} (hI : StoreLocal I) {ss : Statements}
    (hss : Block.noLoops ss = true) (hnc : Statements.noCalls ss = true) {aid : AssertId Expression}
    (h : AssertValidOnTracesWhen (EventLang.coreBlock π) I
      (BlockInitEnvWF params (deadDefElimH [] ss)) (deadDefElimH [] ss) aid) :
    AssertValidOnTracesWhen (EventLang.coreBlock π) I (BlockInitEnvWF params ss) ss aid :=
  deadDefElim_assertValid π params hI hss hnc (deadDefElimH_eq [] ss ▸ h)

end -- public section

end DeadDefElim

end Core
