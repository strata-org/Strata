/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelineUnitChain
public import Strata.Languages.Core.PipelinePhaseProps
public import Strata.Languages.Core.ProcedureUnitProps
import all Strata.Languages.Core.PipelinePhase
import all Strata.Languages.Core.RuntimeCompositionProof
import all Strata.Languages.Core.Counterexample.BackLinkExact
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Per-level validity of the runtime pipeline

A level of the runtime pipeline is valid at its unit pair (`LinkPreservesAt`: the link,
read as a targeted link, preserves counterexample validity along the forward map sending
exactly its input unit to the next level's input unit).  This file gives the per-level
sufficient conditions and the end-to-end statement built from them.

Key theorems:

* `composeRuntimeBackLinks_sound_levels` — if every level is valid at its unit pair
  (`LevelsOK`), a producer outcome valid at the final unit composes to an outcome valid at
  the first level's unit;
* `linkPreservesAt_of_any` — a link valid for any forward map is valid at every pair;
* `linkPreservesAt_of_map` — a link valid along a phase's own unit map `U` is valid at a
  pair related by `U`;
* `unitStep_eq_some` — the forward map `unitStep a b` relates only `a` to `b`. -/

namespace Core

open Imperative

public section

/-! ## Units of a program -/

/-- In a contract-free program (`Program.ContractFree`: no procedure has a precondition or
    a postcondition, as in every obligation program), the unit of a procedure is its
    structured body. -/
theorem Program.unitBodyOf_of_contractFree {p : Program} (h : p.ContractFree) (n : String) :
    p.unitBodyOf n = p.bodyOf n := by
  unfold Program.unitBodyOf Program.bodyOf
  have hdecl : ∀ d ∈ p.decls, Decl.unitNamed n d = Decl.bodyNamed n d := fun d hd => by
    rcases d with _ | _ | _ | ⟨q, a⟩ | _ <;> simp only [Decl.unitNamed, Decl.bodyNamed, beq_iff_eq]
    grind [WPObl.procPassive_emptySpec, Program.ContractFree]
  generalize p.decls = l at hdecl
  induction l <;> grind

/-! ## Validity at a unit pair -/

/-- The forward map `unitStep a b` relates only `a` to `b`. -/
theorem unitStep_eq_some {a b st st' : List Statement} (h : unitStep a b st = some st') :
    st = a ∧ st' = b := by grind [unitStep]

/-- The targeted reading of a linked carrier at the procedure name `procName` builds the
    back-link at a target `t` by instantiating its builder at `t`, `procName` and `π`, and
    maps targets by its `upstreamTarget` at `procName`. -/
theorem toTargeted_linked (π : String → Option Procedure)
    (build : Target → Option String → (String → Option Procedure) →
      BackLink Expression Command Command)
    (sourceUnit : Target → Option String → List (Stmt Expression Command))
    (upstreamTarget : Target → Option String → Target) (procName : Option String) :
    (RuntimeBackLink.linked build sourceUnit upstreamTarget).toTargeted π procName =
      { build := fun t => build t procName π, upstream := fun t => upstreamTarget t procName } :=
    (rfl)

/-- A link that, read as a targeted link at any procedure name, preserves counterexample
    validity along a forward map `T` is valid at every unit pair `T` relates
    (`LinkPreservesAt`). -/
theorem linkPreservesAt_of_map {π : String → Option Procedure} {link : RuntimeBackLink}
    {T : List Statement → Option (List Statement)} {a b : List Statement}
    (h : ∀ procName, TargetedBackLinkPreserves π T (link.toTargeted π procName))
    (hab : T a = some b) : LinkPreservesAt π link a b := by
  intro procName t st st' hst o ho
  obtain ⟨rfl, rfl⟩ := unitStep_eq_some hst
  exact h procName t st st' hab o ho

/-- A link that, read as a targeted link at any procedure name, preserves counterexample
    validity along every forward map is valid at every unit pair (`LinkPreservesAt`). -/
theorem linkPreservesAt_of_any {π : String → Option Procedure} {link : RuntimeBackLink}
    (h : ∀ T procName, TargetedBackLinkPreserves π T (link.toTargeted π procName))
    (a b : List Statement) : LinkPreservesAt π link a b := h _

/-- An unavailable phase (one that stops lifting with the empty outcome) is valid at every
    unit pair (`LinkPreservesAt`). -/
theorem linkPreservesAt_unavailable (π : String → Option Procedure) (phase : String)
    (a b : List Statement) : LinkPreservesAt π (.unavailable phase) a b :=
  toTargeted_unavailable_preserves π phase _

/-- A linked phase with the identity target map is valid at a unit pair `(a, b)`
    (`LinkPreservesAt`) as soon as each of its back-links, instantiated at a target `t` and
    a procedure name `n`, lifts every outcome valid for `t` at `b` to one valid for `t` at
    `a`. -/
theorem linkPreservesAt_linked_id (π : String → Option Procedure)
    (build : Target → Option String → (String → Option Procedure) →
      BackLink Expression Command Command)
    (sourceUnit : Target → Option String → List (Stmt Expression Command))
    {a b : List Statement} (h : ∀ n t, BackLinkPreservesT π t t (unitStep a b) (build t n π)) :
    LinkPreservesAt π (.linked build sourceUnit fun t _ => t) a b := h

/-- Recording a phase's input and output programs in its carrier
    (`RuntimeBackLink.withPrograms`) does not change its validity at a unit pair
    (`LinkPreservesAt`). -/
theorem linkPreservesAt_withPrograms (π : String → Option Procedure) (link : RuntimeBackLink)
    (input output : Program) (a b : List Statement) :
    LinkPreservesAt π (link.withPrograms input output) a b ↔ LinkPreservesAt π link a b := by
  cases link <;> exact Iff.rfl

/-! ## Monotonicity of untargeted preservation in the forward map -/

/-- An empty-unit-guarded link only needs its unguarded preservation at non-empty units:
    if every pair `T'` relates with a non-empty input is related by `T`, preservation of
    counterexample validity (`BackLinkPreserves`) by `link` along `T` gives preservation by
    `link.guardEmptyUnit` (which returns the empty outcome at the empty unit) along `T'`. -/
theorem guardEmptyUnit_preserves_of_nonempty {π : String → Option Procedure}
    {t : AssertId Expression} {T T' : List Statement → Option (List Statement)}
    {link : BackLink Expression Command Command} (h : BackLinkPreserves π t T link)
    (hT : ∀ st st', T' st = some st' → st ≠ [] → T st = some st') :
    BackLinkPreserves π t T' link.guardEmptyUnit := fun st st' hT' o ho => by
  simp only [BackLink.guardEmptyUnit]
  split
  · exact validOutcome_empty ..
  · exact h _ _ (hT _ _ hT' (by grind)) _ ho

/-! ## The chain of levels -/

/-- The forward chain `levelChain` built through `units` has the given units as its
    per-link input units. -/
private theorem levelChain_inputUnits (π : String → Option Procedure) (last : List Statement)
    (target : Target) (procName0 : Option String) :
    ∀ (links : List RuntimeBackLink) (units : List (List Statement))
      (h : LevelsOK π last links units),
      (levelChain π last target procName0 links units h).inputUnits = units
  | [], [], _ => rfl
  | _ :: ls, _ :: us, h => by
    simp! [ForwardChainT.inputUnits, levelChain_inputUnits π _ target procName0 ls us h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [LevelsOK] at h

/-- **End-to-end soundness from per-level validity.**  If every runtime link is valid at
    its unit pair (`LevelsOK`) — its input unit as the runtime fold computes it
    (`runtimeUnits`), and the next level's input unit (the producer's unit `st'` after the
    last level) — then a producer outcome valid at `st'` (`ValidOutcomeOf (genuineFeasibleT π)`:
    each counterexample it claims for the target is a genuine, feasible one at that unit)
    composes to an outcome valid at the first level's unit, for the target as rewritten
    along the pipeline. -/
theorem composeRuntimeBackLinks_sound_levels (π : String → Option Procedure)
    (links : List RuntimeBackLink) (target : Target) (procName0 : Option String)
    (st' : List Statement)
    (h : LevelsOK π st' links (runtimeUnits target procName0 links))
    (producer : BackLinkOutcome Expression Command)
    (hproducer : ValidOutcomeOf (genuineFeasibleT π) target st' producer) :
    ValidOutcomeOf (genuineFeasibleT π) (runtimeState target procName0 links).1
      ((runtimeUnits target procName0 links).headD st')
      (composeRuntimeBackLinks target π links producer procName0) :=
  composeRuntimeBackLinks_sound _ _ _ _ _ _ _ _ (levelChain_inputUnits _ _ _ _ _ _ h) _ hproducer

/-! ## Links recorded from a run of the phases -/

/-- A recorded carrier (`PhaseRecord.link`) of a linked phase that supplies no unit of
    its own (`sourceUnit` empty everywhere) is linked with the same builder and target map,
    and lifts at the unit `Program.sourceUnitFor` picks in the recorded input and output
    programs.  `RuntimeBackLink.withPrograms` keeps a non-empty supplied unit and
    recomputes the unit from the programs only where the supplied one is empty, so this
    recomputed form needs the supplied unit to be empty; every phase supplies the default
    empty unit. -/
theorem PhaseRecord.link_linked (r : PhaseRecord)
    (build : Target → Option String → (String → Option Procedure) →
      BackLink Expression Command Command)
    (sourceUnit : Target → Option String → List (Stmt Expression Command))
    (upstreamTarget : Target → Option String → Target)
    (h : r.phase.buildBackLink r.input r.output = .linked build sourceUnit upstreamTarget)
    (hsu : ∀ t below, sourceUnit t below = []) :
    r.link = .linked build (fun t below => (r.input.sourceUnitFor r.output t below).1)
      upstreamTarget := by
  simp [PhaseRecord.link, h, RuntimeBackLink.withPrograms, hsu]

end -- public section

end Core
