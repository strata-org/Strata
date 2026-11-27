/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.Counterexample.BackLinkPhases
public import Strata.Languages.Core.Counterexample.BackLinkTarget
import Strata.Languages.Core.Counterexample.BackLinkTargetProps
import all Strata.Languages.Core.PipelinePhase
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.BackLinkProps
import all Strata.Languages.Core.Counterexample.BackLinkPhases
import all Strata.Languages.Core.Counterexample.BackLinkTarget
import Strata.DL.Imperative.Counterexample.Tactics

/-! # The runtime back-link composition is the proved composition

The runtime fold `composeRuntimeBackLinks` coincides with
`Imperative.composeTargeted`, once each runtime link is read as a `TargetedBackLink`
(`RuntimeBackLink.toTargeted`, with `.unavailable` read as the link lifting every outcome
to the empty one, each link's target map applied at the procedure name the runtime fold
holds at its output: `runtimeTargeted`) and the units are those the runtime fold threads
(`runtimeUnits`).

Key definitions: `RuntimeBackLink.toTargeted`, `runtimeState`, `runtimeTargeted`,
`runtimeUnits`.

Key theorems: `composeRuntimeBackLinks_eq_composeTargeted`, `composeRuntimeBackLinks_sound`.

The results are not in `PipelinePhaseProps.lean`: they relate `composeRuntimeBackLinks` to the
composition of back-links of `BackLinkPhases` and `BackLinkTarget`, which
`PipelinePhase.lean` and `PipelinePhaseProps.lean` do not import, and this module defines the
readings (`RuntimeBackLink.toTargeted`, `runtimeTargeted`, `runtimeUnits`) they are stated
with. -/

namespace Core

open Imperative

public section

/-- The back-link lifting every outcome to the empty outcome: the reading of a
    `RuntimeBackLink.unavailable` phase. -/
def emptyBackLink (name : String) : BackLink Expression Command Command where
  name := name
  lift := fun _ _ => .empty

/-- A runtime link as a targeted back-link at the procedure table `π`, its builder and
    target map applied at `procName` (the name of the obligation's procedure at the link's
    output). -/
def RuntimeBackLink.toTargeted (π : String → Option Procedure) (procName : Option String) :
    RuntimeBackLink → TargetedBackLink Expression Command Target
  | .linked build _ upstreamTarget =>
    { build := fun t => build t procName π, upstream := fun t => upstreamTarget t procName }
  | .unavailable phase => { build := fun _ => emptyBackLink phase, upstream := id }

/-- The target id and procedure name the runtime fold holds when it reaches the link
    just upstream of `links` (forward order), starting from `(target, procName0)` after
    the last link (`procName0`: the procedure the producer's unit belongs to, if known).
    A linked phase passes the name up unchanged when its unit is not empty, and no name
    when it is. -/
def runtimeState (target : Target) (procName0 : Option String := none) :
    List RuntimeBackLink → Target × Option String
  | [] => (target, procName0)
  | l :: ls =>
    let (tgt, procName) := runtimeState target procName0 ls
    match l with
    | .unavailable _ => (tgt, procName)
    | .linked _ sourceUnit upstreamTarget =>
      (upstreamTarget tgt procName, if (sourceUnit tgt procName).isEmpty then none else procName)

/-- The targeted readings of `links` (forward order), each at the procedure name the runtime
    fold holds at the link's output (the second component of `runtimeState`). -/
@[expose] def runtimeTargeted (π : String → Option Procedure) (target : Target)
    (procName0 : Option String := none) :
    List RuntimeBackLink → List (TargetedBackLink Expression Command Target)
  | [] => []
  | l :: ls =>
    l.toTargeted π (runtimeState target procName0 ls).2 :: runtimeTargeted π target procName0 ls

/-- The unit each runtime link lifts at (forward order): a linked phase's
    `sourceUnit` at the state threaded from downstream; `[]` for an unavailable one. -/
def runtimeUnits (target : Target) (procName0 : Option String := none) :
    List RuntimeBackLink → List (List (Stmt Expression Command))
  | [] => []
  | l :: ls =>
    let (tgt, procName) := runtimeState target procName0 ls
    (match l with
     | .unavailable _ => []
     | .linked _ sourceUnit _ => sourceUnit tgt procName) :: runtimeUnits target procName0 ls

/-- Rewriting `target` along the targeted readings of `links` (`targetIn` over
    `runtimeTargeted`: each link's `upstream` map, from the last link to the first) gives
    the target the runtime fold holds after all of `links` (the first component of
    `runtimeState`). -/
theorem targetIn_toTargeted (π : String → Option Procedure) (target : Target)
    (procName0 : Option String)
    (links : List RuntimeBackLink) :
    targetIn (runtimeTargeted π target procName0 links) target
      = (runtimeState target procName0 links).1 := by
  induction links with
  | nil => rfl
  | cons l ls ih =>
    cases l <;> simp! [ih]

/-- The runtime fold over `links.reverse` (from the last link to the first) ends with the
    outcome `composeTargeted` gives over the links' targeted readings at the units
    `runtimeUnits`, and, unless that outcome is the empty outcome, with the threaded
    target and procedure name `runtimeState`. -/
private theorem runtimeFold_eq (target : Target) (π : String → Option Procedure)
    (initial : BackLinkOutcome Expression Command) (procName0 : Option String)
    (links : List RuntimeBackLink) :
    let r := links.reverse.foldl (init := (initial, target, procName0))
      fun (outcome, tgt, procName) runtimeLink =>
        match outcome with
        | ⟨[], none⟩ => (.empty, tgt, procName)
        | _ =>
          match runtimeLink with
          | .unavailable _ => (.empty, tgt, procName)
          | .linked build sourceUnit upstreamTarget =>
            let tgt' := upstreamTarget tgt procName
            let unit := sourceUnit tgt procName
            ((build tgt' procName π).lift unit outcome, tgt',
              if unit.isEmpty then none else procName)
    r.1 = composeTargeted (runtimeTargeted π target procName0 links)
        (runtimeUnits target procName0 links) target initial ∧
      (r.1 = ⟨[], none⟩ ∨ r.2 = runtimeState target procName0 links) := by
  induction links with
  | nil => simp! [runtimeState]
  | cons l ls ih =>
    simp only [List.reverse_cons, List.foldl_append] at *
    generalize ls.reverse.foldl _ _ = r at *
    obtain ⟨o, t, n⟩ := r
    obtain ⟨rfl, hstate⟩ := ih
    simp only [List.foldl_cons, List.foldl_nil, runtimeTargeted, runtimeUnits, composeTargeted]
    split <;> rcases l with _ | _ <;> grind [composeStep, runtimeState, targetIn, emptyBackLink,
      RuntimeBackLink.toTargeted, targetIn_toTargeted, BackLinkOutcome.empty]

/-- The runtime fold `composeRuntimeBackLinks` equals `composeTargeted` over the links'
    targeted readings (`runtimeTargeted`) at the units the runtime fold lifts at
    (`runtimeUnits`). -/
theorem composeRuntimeBackLinks_eq_composeTargeted (target : Target)
    (π : String → Option Procedure) (links : List RuntimeBackLink)
    (initial : BackLinkOutcome Expression Command) (procName0 : Option String := none) :
    composeRuntimeBackLinks target π links initial procName0
      = composeTargeted (runtimeTargeted π target procName0 links)
          (runtimeUnits target procName0 links) target initial :=
  (runtimeFold_eq target π initial procName0 links).1

/-- The reading of an unavailable phase (lifting every outcome to the empty outcome) is
    per-level preserving along any forward map `T` (`TargetedBackLinkPreserves`: for every
    target, an outcome valid at the output unit lifts to one valid at the input unit). -/
theorem toTargeted_unavailable_preserves (π : String → Option Procedure) (phase : String)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    (procName : Option String) :
    TargetedBackLinkPreserves π T ((RuntimeBackLink.unavailable phase).toTargeted π procName) :=
  fun t a _ _ _ _ => validOutcomeT_empty π t a

/-- Let `links` be the pipeline's runtime links (forward order).  Phases transform
    programs, not units, so the per-level units are hypotheses: `hchain` is a forward chain
    of the links' targeted readings, from the global-source unit `st` to the final unit
    `st'`, whose per-link input units are the units the runtime fold lifts at (`hunits`);
    each link's per-level preservation fact is carried by `hchain`.  Then, whenever the
    producer outcome is valid for `target` at `st'`, the runtime outcome is valid at `st`
    for the target as rewritten along the pipeline. -/
theorem composeRuntimeBackLinks_sound (π : String → Option Procedure)
    (links : List RuntimeBackLink)
    (Ts : List (List (Stmt Expression Command) → Option (List (Stmt Expression Command))))
    (st st' : List (Stmt Expression Command)) (target : Target) (procName0 : Option String)
    (hchain : ForwardChainT π (runtimeTargeted π target procName0 links) Ts st st')
    (hunits : hchain.inputUnits = runtimeUnits target procName0 links)
    (producer : BackLinkOutcome Expression Command)
    (hproducer : ValidOutcomeOf (genuineFeasibleT π) target st' producer) :
    ValidOutcomeOf (genuineFeasibleT π) (runtimeState target procName0 links).1 st
      (composeRuntimeBackLinks target π links producer procName0) := by
  rw [composeRuntimeBackLinks_eq_composeTargeted _ π _ _ procName0, ← hunits,
    ← targetIn_toTargeted π _ procName0]
  apply_rules [composeTargeted_sound]

end -- public section

end Core
