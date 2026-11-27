/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkTarget
import all Strata.DL.Imperative.Interpreter
import all Strata.DL.Imperative.InterpreterObs
import all Strata.DL.Imperative.InterpreterCall
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Counterexample.BackLinkExact
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.DL.Imperative.Counterexample.RunProps
import all Strata.DL.Imperative.Counterexample.BackLinkProps
import all Strata.Languages.Core.Counterexample.BackLinkPhases
import all Strata.Languages.Core.Counterexample.BackLinkCallElim
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.DL.Imperative.Counterexample.Tactics
import Strata.Languages.Core.Counterexample.BackLinkPhasesProps
import all Strata.Languages.Core.Counterexample.BackLinkTarget

/-! # Properties of the target back-links

Validity facts for the back-links of `BackLinkTarget`.  `BackLinkPreservesT π t t' T
link` says that whenever the forward map `T` maps the unit `st` to `st'`, `link` lifts
every outcome valid for the target `t` at `st'` to one valid for `t'` at `st`;
`TargetedBackLinkPreserves` is its per-level form for a target-rewriting link, and
`ForwardChainT` a forward chain of such links.

Key theorems: `directTargetBackLink_preserves` (the direct back-link of a target is valid
for it), `composeTargeted_sound` (whole-pipeline soundness with target threading),
`callElimBackLink_targetedPreserves`.  Lemmas on outcome validity: `validOutcomeT_empty`,
`backLinkPreservesT_assert`, `directAssertionBackLink_valid_of_wf`. -/

namespace Core

open Imperative
open BackLinkOutcome

public section

/-! ## Claim validity over targets -/

/-- The empty outcome (no slices, no claim) is valid (`ValidOutcomeOf (genuineFeasibleT π)`)
    for every target at every unit. -/
theorem validOutcomeT_empty (π : String → Option Procedure) (t : Target)
    (stmts : List (Stmt Expression Command)) :
    ValidOutcomeOf (genuineFeasibleT π) t stmts
      (BackLinkOutcome.empty : BackLinkOutcome Expression Command) := by
  simp [ValidOutcomeOf, chain, empty]

/-! ## Direct back-links over `Target` -/

/-- A back-link that preserves outcome validity for the assertion `a` along the forward
    map `T` (`BackLinkPreserves`: whenever `T` maps the unit `st` to `st'`, it lifts every
    outcome valid for `a` at `st'` to one valid for `a` at `st`) preserves it for the
    target `.assert a` (`BackLinkPreservesT`). -/
theorem backLinkPreservesT_assert {π : String → Option Procedure} {a : AssertId Expression}
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {link : BackLink Expression Command Command} (h : BackLinkPreserves π a T link) :
    BackLinkPreservesT π (.assert a) (.assert a) T link := h

/-- `directAssertionBackLink` produces an outcome valid for its assertion `a` at the unit
    `st` (`ValidOutcome`: its chain head starts at the top of `st`, its claim is genuine
    and feasible for `a`, its chain elements are well-formed) from any incoming outcome
    whose chain elements are well-formed (`CexWF`).  The incoming claim is not trusted:
    every claim the link returns is re-validated by replay. -/
theorem directAssertionBackLink_valid_of_wf (π : String → Option Procedure)
    (a : AssertId Expression) (name : String) (st : List (Stmt Expression Command))
    (o : BackLinkOutcome Expression Command) (hwf : ∀ x ∈ o.chain, CexWF x) :
    ValidOutcome π a st ((directAssertionBackLink π a name).lift st o) :=
  cel_directValid _ _ _ _ _ hwf

/-- Let `check` decide the target `t'` soundly: every counterexample it accepts at a fuel
    is a valid claim for `t'` there (`genuineFeasibleT`).  Then the direct checked
    back-link preserves validity from any target `t` to `t'` along any forward map `T`
    (`BackLinkPreservesT`: whenever `T` maps the unit `st` to `st'`, an outcome valid for
    `t` at `st'` lifts to one valid for `t'` at `st`); of the incoming outcome only the
    well-formedness of its chain is used. -/
private theorem directCheckedBackLink_preserves (π : String → Option Procedure) (name : String)
    (check : Nat → CexA Expression Command → Bool) (t t' : Target)
    (hcheck : ∀ f c, check f c = true → genuineFeasibleT π t' f c)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreservesT π t t' T (directCheckedBackLink name check) := fun st _ _ o ⟨_, _, hwf⟩ => by
  simp only [directCheckedBackLink, List.isEmpty_iff]
  have hhead := @headEnv_wf o
  (repeat' split) <;> simp_all [ValidOutcomeOf, chain, empty, CexWF, isTopLevelAt]

/-- The direct loop-VC back-link of `id` preserves validity from any target `t` to the
    loop VC `id` along any forward map `T` (`BackLinkPreservesT`: an outcome valid for `t`
    at the output unit lifts to one valid for `.loopVC id` at the input unit). -/
theorem directLoopVCBackLink_preserves (π : String → Option Procedure) (id : LoopVCId)
    (name : String) (t : Target)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreservesT π t (.loopVC id) T (directLoopVCBackLink π id name) :=
  directCheckedBackLink_preserves _ _ _ _ _ (by exact fun _ _ h => h) T

/-- The direct point-check back-link of `id` preserves validity from any target `t` to
    the point check `id` along any forward map `T` (`BackLinkPreservesT`: an outcome valid
    for `t` at the output unit lifts to one valid for `.atPoint id` at the input unit). -/
theorem directPointBackLink_preserves (π : String → Option Procedure) (id : PointCheckId)
    (name : String) (t : Target)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreservesT π t (.atPoint id) T (directPointBackLink π id name) :=
  directCheckedBackLink_preserves _ _ _ _ _ (by exact fun _ _ h => h) T

/-- **The direct back-link of a target is valid for that target.**  For all targets `t`
    and `t'` and every forward map `T`, `directTargetBackLink π name t'` lifts an outcome
    valid for `t` at the output unit to one valid for `t'` at the input unit
    (`BackLinkPreservesT`). -/
theorem directTargetBackLink_preserves (π : String → Option Procedure) (name : String)
    (t t' : Target)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    BackLinkPreservesT π t t' T (directTargetBackLink π name t') := fun _ _ _ _ hv@⟨_, _, hwf⟩ => by
  cases t' <;> first
    | apply directLoopVCBackLink_preserves <;> assumption
    | apply directPointBackLink_preserves <;> assumption
    | exact directAssertionBackLink_valid_of_wf _ _ _ _ _ hwf

/-! ## Target-threading composition over `Target` -/

/-- **Whole-pipeline soundness with target threading.**  Let `hchain` be a forward chain
    of target-rewriting links (`ForwardChainT`) from the global-source unit `st` to the
    final unit `st'`, each link per-level preserving at its forward map.  If the producer
    outcome is valid (`ValidOutcomeOf (genuineFeasibleT π)`) for the target `t` at `st'`, the
    reverse composition of the links at the chain's input units (`composeTargeted`) is valid at
    `st` for the target as rewritten along the whole chain (`targetIn links t`). -/
theorem composeTargeted_sound (π : String → Option Procedure) (links) (Ts)
    (st st' : List (Stmt Expression Command)) (hchain : ForwardChainT π links Ts st st')
    (t : Target) (producer : BackLinkOutcome Expression Command)
    (hproducer : ValidOutcomeOf (genuineFeasibleT π) t st' producer) :
    ValidOutcomeOf (genuineFeasibleT π) (targetIn links t) st
      (composeTargeted links hchain.inputUnits t producer) := by
  induction hchain with
  | nil => exact hproducer
  | cons _ _ links _ st mid _ hpres hstep _ ih =>
    simp only [ForwardChainT.inputUnits, composeTargeted, composeStep]
    split
    · exact validOutcomeT_empty π _ st
    exact hpres (targetIn links t) st mid hstep _ (ih hproducer)

/-- `callElimUpstreamTarget` maps an id to one that is the upstream id of no generated check
    (`callElimNotGeneratedTarget`) only when it is that id itself. -/
private theorem callElimUpstreamTarget_eq_of_notGenerated {origins : List CallElim.CallOrigin}
    {a : AssertId Expression}
    (h : callElimNotGeneratedTarget origins (callElimUpstreamTarget origins a) = true) :
    a = callElimUpstreamTarget origins a := by
  revert h
  unfold callElimUpstreamTarget
  split
  · rename_i u hu
    obtain ⟨o, ho, hl⟩ := List.exists_of_findSome?_eq_some hu
    obtain ⟨l₁, l₂, hl, -⟩ := List.lookup_eq_some_iff.1 hl
    simp only [callElimNotGeneratedTarget, List.all_eq_true, bne_iff_ne, ne_eq]
    exact fun h => absurd rfl (h o ho _ (hl ▸ List.mem_append_right l₁ List.mem_cons_self))
  · exact fun _ => rfl

/-- `callElimBackLinkT`, with assertion targets rewritten upstream by
    `callElimUpstreamTarget` (other targets unchanged), is per-level preserving along any
    forward map `T` (`TargetedBackLinkPreserves`): for every target `t`, the link built at
    the rewritten target lifts an outcome valid for `t` at the output unit to one valid
    for the rewritten target at the input unit. -/
theorem callElimBackLink_targetedPreserves (π : String → Option Procedure)
    (origins : List CallElim.CallOrigin)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))) :
    TargetedBackLinkPreserves π T
      { build := callElimBackLinkT π origins
        upstream := Target.mapAssert (callElimUpstreamTarget origins) } := by
  intro t
  cases t
  · exact plainOrSlicedLink_preserves_of π _ _ _ _ _ (fun st o hwf => slicedChainOutcome_valid π _
      st _ _ _ (fun _ => dropFreshEnv_wf _) (callElimSlice_wf π _ _)
      (fun c _ => uncallElimConfig_wf _ c) o hwf)
      (fun _ h => callElimUpstreamTarget_eq_of_notGenerated (Bool.and_eq_true _ _ ▸ h).2) T
  all_goals apply_rules [directTargetBackLink_preserves]

end -- public section

end Core
