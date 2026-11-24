/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExact
import Strata.DL.Imperative.Counterexample.RunProps
import Strata.DL.Imperative.Counterexample.BackLinkProps
import all Strata.Languages.Core.Counterexample.BackLinkExact
import all Strata.DL.Imperative.Counterexample.Run
import all Strata.DL.Imperative.Counterexample.BackLink
import all Strata.Languages.Core.InterpreterReplay
import all Strata.Languages.Core.Counterexample.Run
import all Strata.Languages.Core.Counterexample.BackLink
import all Strata.Languages.Core.Counterexample.ValuationToRun
import Strata.DL.Imperative.Counterexample.Tactics

/-! # Validity of the replay-free back-links for exact phases

Properties of the definitions in `BackLinkExact`:

* `exactBackLink_backLinkPreserves` — the Core instantiation (`BackLinkPreserves`) of
  `Imperative.exactBackLink_preserves`.
* `guardEmptyUnit_preserves` — guarding a back-link at an empty unit keeps it valid.
* `unchangedExactBackLink_preserves` — the back-link of the unchanged-unit certificate
  preserves outcome validity. -/

namespace Core

open Imperative

public section

/-- **Core instantiation.**  The replay-free back-link of a certificate whose claim
    validity is `genuineFeasible π` on both sides and whose target map fixes `target`
    preserves outcome validity (`BackLinkPreserves`): it lifts every outcome valid at the
    downstream unit to one valid at the upstream unit. -/
theorem exactBackLink_backLinkPreserves (π : String → Option Procedure)
    (target : AssertId Expression)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    (name : String)
    (cert : ExactCert T (fun t f c => genuineFeasible π t f c)
      (fun t f c => genuineFeasible π t f c))
    (htgt : cert.backTarget target = target) :
    BackLinkPreserves π target T (exactBackLink name cert) :=
  fun _ _ hT o h => htgt ▸ exactBackLink_preserves name cert _ _ hT target o h

/-- A back-link that preserves outcome validity (`BackLinkPreserves`) still does when
    guarded to return the empty outcome at an empty unit (`guardEmptyUnit`). -/
theorem guardEmptyUnit_preserves (π : String → Option Procedure) (target : AssertId Expression)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {link : BackLink Expression Command Command} (h : BackLinkPreserves π target T link) :
    BackLinkPreserves π target T link.guardEmptyUnit := fun _ _ hT _ ho => by
  simp only [BackLink.guardEmptyUnit]
  split <;> solve_by_elim [validOutcome_empty]

/-- The replay-free back-link of the unchanged-unit certificate over one procedure table
    `π` on both sides preserves outcome validity (`BackLinkPreserves`: it lifts every
    outcome valid at the downstream unit to one valid at the upstream unit), for any
    forward map `T`. -/
theorem unchangedExactBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) (T : List Statement → Option (List Statement)) (name : String) :
    BackLinkPreserves π target T
      (exactBackLink name (ExactCert.ofUnchangedUnit (π' := π) (π := π)
        (isReplaySimulation_of_sub fun _ _ h => h) T)) :=
  fun st st' hT o h => exactBackLink_preserves name _ st st' hT target o h

end -- public section

end Core
