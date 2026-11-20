/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.Run

/-! # Back-links of Core: outcome-validity preservation

A back-link (`Imperative.BackLink`) translates level-(a) counterexamples (runs of the
program) of a transformation's output into runs of its input.  Its correctness is that it
preserves outcome validity (`ValidOutcomeOf`) across the transformation's forward map: this
module states that property, for a generic claim validity and target type
(`BackLinkPreservesOf`), over `Target` (`BackLinkPreservesT`) and for one assertion
(`BackLinkPreserves`).

Key definitions: `BackLinkPreservesOf`, `BackLinkPreservesT`, `BackLinkPreserves`.
-/

namespace Core

open Imperative

public section

/-- Outcome-validity preservation between two targets, generic over the target type and the
    claim-validity predicate `V`: whenever the forward map `T` maps the unit `st` to `st'`, the
    link lifts every outcome valid for `t` at `st'` (`ValidOutcomeOf V t`) to one valid for `t'`
    at `st`. -/
@[expose] def BackLinkPreservesOf {Tgt : Type} (V : CexValidity Tgt) (t t' : Tgt)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    (link : BackLink Expression Command Command) : Prop :=
  ∀ st st', T st = some st' →
    ∀ o, ValidOutcomeOf V t st' o → ValidOutcomeOf V t' st (link.lift st o)

/-- Outcome-validity preservation between two targets of type `Target`: `BackLinkPreservesOf`
    with claims validated by `genuineFeasibleT π`. -/
abbrev BackLinkPreservesT (π : String → Option Procedure) (t t' : Target)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    (link : BackLink Expression Command Command) : Prop :=
  BackLinkPreservesOf (genuineFeasibleT π) t t' T link

/-- Back-link outcome-validity preservation for one target assertion across the forward map
    `T`: `BackLinkPreservesOf` with claims validated by `genuineFeasible π` and the target
    `target` on both sides (whenever `T` maps `st` to `st'`, the link lifts every outcome valid
    at `st'`, `ValidOutcome`, to one valid at `st`). -/
abbrev BackLinkPreserves (π : String → Option Procedure) (target : AssertId Expression)
    (T : List (Stmt Expression Command) → Option (List (Stmt Expression Command)))
    (link : BackLink Expression Command Command) : Prop :=
  BackLinkPreservesOf (genuineFeasible π) target target T link

end -- public section

end Core
