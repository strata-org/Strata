/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExactInsert
import all Strata.Languages.Core.Counterexample.BackLinkExact
import Strata.Languages.Core.Counterexample.BackLinkExactProps

/-! # Properties of the insertion certificates and `BackLink.orElseIfEmpty`

Key theorems:
- `insExactBackLink_backLinkPreserves`: the exact back-link built from `insCert` preserves
  outcome validity for a target whose label the phase does not reserve.
- `orElseIfEmpty_preserves`: the combinator `BackLink.orElseIfEmpty` preserves outcome
  validity when both of its back-links do. -/

namespace Core

open Imperative

public section

/-- An insertion back-link preserves outcome validity (`BackLinkPreserves`) for a target
    whose label the phase does not reserve: with one procedure table `π` on both sides and
    any per-unit forward map `T`, whenever `T` maps the unit `st` to `st'`, it lifts every
    outcome valid at `st'` to one valid at `st`.  A valid outcome is a chain of well-formed
    counterexamples starting at the top of the unit whose claim, if any, is genuine and
    feasible for `target`. -/
theorem insExactBackLink_backLinkPreserves (ext : String → Bool) (π : String → Option Procedure)
    (target : AssertId Expression) (ht : ext target.label = false)
    (T : List Statement → Option (List Statement)) (name : String) :
    BackLinkPreserves π target T (exactBackLink name (insCert ext π π
        T)) := fun _ _ hT o ho => exactBackLink_preserves _ _ _ _ hT _ o
  ⟨ho.1, fun c f hc => ⟨⟨(ho.2.1 c f hc).1, ht⟩, (ho.2.1 c f hc).2⟩, ho.2.2⟩

/-- `primary.orElseIfEmpty fallback` (use `fallback` where `primary` translates nothing of
    a non-empty chain) preserves outcome validity (`BackLinkPreserves`: whenever `T` maps
    the unit `st` to `st'`, every outcome valid at `st'` lifts to one valid at `st`) when
    both `primary` and `fallback` do. -/
theorem orElseIfEmpty_preserves (π : String → Option Procedure) (target : AssertId Expression)
    {T : List (Stmt Expression Command) → Option (List (Stmt Expression Command))}
    {primary fallback : BackLink Expression Command Command}
    (hp : BackLinkPreserves π target T primary) (hf : BackLinkPreserves π target T fallback) :
    BackLinkPreserves π target T (primary.orElseIfEmpty fallback) := fun st st' hT o ho => by
  simp only [BackLink.orElseIfEmpty]
  split <;> solve_by_elim

end -- public section

end Core
