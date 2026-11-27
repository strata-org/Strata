/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExactProps
import all Strata.Languages.Core.Counterexample.BackLinkExact
import Strata.Languages.Core.Counterexample.BackLinkExactProps

/-! # Exact certificate: `filterProcedures`

`filterProcedures` removes procedures and leaves every remaining unit unchanged
(`Strata/Transform/FilterProcedures.lean`: `prog.decls.filter`).  So the only
difference between a downstream and an upstream replay is the procedure table the
`.call`s resolve against, and the downstream table is a sub-table of the upstream
one.  The two replays are then related by a replay simulation, and the certificate is
`ExactCert.ofSubTable`, the identity on configurations, oracles, targets and fuel.

Key theorem: `filterProceduresBackLink_preserves`, outcome-validity preservation of the
exact back-link built from `ExactCert.ofSubTable`. -/

namespace Core

open Imperative

public section

/-- The `filterProcedures` back-link preserves outcome validity (`BackLinkPreserves`):
    with one procedure table `π` on both sides, it lifts every outcome valid at a
    downstream unit to one valid at the same upstream unit.  A valid outcome is a chain
    of well-formed counterexamples starting at the top of the unit whose claim, if any,
    is genuine and feasible for `target`. -/
theorem filterProceduresBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) :
    BackLinkPreserves π target (fun st => some st)
      (exactBackLink "filterProcedures" (ExactCert.ofSubTable (π' := π) (π := π)
        fun _ _ h => h)) :=
  fun st st' hT o h => exactBackLink_preserves _ _ st st' hT target o h

end -- public section

end Core
