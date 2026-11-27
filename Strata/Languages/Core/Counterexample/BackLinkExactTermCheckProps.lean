/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExactProps
import Strata.Languages.Core.Counterexample.BackLinkExactProps

/-! # Exact certificate: `termCheck` on existing procedures

`termCheck` (`TermCheck.termCheck`) keeps every existing `.proc` declaration and adds no
procedure (only `adtRank` functions, axioms and termination lemmas around recursive-function
blocks), so on an existing procedure the unit is unchanged and the procedure tables agree.  The
certificate is `ExactCert.ofSubTable`, the identity certificate of a replay simulation, under
the hypothesis that every procedure the downstream table resolves is resolved identically
upstream (trivial with one table at every level).

Key theorem: `termCheckBackLink_preserves`, outcome-validity preservation of the exact
back-link built from `ExactCert.ofSubTable` on existing procedures. -/

namespace Core

open Imperative

public section

/-- The `termCheck` back-link preserves outcome validity (`BackLinkPreserves`) on existing
    procedures: with one procedure table `π` at every level, it lifts every outcome valid
    at a downstream unit to one valid at the same upstream unit.  A valid outcome is a
    chain of well-formed counterexamples starting at the top of the unit whose claim, if
    any, is genuine and feasible for `target`. -/
theorem termCheckBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) :
    BackLinkPreserves π target (fun st => some st)
      (exactBackLink "termCheck" (ExactCert.ofSubTable (π' := π) (π := π) fun _ _ h => h)) :=
    exactBackLink_backLinkPreserves _ _ _ _ rfl

end -- public section

end Core
