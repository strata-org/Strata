/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.BackLinkExactNondet
import Strata.Languages.Core.Counterexample.BackLinkExactProps

/-! # Properties of the `nondetElim` certificate

Key theorem: `nondetElimExactBackLink_preserves`, outcome-validity preservation of the
exact back-link built from `nondetElimCert` across the phase's per-unit forward map
`nondetElimUnit`. -/

namespace Core

open Imperative

public section

/-- The `nondetElim` back-link preserves outcome validity (`BackLinkPreserves`): with one
    procedure table `π` on both sides, whenever `nondetElimUnit` maps the unit `st` to
    `st'`, it lifts every outcome valid at `st'` to one valid at `st`.  A valid outcome is
    a chain of well-formed counterexamples starting at the top of the unit whose claim,
    if any, is genuine and feasible for `target`. -/
theorem nondetElimExactBackLink_preserves (π : String → Option Procedure)
    (target : AssertId Expression) :
    BackLinkPreserves π target nondetElimUnit
      (exactBackLink "nondetElim" (nondetElimCert π
          π)) := exactBackLink_backLinkPreserves _ _ _ _ rfl

end -- public section

end Core
