/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTyUnify

/-! ## Tests for LTyUnify -/

namespace Lambda
open Std (ToFormat Format format)
open LTy.Syntax

/-- info: [(a, int) (b, (arrow c d))] -/
#guard_msgs in
#eval match Constraints.unify [(mty[%a → %b], mty[int → (%c → %d)])] SubstInfo.empty with
  | .ok S => format S.subst
  | .error e => format e

/--
info: Impossible to unify (Map int int) with (Map int bool).
First mismatch: int with bool.
-/
#guard_msgs in
#eval match Constraints.unify [(mty[Map int int], mty[Map int bool])] SubstInfo.empty with
  | .ok S => format S.subst
  | .error e => format e

/--
info: Impossible to unify (Map (Map bool int) int) with (Map int bool).
First mismatch: (Map bool int) with int.
-/
#guard_msgs in
#eval match Constraints.unify [(mty[int], mty[int]),
                               (mty[Map (Map bool int) int], mty[Map int bool])]
                              SubstInfo.empty with
  | .ok S => format S.subst
  | .error e => format e

end Lambda
