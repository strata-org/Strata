/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Util.Decimal

namespace Strata.Decimal.Tests

open Strata

#guard s!"{Decimal.mk 0 0}" = "0.0"
#guard s!"{Decimal.mk 1 0}" = "1.0"
#guard s!"{Decimal.mk (-3) 0}" = "-3.0"
#guard s!"{Decimal.mk 4 2}" = "400.0"
#guard s!"{Decimal.mk (-4) 2}" = "-400.0"
#guard s!"{Decimal.mk (42) (-2)}" = "0.42"
#guard s!"{Decimal.mk (-42) (-2)}" = "-0.42"
#guard s!"{Decimal.mk (-134) (-2)}" = "-1.34"
#guard s!"{Decimal.mk (-142) 10}" = "-142e10"
#guard s!"{Decimal.mk (-142) 10}" = "-142e10"
-- leading zeros in fractional part
#guard s!"{Decimal.mk 2 (-2)}"  = "0.02"
#guard s!"{Decimal.mk 1 (-2)}"  = "0.01"
#guard s!"{Decimal.mk 5 (-3)}"  = "0.005"
#guard s!"{Decimal.mk 1 (-3)}"  = "0.001"
#guard s!"{Decimal.mk (-2) (-2)}" = "-0.02"

end Strata.Decimal.Tests
