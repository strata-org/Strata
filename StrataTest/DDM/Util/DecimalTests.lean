/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.Decimal

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

end Strata.Decimal.Tests
