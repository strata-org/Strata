/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DDM.Util.DecimalRat

namespace Strata.Decimal.Tests

open Strata.Decimal

#guard Decimal.fromRat (5 : Rat) = some (Decimal.mk 5 0)
#guard Decimal.fromRat (0 : Rat) = some Decimal.zero
#guard Decimal.fromRat (-3 : Rat) = some (Decimal.mk (-3) 0)
#guard Decimal.fromRat (1/2 : Rat) = some (Decimal.mk 5 (-1))
#guard Decimal.fromRat (1/4 : Rat) = some (Decimal.mk 25 (-2))
#guard Decimal.fromRat (7/20 : Rat) = some (Decimal.mk 35 (-2))
#guard Decimal.fromRat (-1/2 : Rat) = some (Decimal.mk (-5) (-1))
#guard Decimal.fromRat (-7/8 : Rat) = some (Decimal.mk (-875) (-3))
#guard Decimal.fromRat (5/2 : Rat) = some (Decimal.mk 25 (-1))
#guard Decimal.fromRat (15/8 : Rat) = some (Decimal.mk 1875 (-3))
#guard Decimal.fromRat (1/3 : Rat) = none
#guard Decimal.fromRat (1/7 : Rat) = none

#guard Decimal.fromRat (Decimal.mk 5 0).toRat = some (Decimal.mk 5 0)
#guard Decimal.fromRat (Decimal.mk 25 (-1)).toRat = some (Decimal.mk 25 (-1))
#guard Decimal.fromRat (Decimal.mk 375 (-3)).toRat = some (Decimal.mk 375 (-3))
#guard Decimal.fromRat (Decimal.mk (-75) (-2)).toRat = some (Decimal.mk (-75) (-2))
#guard Decimal.fromRat (Decimal.mk 100 (-2)).toRat = some (Decimal.mk 1 0)
#guard (Decimal.fromRat (5 : Rat)).get!.toRat = (5 : Rat)
#guard (Decimal.fromRat (1/2 : Rat)).get!.toRat = (1/2 : Rat)
#guard (Decimal.fromRat (22/5 : Rat)).get!.toRat = (22/5 : Rat)

end Strata.Decimal.Tests
