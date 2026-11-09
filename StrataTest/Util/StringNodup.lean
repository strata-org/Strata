/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.StringNodupProps
import all Strata.Util.StringNodup
meta import Strata.Util.StringNodup

/-! # `Strata.StringNodup` unit tests -/

namespace Strata.StringNodup.Test

-- The sort orders the numbers and keeps duplicates, which end up adjacent.
#guard sortFuel 5 [3, 1, 2, 5, 4] == [1, 2, 3, 4, 5]
#guard sortFuel 4 [2, 1, 2, 1] == [1, 1, 2, 2]
#guard sortFuel 0 ([] : List Nat) == []
#guard sortFuel 1 [7] == [7]

-- With too little fuel the result keeps the input's elements but is unsorted.
#guard sortFuel 0 [2, 1] == [2, 1]

#guard strictlyIncreasing [] && strictlyIncreasing [5]
#guard strictlyIncreasing [1, 2, 3] && !strictlyIncreasing [1, 1]

-- The check accepts distinct names, including a non-ASCII one, and rejects a
-- repeated name.
#guard strictlyIncreasing
  (sortFuel 3 (["Int.Add", "Int.Sub", "Bv8.Añadir"].map byteCode))
#guard !strictlyIncreasing
  (sortFuel 3 (["Int.Add", "Int.Sub", "Int.Add"].map byteCode))

-- The kernel discharges the check, giving a proof of `Nodup`.
example : ["Int.Add", "Int.Sub", "Bool.Not", "Bv8.Add"].Nodup :=
  nodup_of_strictlyIncreasing_sortFuel _ (by decide +kernel)

example : ([] : List String).Nodup :=
  nodup_of_strictlyIncreasing_sortFuel _ (by decide +kernel)

end Strata.StringNodup.Test
