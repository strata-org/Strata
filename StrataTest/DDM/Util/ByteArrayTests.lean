/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.ByteArray

namespace ByteArray.Tests

#guard (ByteArray.empty |>.back!) = default
#guard (ByteArray.empty |>.push 4 |>.back!) = 4

#guard (ByteArray.empty |>.pop) = .empty
#guard let a := ByteArray.empty |>.push 0 |>.push 1; (a |>.push 2 |>.pop) = a

end ByteArray.Tests
