/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Test the #load_dialect command and also validate example dialects parse.
-/

import Strata.DDM.Integration.Lean

namespace Strata.Test

/--
error: Could not find file INVALID!
-/
#guard_msgs in
#load_dialect "INVALID!"

-- This tests that dialects must be loaded in order.
/--
error: 5 error(s) reading ../../Examples/dialects/Arith.dialect.st:
  2:7: Unknown dialect Bool
  11:27: Undeclared type or category Bool.
  12:27: Undeclared type or category Bool.
  13:27: Undeclared type or category Bool.
  14:27: Undeclared type or category Bool.
-/
#guard_msgs in
#load_dialect "../../Examples/dialects/Arith.dialect.st"

#load_dialect "../../Examples/dialects/Bool.dialect.st"

namespace Bool
#strata_gen Bool
end Bool

#load_dialect "../../Examples/dialects/Arith.dialect.st"

namespace Arith
#strata_gen Arith
end Arith
