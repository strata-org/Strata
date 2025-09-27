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
error: 1 error(s) in ../../Examples/dialects/Arith.dialect.st:
  2:7: Unknown dialect Bool
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
