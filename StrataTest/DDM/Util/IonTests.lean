/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.DDM.Util.Ion

namespace Ion.Tests

open Ion

#guard toString Position.root = "root"
#guard toString (Position.root |>.push 0) = "root.0"
#guard toString (Position.root |>.push 0 |>.push 1) = "root.0.1"

end Ion.Tests
