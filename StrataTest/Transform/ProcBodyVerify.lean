/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Languages.Core.Program

/-! # Procedure Body Verification Tests

Unit tests for the ProcBodyVerify transformation.
-/

namespace ProcBodyVerifyTest

open Core Core.ProcBodyVerify

-- TODO: Add unit tests once we have the transformation working

#guard_msgs in
example : True := by trivial

end ProcBodyVerifyTest
