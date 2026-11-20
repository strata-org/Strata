/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Verifier

/-! Importing `Core.Verifier` exports no `Core.Lambda` namespace: inside `namespace Core`,
`open Lambda` opens the root `Lambda`. -/

namespace Core

open Lambda

example := @LExpr.const
example : LMonoTy := LMonoTy.int

end Core
