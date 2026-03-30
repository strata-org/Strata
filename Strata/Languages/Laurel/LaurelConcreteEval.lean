/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LaurelInterpreter

/-!
# Concrete Program Interpreter for Laurel

Bridges the gap between `interpStmt` (which operates on individual statements)
and `Laurel.Program` (which is the top-level program structure). Given a program,
builds the required environments and calls `interpStmt` on the `main` procedure's body.

See `LaurelSemantics.lean` for the module layering rationale.
-/

namespace Strata.Laurel

end Strata.Laurel
