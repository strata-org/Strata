/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/-- B3 Statement is now an abbreviation over B3AST.Statement -/
abbrev Stmt := Strata.B3AST.Statement Unit

/-- B3 CallArg is now an abbreviation over B3AST.CallArg -/
abbrev CallArg := Strata.B3AST.CallArg Unit

/-- Backward compatibility alias -/
abbrev B3Stmt := Stmt

/-- Backward compatibility alias -/
abbrev B3CallArg := CallArg

end B3
