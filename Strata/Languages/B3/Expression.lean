/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.Parse
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/-- B3 Expression is now an abbreviation over B3AST.Expression -/
abbrev Expression := Strata.B3AST.Expression Unit

/-- B3 Pattern is now an abbreviation over B3AST.Pattern -/
abbrev Pattern := Strata.B3AST.Pattern Unit

/-- B3 BinaryOp is now an abbreviation over B3AST.BinaryOp -/
abbrev BinaryOp := Strata.B3AST.BinaryOp Unit

/-- B3 UnaryOp is now an abbreviation over B3AST.UnaryOp -/
abbrev UnaryOp := Strata.B3AST.UnaryOp Unit

/-- B3 QuantifierKind is now an abbreviation over B3AST.QuantifierKind -/
abbrev QuantifierKind := Strata.B3AST.QuantifierKind Unit

/-- Backward compatibility alias -/
abbrev B3Expression := Expression

/-- Backward compatibility alias -/
abbrev B3Pattern := Pattern

end B3
