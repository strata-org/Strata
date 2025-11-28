/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.DDMTransform.ParseCST
import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.Languages.B3.Identifiers

namespace B3
open Std (ToFormat Format format)

/-- B3 ParamMode is now an abbreviation over B3AST.ParamMode -/
abbrev ParamMode := Strata.B3AST.ParamMode Unit

/-- B3 FParameter is now an abbreviation over B3AST.FParameter -/
abbrev FParameter := Strata.B3AST.FParameter Unit

/-- B3 PParameter is now an abbreviation over B3AST.PParameter -/
abbrev PParameter := Strata.B3AST.PParameter Unit

/-- B3 Spec is now an abbreviation over B3AST.Spec -/
abbrev Spec := Strata.B3AST.Spec Unit

/-- B3 Decl is now an abbreviation over B3AST.Decl -/
abbrev Decl := Strata.B3AST.Decl Unit

/-- Backward compatibility alias -/
abbrev B3Decl := Decl

/-- Backward compatibility alias -/
abbrev B3FParameter := FParameter

/-- Backward compatibility alias -/
abbrev B3PParameter := PParameter

/-- Backward compatibility alias -/
abbrev B3Spec := Spec

end B3
