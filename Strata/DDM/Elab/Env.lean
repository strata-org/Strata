/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Lean.Parser.Basic

namespace Strata

open Lean

abbrev PrattParsingTableMap := Std.HashMap QualifiedIdent Parser.PrattParsingTables

initialize parserExt : EnvExtension PrattParsingTableMap ←
  registerEnvExtension (pure {})

end Strata
