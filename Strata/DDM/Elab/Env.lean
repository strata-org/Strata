/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Lean.Parser.Basic
import Lean

namespace Strata


abbrev PrattParsingTableMap := Std.HashMap QualifiedIdent Lean.Parser.PrattParsingTables

initialize parserExt : Lean.EnvExtension PrattParsingTableMap ←
  Lean.registerEnvExtension (pure {})

end Strata
