/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.AST
public import Lean.Parser.Basic

namespace Strata

open Lean

public abbrev PrattParsingTableMap := Std.HashMap QualifiedIdent Parser.PrattParsingTables

public initialize parserExt : EnvExtension PrattParsingTableMap ←
  registerEnvExtension (pure {})

end Strata
