/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import Lean.Parser.Basic

namespace StrataDDM

open Lean

public abbrev PrattParsingTableMap := Std.HashMap QualifiedIdent Parser.PrattParsingTables

public initialize parserExt : EnvExtension PrattParsingTableMap ←
  registerEnvExtension (pure {})

end StrataDDM
