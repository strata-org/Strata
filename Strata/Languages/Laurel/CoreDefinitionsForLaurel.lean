/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.AST
public import StrataDDM.Integration.Lean.HashCommands -- shake: keep
public import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.LaurelGrammar

namespace Strata.Laurel

public section

/--
Core map operations (`select`, `update`, `const`) expressed in Laurel syntax.
These are internal stand-ins for Core's native, already-polymorphic map
primitives (the real `∀ k v` signatures live in `Core.Factory`). Declared
`external`, they are filtered out before Core translation and never reach Core
themselves; calls resolve to the Core primitives by name. Their parameters use a
concrete `int` placeholder ON PURPOSE: although Laurel now supports user-level
polymorphism, parameterizing these internal built-ins would buy nothing, since the
polymorphic behavior comes from the Core primitives they map to.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

datatype LaurelResolutionErrorPlaceholder {}
datatype Float64IsNotSupportedYet {}
datatype LaurelUnit { MkLaurelUnit() }

// Concrete `int` placeholders ON PURPOSE: these `external` stand-ins are filtered
// out before Core, where the real polymorphic select/update/const live.
function select(map: int, key: int) : int
  external;

function update(map: int, key: int, value: int) : int
  external;

function const(value: int) : int
  external;

#end

/--
The core map operation definitions as a `Laurel.Program`, parsed at compile time.
-/
def coreDefinitionsForLaurel : Program :=
  match TransM.run none (parseProgram coreDefinitionsForLaurelDDM) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: CoreDefinitionsForLaurel parse error: {e}"; default

end -- public section

end Strata.Laurel
