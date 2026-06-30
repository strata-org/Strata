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
These are polymorphic map primitives used by the Laurel-to-Core translator.
Since Laurel doesn't have polymorphic types, `int` is used as a placeholder type
for all parameters — the actual types are inferred during Core translation.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

datatype LaurelResolutionErrorPlaceholder {}
datatype Float64IsNotSupportedYet {}
datatype LaurelUnit { MkLaurelUnit() }

// The types for these Map functions are incorrect.
// We'll fix them when Laurel supports polymorphism
// And then we can remove the datatype Box as well
// And remove the hacky filter in HeapParameterization
datatype Box { MkBox() }

function select(map: int, key: int) : Box
  external;

function update(map: int, key: int, value: int) : Box
  external;

function const(value: int) : Box
  external;

// Sequence operations. Parameter types and Seq-valued results use int as a
// placeholder (like Map operations); Core infers the real polymorphic types
// via WFFactory. Sequence.contains is declared bool because its result is
// boolean regardless of element type.
function Sequence.empty() : int
  external;

function Sequence.build(s: int, v: int) : int
  external;

function Sequence.select(s: int, i: int) : int
  external;

function Sequence.update(s: int, i: int, v: int) : int
  external;

function Sequence.length(s: int) : int
  external;

function Sequence.append(s1: int, s2: int) : int
  external;

function Sequence.contains(s: int, v: int) : bool
  external;

function Sequence.take(s: int, n: int) : int
  external;

function Sequence.drop(s: int, n: int) : int
  external;

// Array operations. Desugared by SubscriptElim into Sequence operations on $data.
function Array.length(a: int) : int
  external;

function Sequence.fromArray(a: int) : int
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
