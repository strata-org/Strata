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

// The types for these Map functions are incorrect.
// We'll fix them when Laurel supports polymorphism
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

/--
E1: the exceptional-channel root for exception handling.
See `docs/design/laurel_extensions.md` (extension E1).

`BaseException` is the root of every value that travels on the exceptional
channel; `throw`'s operand, a `catch` binding, and the `onThrow` binder are all
typed `BaseException` (or a declared subtype). The prelude defines only the
root: any catchable-vs-fatal tiering above it is front-end policy, expressed by
which parent a front-end type `extends` plus the catch predicate.

Unlike `coreDefinitionsForLaurel` (datatypes/functions that are "free" for SMT),
`BaseException` is a *composite* and therefore participates in the heap model.
Injecting it into every program would perturb SMT heap reasoning for programs
that do not use exceptions, so it is kept separate and prepended **only when a
program references it** (see the pipeline's gating on `baseExceptionTypeName`).
-/
def exceptionDefinitionsForLaurelDDM :=
#strata
program Laurel;

composite BaseException {
  var message: string
}

datatype Result<Val, Err> {
  Good(value: Val),
  Bad(err: Err)
}

#end

/--
The E1 exception prelude as a `Laurel.Program`, parsed at compile time.
-/
def exceptionDefinitionsForLaurel : Program :=
  match TransM.run none (parseProgram exceptionDefinitionsForLaurelDDM) with
  | .ok program => program
  | .error e => dbg_trace s!"BUG: ExceptionDefinitionsForLaurel parse error: {e}"; default

end -- public section

end Strata.Laurel
