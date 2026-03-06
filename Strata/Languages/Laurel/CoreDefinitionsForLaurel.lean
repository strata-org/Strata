/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator

namespace Strata.Laurel

/--
Core map operations (`select`, `update`, `const`) expressed in Laurel syntax.
These are polymorphic map primitives used by the Laurel-to-Core translator.
Since Laurel doesn't have polymorphic types, `int` is used as a placeholder type
for all parameters — the actual types are inferred during Core translation.
-/
def coreDefinitionsForLaurelDDM :=
#strata
program Laurel;

// The types for these Map functions are incorrect.
// We'll fix them when Laurel supports polymorphism
function select(map: int, key: int) : int
  external

function update(map: int, key: int, value: int) : int
  external

function const(value: int) : int
  external

#end

/--
The core map operation definitions as a `Laurel.Program`, parsed at compile time.
-/
def coreDefinitionsForLaurel : Program :=
  let uri := Strata.Uri.file "Strata/Languages/Laurel/CoreDefinitionsForLaurel.lean"
  match TransM.run uri (parseProgram coreDefinitionsForLaurelDDM) with
  | .ok program => program
  | .error e => panic! s!"CoreDefinitionsForLaurel parse error: {e}"

end Strata.Laurel
