/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Laurel

namespace Strata
namespace Python

/--
Python prelude declarations expressed in Laurel grammar.
Converted from PythonLaurelCorePrelude.lean (Core dialect) to Laurel dialect.

Core-specific constructs that Laurel does not support:
- `inline` keyword: noted in comments
- Labels on requires/ensures/assert/assume: noted in nearby comments
- Axioms: commented out
- `mutual`/`end` blocks: flattened (Laurel does not support mutual blocks)
-/
private def pythonRuntimeLaurelPartDDM :=
#strata
program Laurel;

// /////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.

datatype Error {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string)
}

// /////////////////////////////////////////////////////////////////////////////////////

// Any type modelling for Python
// We model Any type of Python as an inductive type in Strata,
// where the value of each type is wrapped around by a constructor.
// In the PythonToLaurel translator, all user-defined variables
// and input/outputs of all user-defined functions are
// translated into variables of this Any type.
// We also add exception constructor for Any type to catch
// errors in the functions that model Python operators that
// appears later in this prelude.
// In this prelude, we model datetime as a single int and assume
// that the conversion from a string constant is handled by the translator.

// Note: Core uses mutual/end blocks for Any and ListAny.
// Laurel does not support mutual blocks, so they are declared separately.

datatype Any {
  from_none (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_string (as_string : string),
  from_datetime (as_datetime : int),
  from_Dict (as_Dict: DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: DictStrAny),
  exception (get_error: Error)
}

datatype ListAny {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
}

datatype DictStrAny {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
}

datatype FIRST_END_MARKER { }

#end

/--
Parse the Laurel DDM prelude into a Laurel Program.
-/
def pythonRuntimeLaurelPart : Laurel.Program :=
  match Laurel.TransM.run none (Laurel.parseProgram pythonRuntimeLaurelPartDDM) with
  | .ok p => p
  | .error e => dbg_trace s!"SOUND BUG: Failed to parse Python runtime Laurel part: {e}"; default

end Python
end Strata
