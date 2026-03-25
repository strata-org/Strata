/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
public import Strata.Languages.Laurel.Laurel

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
  IndexError (IndexError_msg : string),
  RePatternError (Re_msg : string)
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

datatype OptionInt {
  Some (unwrap: int),
  None ()
}

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
  from_Slice(start: int, stop: OptionInt),
  exception (get_error: Error)
}

datatype ListAny {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
}

datatype ListStr {
  ListStr_nil (),
  ListStr_cons (head: string, tail: ListStr)
}

datatype DictStrAny {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
}

// /////////////////////////////////////////////////////////////////////////////////////
// Regex support — re.Match
//
// Models Python's re.Match as a composite (reference) type following the
// module_Class naming convention (re_Match).
//
// The Python-through-Laurel pipeline is entirely Any-typed: all user
// variables and function inputs/outputs are wrapped in the Any datatype.
// Consequently, re_match/re_search/re_fullmatch return Any (from_none
// or from_ClassInstance wrapping a re_Match).  If the pipeline ever
// moves to concrete types, these should return re_Match | None directly.
//
// Fields that can be determined from the call site are set concretely
// in the Core-only prelude.  pos and endpos are sound as 0 / str.len
// for the module-level re.match/re.search/re.fullmatch API which does
// not accept pos/endpos arguments.  If compiled-pattern method calls
// with explicit pos/endpos are supported later, those values must be
// threaded through.
//
// Methods that depend on capture groups (group, start, end, span,
// groups, lastindex, lastgroup) are uninterpreted because SMT-LIB's
// string theory has no capture group support.  This is a sound
// over-approximation: the solver treats them as abstract, so
// verification results involving these will be inconclusive rather
// than unsound.

composite re_Match {
  var re_match_string : string
  var re_match_pos : int
  var re_match_endpos : int
}

// re.Match methods — uninterpreted (capture groups are beyond SMT-LIB)
function re_Match_group (self : re_Match, n : int) : string;
function re_Match_start (self : re_Match, n : int) : int;
function re_Match_end   (self : re_Match, n : int) : int;
function re_Match_span_start (self : re_Match, n : int) : int;
function re_Match_span_end   (self : re_Match, n : int) : int;
function re_Match_lastindex  (self : re_Match) : int;
function re_Match_lastgroup  (self : re_Match) : string;
function re_Match_groups     (self : re_Match) : ListStr;

datatype FIRST_END_MARKER { }

#end

/--
Parse the Laurel DDM prelude into a Laurel Program.
-/
public def pythonRuntimeLaurelPart : Laurel.Program :=
  match Laurel.TransM.run none (Laurel.parseProgram pythonRuntimeLaurelPartDDM) with
  | .ok p => p
  | .error e => dbg_trace s!"SOUND BUG: Failed to parse Python runtime Laurel part: {e}"; default

end Python
end Strata
