/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
public import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

/--
Core-only prelude declarations for the Python-through-Laurel pipeline.

This contains declarations that cannot be expressed in Laurel grammar:
- Axioms
- Parameterized datatypes (`Except`)
- Type synonyms (`ExceptErrorRegex`)
- Functions using `regex` type

Types already defined in `PythonRuntimeLaurelPart.lean` are forward-declared
here so the DDM parser can resolve references. At the Core level, the
Laurel-translated declarations take precedence and these forward declarations
are filtered out.

The original `CorePrelude.lean` remains unchanged for the Python-through-Core pipeline.
-/
private def PythonLaurelCorePreludeDDM :=
#strata
program Core;


// =====================================================================
// Forward declarations of types defined in PythonRuntimeLaurelPart.
// These are needed so the DDM parser can resolve references in axioms
// and procedures below. They will be filtered out when merging with
// the Laurel-translated declarations.
// =====================================================================

datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string),
  RePatternError (Re_msg : string),
  UnknownError ()
};

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

datatype OptionInt {
  OptSome (unwrap: int),
  OptNone ()
};

datatype Any () {
  from_None (),
  from_bool (as_bool : bool),
  from_int (as_int : int),
  from_float (as_float : real),
  from_str (as_string : string),
  from_datetime (as_datetime : int),
  from_bytes (as_bytes: string),
  from_DictStrAny (as_Dict: DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes: DictStrAny),
  from_Slice(start: int, stop: OptionInt),
  exception (get_error: Error)
}

datatype ListAny () {
  ListAny_nil (),
  ListAny_cons (head: Any, tail: ListAny)
}

datatype ListStr () {
  ListStr_nil (),
  ListStr_cons (head: string, tail: ListStr)
}

datatype DictStrAny () {
  DictStrAny_empty (),
  DictStrAny_cons (key: string, val: Any, tail: DictStrAny)
};

type CoreOnlyDelimiter;

// =====================================================================
// Core-only declarations (not expressed in Laurel)
// =====================================================================

// /////////////////////////////////////////////////////////////////////////////////////
// ListAny functions
// /////////////////////////////////////////////////////////////////////////////////////

// TODO introduce procedure types in Laurel so we can move this to the Laurel part
rec function List_map (@[cases] l : ListAny, f: Any -> Any) : ListAny
{
  if ListAny..isListAny_nil(l) then
    ListAny_nil()
  else
    ListAny_cons(f(ListAny..head!(l)), List_map(ListAny..tail!(l), f))
};

rec function List_filter (@[cases] l : ListAny, f: Any -> bool) : ListAny
{
  if ListAny..isListAny_nil(l) then
    ListAny_nil()
  else if f(ListAny..head!(l)) then
    ListAny_cons(ListAny..head!(l), List_filter(ListAny..tail!(l), f))
  else
    List_filter(ListAny..tail!(l), f)
};

#end

public section
/--
Get the Core-only prelude declarations for the Laurel pipeline.
These are declarations that cannot be expressed in Laurel grammar.
The returned program includes forward declarations of types from the
Laurel prelude; callers should filter out duplicates when merging.
-/
def PythonLaurelCorePrelude : Core.Program :=
  Core.getProgram PythonLaurelCorePreludeDDM |>.fst

/--
Get only the Core-only declarations, dropping the forward declarations
that precede the `type CoreOnlyDelimiter;` sentinel (and the sentinel itself).
Everything after the delimiter is a genuine Core-only declaration.
-/
def coreOnlyFromRuntimeCorePart : List Core.Decl :=
  let decls := PythonLaurelCorePrelude.decls
  -- Drop everything up to and including the CoreOnlyDelimiter sentinel
  match decls.dropWhile (fun d => d.name.name != "CoreOnlyDelimiter") with
  | _ :: rest => rest   -- drop the delimiter itself
  | [] => dbg_trace "SOUND BUG: CoreOnlyDelimiter sentinel not found in PythonLaurelCorePrelude"; []

end -- public section


end Python
end Strata
