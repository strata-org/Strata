/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Grammar
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

/--
Core-only prelude declarations for the Python-through-Laurel pipeline.

This contains declarations that cannot be expressed in Laurel grammar:
- Axioms
- Parameterized datatypes (`Except`)
- Type synonyms (`ExceptErrorRegex`)
- Functions using `regex` type
- Procedures using discriminator access (`..`)
- Procedures with labeled requires/ensures

Types already defined in `PythonRuntimeLaurelPart.lean` are forward-declared
here so the DDM parser can resolve references. At the Core level, the
Laurel-translated declarations take precedence and these forward declarations
are filtered out.

The original `CorePrelude.lean` remains unchanged for the Python-through-Core pipeline.
-/
private def pythonRuntimeCorePartDDM :=
#strata
program Core;

// =====================================================================
// Forward declarations of types defined in PythonRuntimeLaurelPart.
// These are needed so the DDM parser can resolve references in axioms
// and procedures below. They will be filtered out when merging with
// the Laurel-translated declarations.
// =====================================================================

type DictStrAny;

datatype Error () {
  NoError (),
  TypeError (Type_msg : string),
  AttributeError (Attribute_msg : string),
  AssertionError (Assertion_msg : string),
  UnimplementedError (Unimplement_msg : string),
  UndefinedError (Undefined_msg : string),
  IndexError (IndexError_msg : string)
};

mutual
datatype Any () {
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
};

datatype ListAny () {
  ListAny_nil (),
  ListAny_cons (h: Any, t: ListAny)
};

end;

type CoreOnlyDelimiter;

// =====================================================================
// Core-only declarations (not expressible in Laurel)
// =====================================================================


// /////////////////////////////////////////////////////////////////////////////////////
// Modelling some datetime-related Python operations, for testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

function to_string(a: Any) : string;

function to_string_any(a: Any) : Any {
  from_string(to_string(a))
}

function datetime_strptime(dtstring: Any, format: Any) : Any;

axiom [datetime_tostring_cancel]: forall dt: Any ::
  datetime_strptime(to_string_any(dt), from_string ("%Y-%m-%d")) == dt;

procedure datetime_date(d: Any) returns (ret: Any, error: Error)
spec {
  requires [d_type]: Any..isfrom_datetime(d);
  ensures [ret_type]: Any..isfrom_datetime(ret) && Any..as_datetime!(ret) <= Any..as_datetime!(d);
}
{
  var timedt: int;
  if (Any..isfrom_datetime(d)) {
    assume [timedt_le]: timedt <= Any..as_datetime!(d);
    ret := from_datetime(timedt);
    error := NoError();
  }
  else {
    ret := from_none();
    error := TypeError("Input must be datetime");
  }
};

procedure datetime_now() returns (ret: Any)
spec {
  ensures [ret_type]: Any..isfrom_datetime(ret);
}
{
  var d: int;
  ret := from_datetime(d);
};

procedure timedelta(days: Any, hours: Any) returns (delta : Any, maybe_except: Error)
spec{
  requires [days_type]: Any..isfrom_none(days) || Any..isfrom_int(days);
  requires [hours_type]: Any..isfrom_none(hours) || Any..isfrom_int(hours);
  requires [days_pos]: Any..isfrom_int(days) ==> Any..as_int!(days)>=0;
  requires [hours_pos]: Any..isfrom_int(hours) ==> Any..as_int!(hours)>=0;
  ensures [ret_pos]: Any..isfrom_int(delta) && Any..as_int!(delta)>=0;
}
{
  var days_i : int := 0;
  if (Any..isfrom_int(days)) {
        days_i := Any..as_int!(days);
  }
  var hours_i : int := 0;
  if (Any..isfrom_int(hours)) {
        hours_i := Any..as_int!(hours);
  }
  delta := from_int ((((days_i * 24) + hours_i) * 3600) * 1000000);
};

// /////////////////////////////////////////////////////////////////////////////////////
// For testing purpose
// /////////////////////////////////////////////////////////////////////////////////////

procedure test_helper_procedure(req_name : Any, opt_name : Any) returns (ret: Any, maybe_except: Error)
spec {
  requires [req_name_is_foo]: req_name == from_string("foo");
  requires [req_opt_name_none_or_str]: (Any..isfrom_none(opt_name)) || (Any..isfrom_string(opt_name));
  requires [req_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar"));
  ensures [ensures_maybe_except_none]: (Error..isNoError(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == from_string("foo");
  assert [assert_opt_name_none_or_str]: (Any..isfrom_none(opt_name)) || (Any..isfrom_string(opt_name));
  assert [assert_opt_name_none_or_bar]: (opt_name == from_none()) || (opt_name == from_string("bar"));
  assume [assume_maybe_except_none]: (Error..isNoError(maybe_except));
};

procedure print(msg : Any) returns ();

#end

/--
Get the Core-only prelude declarations for the Laurel pipeline.
These are declarations that cannot be expressed in Laurel grammar.
The returned program includes forward declarations of types from the
Laurel prelude; callers should filter out duplicates when merging.
-/
def pythonRuntimeCorePart : Core.Program :=
  Core.getProgram pythonRuntimeCorePartDDM |>.fst

/--
Get only the Core-only declarations, dropping the forward declarations
that precede the `type CoreOnlyDelimiter;` sentinel (and the sentinel itself).
Everything after the delimiter is a genuine Core-only declaration.
-/
def coreOnlyFromRuntimeCorePart : List Core.Decl :=
  let decls := pythonRuntimeCorePart.decls
  -- Drop everything up to and including the CoreOnlyDelimiter sentinel
  match decls.dropWhile (fun d => d.name.name != "CoreOnlyDelimiter") with
  | _ :: rest => rest   -- drop the delimiter itself
  | [] => panic! "CoreOnlyDelimiter sentinel not found in pythonRuntimeCorePart"

end Python
end Strata
