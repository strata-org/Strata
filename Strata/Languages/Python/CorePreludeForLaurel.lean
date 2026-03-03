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

Types already defined in `PythonPreludeInLaurel.lean` are forward-declared
here so the DDM parser can resolve references. At the Core level, the
Laurel-translated declarations take precedence and these forward declarations
are filtered out.

The original `CorePrelude.lean` remains unchanged for the Python-through-Core pipeline.
-/
private def corePreludeForLaurelDDM :=
#strata
program Core;

// =====================================================================
// Forward declarations of types defined in PythonPreludeInLaurel.
// These are needed so the DDM parser can resolve references in axioms
// and procedures below. They will be filtered out when merging with
// the Laurel-translated declarations.
// =====================================================================
datatype None () {
  None_none()
};

type Object;
function Object_len(x : Object) : int;
function inheritsFrom(child : string, parent : string) : (bool);

datatype Error () {
  Error_TypeError(getTypeError: string),
  Error_AttributeError(getAttributeError: string),
  Error_RePatternError(getRePatternError: string),
  Error_Unimplemented(getUnimplemented: string)
};

datatype ExceptOrNone () {
  ExceptOrNone_mk_code(code_val: string),
  ExceptOrNone_mk_none(none_val: None)
};

datatype IntOrNone () {
  IntOrNone_mk_int(int_val: int),
  IntOrNone_mk_none(none_val: None)
};

datatype StrOrNone () {
  StrOrNone_mk_str(str_val: string),
  StrOrNone_mk_none(none_val: None)
};

function strOrNone_toObject(v : StrOrNone) : Object;

type Datetime;
type Datetime_base;
type DictStrAny;
type ListDictStrAny;

datatype ListStr () {
  ListStr_nil(),
  ListStr_cons(head: string, tail: ListStr)
};

function Timedelta_mk(days : int, seconds : int, microseconds : int): int {
  ((days * 3600 * 24) + seconds) * 1000000 + microseconds
}
function Timedelta_get_days(timedelta : int) : int;
function Timedelta_get_seconds(timedelta : int) : int;
function Timedelta_get_microseconds(timedelta : int) : int;

function Datetime_get_base(d : Datetime) : Datetime_base;
function Datetime_get_timedelta(d : Datetime) : int;
function Datetime_add(d:Datetime, timedelta:int):Datetime;
function Datetime_lt(d1:Datetime, d2:Datetime):bool;
function datetime_to_str(dt : Datetime) : string;

// =====================================================================
// Core-only declarations (not expressible in Laurel)
// =====================================================================

// Axioms
axiom [Object_len_ge_zero]: (forall x : Object :: Object_len(x) >= 0);
axiom [inheritsFrom_refl]: (forall s: string :: {inheritsFrom(s, s)} inheritsFrom(s, s));

// Parameterized datatype + regex type
datatype Except (err : Type, ok : Type) {
  Except_mkOK(Except_getOK: ok),
  Except_mkErr(Except_getErr: err)
};

type ExceptErrorRegex := Except Error regex;

function PyReMatchRegex(pattern : regex, str : string, flags : int) : bool;
axiom [PyReMatchRegex_def_noFlg]:
  (forall pattern : regex, str : string :: {PyReMatchRegex(pattern, str, 0)}
    PyReMatchRegex(pattern, str, 0) == str.in.re(str, pattern));

function PyReMatchStr(pattern : string, str : string, flags : int) : Except Error bool;

// strOrNone axioms
axiom (forall s1:StrOrNone, s2: StrOrNone :: {strOrNone_toObject(s1), strOrNone_toObject(s2)}
        s1 != s2 ==>
        strOrNone_toObject(s1) != strOrNone_toObject(s2));
axiom (forall s : StrOrNone :: {StrOrNone..isStrOrNone_mk_str(s)}
        StrOrNone..isStrOrNone_mk_str(s) ==>
        Object_len(strOrNone_toObject(s)) == str.len(StrOrNone..str_val(s)));

// Timedelta axioms
axiom [Timedelta_deconstructors]:
    (forall days0 : int, seconds0 : int, msecs0 : int,
            days : int, seconds : int, msecs : int
            :: {(Timedelta_mk(days0, seconds0, msecs0))}
      Timedelta_mk(days0, seconds0, msecs0) ==
          Timedelta_mk(days, seconds, msecs) &&
      0 <= msecs && msecs < 1000000 &&
      0 <= seconds && seconds < 3600 * 24 &&
      -999999999 <= days && days <= 999999999
      ==> Timedelta_get_days(Timedelta_mk(days0, seconds0, msecs0)) == days &&
          Timedelta_get_seconds(Timedelta_mk(days0, seconds0, msecs0)) == seconds &&
          Timedelta_get_microseconds(Timedelta_mk(days0, seconds0, msecs0)) == msecs);

// Datetime axioms
axiom [Datetime_add_ax]:
    (forall d:Datetime, timedelta:int :: {}
        Datetime_get_base(Datetime_add(d,timedelta)) == Datetime_get_base(d) &&
        Datetime_get_timedelta(Datetime_add(d,timedelta)) ==
          Datetime_get_timedelta(d)  + timedelta);

axiom [Datetime_lt_ax]:
    (forall d1:Datetime, d2:Datetime :: {}
        Datetime_get_base(d1) == Datetime_get_base(d2)
        ==> Datetime_lt(d1, d2) ==
            (Datetime_get_timedelta(d1) < Datetime_get_timedelta(d2)));

// Procedures with discriminator access or labeled specs

procedure datetime_strptime(time: string, format: string) returns (d : Datetime, maybe_except: ExceptOrNone)
spec{
  requires [req_format_str]: (format == "%Y-%m-%d");
  ensures [ensures_str_strp_reverse]: (forall dt : Datetime :: {d == dt} ((time == datetime_to_str(dt)) <==> (d == dt)));
}
{
  assume [assume_str_strp_reverse]: (forall dt : Datetime :: {d == dt} ((time == datetime_to_str(dt)) <==> (d == dt)));
};

procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [req_opt_name_none_or_str]: (if (!StrOrNone..isStrOrNone_mk_none(opt_name)) then (StrOrNone..isStrOrNone_mk_str(opt_name)) else true);
  requires [req_opt_name_none_or_bar]: (if (StrOrNone..isStrOrNone_mk_str(opt_name)) then (StrOrNone..str_val(opt_name) == "bar") else true);
  ensures [ensures_maybe_except_none]: (ExceptOrNone..isExceptOrNone_mk_none(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == "foo";
  assert [assert_opt_name_none_or_str]: (if (!StrOrNone..isStrOrNone_mk_none(opt_name)) then (StrOrNone..isStrOrNone_mk_str(opt_name)) else true);
  assert [assert_opt_name_none_or_bar]: (if (StrOrNone..isStrOrNone_mk_str(opt_name)) then (StrOrNone..str_val(opt_name) == "bar") else true);
  assume [assume_maybe_except_none]: (ExceptOrNone..isExceptOrNone_mk_none(maybe_except));
};

#end

/--
Get the Core-only prelude declarations for the Laurel pipeline.
These are declarations that cannot be expressed in Laurel grammar.
The returned program includes forward declarations of types from the
Laurel prelude; callers should filter out duplicates when merging.
-/
def corePreludeForLaurel : Core.Program :=
  Core.getProgram corePreludeForLaurelDDM |>.fst

/--
Get only the Core-only declarations (filtering out forward declarations
of types/functions that are already defined in the Laurel prelude).
-/
def coreOnlyPreludeForLaurel : List Core.Decl :=
  -- Names that are forward-declared here but actually defined in PythonPreludeInLaurel.
  -- These will be provided by the Laurel-translated program, so we filter them out.
  let laurelDefinedNames : Std.HashSet String := Std.HashSet.ofList [
    "None", "Object", "Object_len", "inheritsFrom",
    "Error", "ExceptOrNone", "IntOrNone", "StrOrNone",
    "strOrNone_toObject",
    "Datetime", "Datetime_base", "DictStrAny", "ListDictStrAny", "ListStr",
    "Timedelta_mk", "Timedelta_get_days", "Timedelta_get_seconds", "Timedelta_get_microseconds",
    "Datetime_get_base", "Datetime_get_timedelta", "Datetime_add", "Datetime_lt",
    "datetime_to_str"
  ]
  corePreludeForLaurel.decls.filter fun d =>
    -- Keep declarations whose name is NOT in the Laurel-defined set.
    -- Axioms always pass (they have unique names not in the set).
    -- The Except datatype, ExceptErrorRegex, PyReMatch*, datetime_strptime,
    -- test_helper_procedure, and the timedelta-with-body all pass.
    !laurelDefinedNames.contains d.name.name

end Python
end Strata
