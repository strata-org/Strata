/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier

namespace Strata
namespace Python

def corePrelude :=
#strata
program Core;

datatype None () {
  None_none()
};

type Object;
function Object_len(x : Object) : int;
axiom [Object_len_ge_zero]: (forall x : Object :: Object_len(x) >= 0);

function inheritsFrom(child : string, parent : string) : (bool);
axiom [inheritsFrom_refl]: (forall s: string :: {inheritsFrom(s, s)} inheritsFrom(s, s));

// /////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.

datatype Error () {
  Error_TypeError(Error_getTypeError: string),
  Error_AttributeError(Error_getAttributeError: string),
  Error_RePatternError(Error_getRePatternError: string),
  Error_Unimplemented(Error_getUnimplemented: string)
};

// /////////////////////////////////////////////////////////////////////////////////////
// /////////////////////////////////////////////////////////////////////////////////////
// Regular Expressions

type Except (err : Type, ok : Type);

// FIXME:
// Once DDM support polymorphic functions (and not just type declarations),
// we will be able to define the following generic functions and axioms. For now,
// we manually define appropriate instantiations.
// Also: when ADT support is lifted up to Boogie, all these
// constructors, testers, destructors, and axioms will be auto-generated.
// How will the DDM keep track of them?

// // Constructors
// function Except_mkOK(err : Type, ok : Type, val : ok) : Except err ok;
// function Except_mkErr(err : Type, ok : Type, val : err) : Except err ok;
// // Testers
// function Except_isOK(err : Type, ok : Type, x : Except err ok) : bool;
// function Except_isErr(err : Type, ok : Type, x : Except err ok) : bool;
// // Destructors
// function Except_getOK(err : Type, ok : Type, x : Except err ok) : ok;
// function Except_getErr(err : Type, ok : Type, x : Except err ok) : err;
// // Axioms
// // Testers of Constructors
// axiom [Except_isOK_mkOK]: (forall x : ok :: Except_isOK(Except_mkOK x));
// axiom [Except_isErr_mkErr]: (forall x : err :: Except_isErr(Except_mkErr x));
// // Destructors of Constructors
// axiom [Except_getOK_mkOK]: (forall x : ok :: Except_getOK(Except_mkOK x) == x);
// axiom [Except_getErr_mkErr]: (forall x : err :: Except_isErr(Except_mkErr x));

datatype ExceptErrorRegex () {
  ExceptErrorRegex_mkOK(ExceptErrorRegex_getOK: regex),
  ExceptErrorRegex_mkErr(ExceptErrorRegex_getErr: Error)
};

// NOTE: `re.match` returns a `Re.Match` object, but for now, we are interested
// only in match/nomatch, which is why we return `bool` here.
function PyReMatchRegex(pattern : regex, str : string, flags : int) : bool;
// We only support Re.Match when flags == 0.
axiom [PyReMatchRegex_def_noFlg]:
  (forall pattern : regex, str : string :: {PyReMatchRegex(pattern, str, 0)}
    PyReMatchRegex(pattern, str, 0) == str.in.re(str, pattern));

// Unsupported/uninterpreted: eventually, this would first call PyReCompile and if there's
// no exception, call PyReMatchRegex.
function PyReMatchStr(pattern : string, str : string, flags : int) : Except Error bool;

// /////////////////////////////////////////////////////////////////////////////////////

// List of strings
datatype ListStr () {
  ListStr_nil(),
  ListStr_cons(ListStr_head: string, ListStr_tail: ListStr)
};

// /////////////////////////////////////////////////////////////////////////////////////

// Temporary Types

datatype ExceptOrNone () {
  ExceptOrNone_mk_code(ExceptOrNone_code_val: string),
  ExceptOrNone_mk_none(ExceptOrNone_none_val: None)
};

datatype IntOrNone () {
  IntOrNone_mk_int(IntOrNone_int_val: int),
  IntOrNone_mk_none(IntOrNone_none_val: None)
};

datatype StrOrNone () {
  StrOrNone_mk_str(StrOrNone_str_val: string),
  StrOrNone_mk_none(StrOrNone_none_val: None)
};

function strOrNone_toObject(v : StrOrNone) : Object;
// Injectivity axiom: different StrOrNone map to different objects.
axiom (forall s1:StrOrNone, s2: StrOrNone :: {strOrNone_toObject(s1), strOrNone_toObject(s2)}
        s1 != s2 ==>
        strOrNone_toObject(s1) != strOrNone_toObject(s2));
axiom (forall s : StrOrNone :: {StrOrNone..isStrOrNone_mk_str(s)}
        StrOrNone..isStrOrNone_mk_str(s) ==>
        Object_len(strOrNone_toObject(s)) == str.len(StrOrNone_str_val(s)));

datatype AnyOrNone () {
  AnyOrNone_mk_str(AnyOrNone_str_val: string),
  AnyOrNone_mk_none(AnyOrNone_none_val: None)
};

datatype BoolOrNone () {
  BoolOrNone_mk_str(BoolOrNone_str_val: string),
  BoolOrNone_mk_none(BoolOrNone_none_val: None)
};

datatype BoolOrStrOrNone () {
  BoolOrStrOrNone_mk_bool(BoolOrStrOrNone_bool_val: bool),
  BoolOrStrOrNone_mk_str(BoolOrStrOrNone_str_val: string),
  BoolOrStrOrNone_mk_none(BoolOrStrOrNone_none_val: None)
};

datatype DictStrStrOrNone () {
  DictStrStrOrNone_mk_str(DictStrStrOrNone_str_val: string),
  DictStrStrOrNone_mk_none(DictStrStrOrNone_none_val: None)
};

datatype BytesOrStrOrNone () {
  BytesOrStrOrNone_mk_none(BytesOrStrOrNone_none_val: None),
  BytesOrStrOrNone_mk_str(BytesOrStrOrNone_str_val: string)
};

type DictStrAny;
function DictStrAny_mk(s : string) : (DictStrAny);

type ListDictStrAny;
function ListDictStrAny_nil() : (ListDictStrAny);

datatype Client () {
  Client_S3(),
  Client_CW()
};

// /////////////////////////////////////////////////////////////////////////////////////
// Datetime

////// 1. Timedelta.

// According to http://docs.python.org/3/library/datetime.html,
// ""
//  Only days, seconds and microseconds are stored internally. Arguments are
//  converted to those units:
//  - A millisecond is converted to 1000 microseconds.
//  - A minute is converted to 60 seconds.
//  - An hour is converted to 3600 seconds.
//  - A week is converted to 7 days.
//  and days, seconds and microseconds are then normalized so that the
//  representation is unique, with
//  - 0 <= microseconds < 1000000
//  - 0 <= seconds < 3600*24 (the number of seconds in one day)
//  - -999999999 <= days <= 999999999
// ""

// In the Strata Core representation, an int type that corresponds to the full
// milliseconds is simply used. See Timedelta_mk.

procedure timedelta(days: IntOrNone, hours: IntOrNone) returns (delta : int, maybe_except: ExceptOrNone)
spec{
}
{
  var days_i : int := 0;
  if (IntOrNone..isIntOrNone_mk_int(days)) {
        days_i := IntOrNone_int_val(days);
  }
  var hours_i : int := 0;
  if (IntOrNone..isIntOrNone_mk_int(hours)) {
        hours_i := IntOrNone_int_val(hours);
  }
  assume [assume_timedelta_sign_matches]: (delta == (((days_i * 24) + hours_i) * 3600) * 1000000);
};

function Timedelta_mk(days : int, seconds : int, microseconds : int): int {
  ((days * 3600 * 24) + seconds) * 1000000 + microseconds
}

function Timedelta_get_days(timedelta : int) : int;
function Timedelta_get_seconds(timedelta : int) : int;
function Timedelta_get_microseconds(timedelta : int) : int;

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


////// Datetime.
// Datetime is abstractly defined as a pair of (base time, relative timedelta).
// datetime.now() returns (<the curent datetime>, 0).
// Adding or subtracting datetime.timedelta updates
type Datetime;
type Datetime_base;

function Datetime_get_base(d : Datetime) : Datetime_base;
function Datetime_get_timedelta(d : Datetime) : int;

// now() returns an abstract, fresh current datetime.
// This abstract now() does not guarantee monotonic increase of time, and this
// means subtracting an 'old' timestamp from a 'new' timestamp may return
// a negative difference.

procedure datetime_now() returns (d:Datetime, maybe_except: ExceptOrNone)
spec {
  ensures (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
}
{
  assume [assume_datetime_now]: (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
};

procedure datetime_utcnow() returns (d:Datetime, maybe_except: ExceptOrNone)
spec {
  ensures (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
}
{
  assume [assume_datetime_now]: (Datetime_get_timedelta(d) == Timedelta_mk(0,0,0));
};

// Addition/subtraction of Datetime and Timedelta.
function Datetime_add(d:Datetime, timedelta:int):Datetime;
function Datetime_sub(d:Datetime, timedelta:int):Datetime {
  Datetime_add(d, -timedelta)
}

axiom [Datetime_add_ax]:
    (forall d:Datetime, timedelta:int :: {}
        Datetime_get_base(Datetime_add(d,timedelta)) == Datetime_get_base(d) &&
        Datetime_get_timedelta(Datetime_add(d,timedelta)) ==
          Datetime_get_timedelta(d)  + timedelta);

// Comparison of Datetimes is abstractly defined so that the result is
// meaningful only if the two datetimes have same base.
function Datetime_lt(d1:Datetime, d2:Datetime):bool;

axiom [Datetime_lt_ax]:
    (forall d1:Datetime, d2:Datetime :: {}
        Datetime_get_base(d1) == Datetime_get_base(d2)
        ==> Datetime_lt(d1, d2) ==
            (Datetime_get_timedelta(d1) < Datetime_get_timedelta(d2)));


type Date;
procedure datetime_date(dt: Datetime) returns (d : Datetime, maybe_except: ExceptOrNone)
spec{};

function datetime_to_str(dt : Datetime) : string;

function datetime_to_int() : int;

procedure datetime_strptime(time: string, format: string) returns (d : Datetime, maybe_except: ExceptOrNone)
spec{
  requires [req_format_str]: (format == "%Y-%m-%d");
  ensures [ensures_str_strp_reverse]: (forall dt : Datetime :: {d == dt} ((time == datetime_to_str(dt)) <==> (d == dt)));
}
{
  assume [assume_str_strp_reverse]: (forall dt : Datetime :: {d == dt} ((time == datetime_to_str(dt)) <==> (d == dt)));
};

/////////////////////////////////////////////////////////////////////////////////////


// /////////////////////////////////////////////////////////////////////////////////////

// Uninterpreted procedures
procedure importFrom(module : string, names : ListStr, level : int) returns ();
procedure import(names : ListStr) returns ();
procedure print(msg : string, opt : StrOrNone) returns ();

procedure json_dumps(msg : DictStrAny, opt_indent : IntOrNone) returns (s: string, maybe_except: ExceptOrNone)
spec{};

procedure json_loads(msg : string) returns (d: DictStrAny, maybe_except: ExceptOrNone)
spec{};

procedure input(msg : string) returns (result: string, maybe_except: ExceptOrNone)
spec{};

procedure random_choice(l : ListStr) returns (result: string, maybe_except: ExceptOrNone)
spec{};

function str_in_list_str(s : string, l: ListStr) : bool;

function str_in_dict_str_any(s : string, l: DictStrAny) : bool;

function list_str_get(l : ListStr, i: int) : string;

function str_len(s : string) : int;

function dict_str_any_get(d : DictStrAny, k: string) : DictStrAny;

function dict_str_any_get_list_str(d : DictStrAny, k: string) : ListStr;

function dict_str_any_get_str(d : DictStrAny, k: string) : string;

function dict_str_any_length(d : DictStrAny) : int;

procedure str_to_float(s : string) returns (result: string, maybe_except: ExceptOrNone)
;

function Float_gt(lhs : string, rhs: string) : bool;

// /////////////////////////////////////////////////////////////////////////////////////



procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [req_opt_name_none_or_str]: (if (!StrOrNone..isStrOrNone_mk_none(opt_name)) then (StrOrNone..isStrOrNone_mk_str(opt_name)) else true);
  requires [req_opt_name_none_or_bar]: (if (StrOrNone..isStrOrNone_mk_str(opt_name)) then (StrOrNone_str_val(opt_name) == "bar") else true);
  ensures [ensures_maybe_except_none]: (ExceptOrNone..isExceptOrNone_mk_none(maybe_except));
}
{
  assert [assert_name_is_foo]: req_name == "foo";
  assert [assert_opt_name_none_or_str]: (if (!StrOrNone..isStrOrNone_mk_none(opt_name)) then (StrOrNone..isStrOrNone_mk_str(opt_name)) else true);
  assert [assert_opt_name_none_or_bar]: (if (StrOrNone..isStrOrNone_mk_str(opt_name)) then (StrOrNone_str_val(opt_name) == "bar") else true);
  assume [assume_maybe_except_none]: (ExceptOrNone..isExceptOrNone_mk_none(maybe_except));
};

#end

def Core.prelude : Core.Program :=
   Core.getProgram corePrelude |>.fst

end Python
end Strata
