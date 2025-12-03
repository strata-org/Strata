/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Verifier

namespace Strata

def boogiePrelude :=
#strata
program Boogie;

type None;
const None_none : None;

type Object;
function Object_len(x : Object) : int;
axiom [Object_len_ge_zero]: (forall x : Object :: Object_len(x) >= 0);

function inheritsFrom(child : string, parent : string) : (bool);
axiom [inheritsFrom_refl]: (forall s: string :: {inheritsFrom(s, s)} inheritsFrom(s, s));

/////////////////////////////////////////////////////////////////////////////////////

// Exceptions
// TODO: Formalize the exception hierarchy here:
// https://docs.python.org/3/library/exceptions.html#exception-hierarchy
// We use the name "Error" to stand for Python's Exceptions +
// our own special indicator, Unimplemented which is an artifact of
// Strata that indicates that our models is partial.
type Error;

// Constructors
function Error_TypeError (msg : string) : Error;
function Error_AttributeError (msg : string) : Error;
function Error_RePatternError (msg : string) : Error;
function Error_Unimplemented (msg : string) : Error;

// Testers
function Error_isTypeError (e : Error) : bool;
function Error_isAttributeError (e : Error) : bool;
function Error_isRePatternError (e : Error) : bool;
function Error_isUnimplemented (e : Error) : bool;

// Destructors
function Error_getTypeError (e : Error) : string;
function Error_getAttributeError (e : Error) : string;
function Error_getRePatternError (e : Error) : string;
function Error_getUnimplemented (e : Error) : string;

// Axioms
// Testers of Constructors
axiom [Error_isTypeError_TypeError]:
    (forall msg : string :: {(Error_TypeError(msg))}
        Error_isTypeError(Error_TypeError(msg)));
axiom [Error_isAttributeError_AttributeError]:
    (forall msg : string :: {(Error_AttributeError(msg))}
        Error_isAttributeError(Error_AttributeError(msg)));
axiom [Error_isRePatternError_RePatternError]:
    (forall msg : string ::
        Error_isRePatternError(Error_RePatternError(msg)));
axiom [Error_isUnimplemented_Unimplemented]:
   (forall msg : string ::
        Error_isUnimplemented(Error_Unimplemented(msg)));
// Destructors of Constructors
axiom [Error_getTypeError_TypeError]:
    (forall msg : string ::
        Error_getTypeError(Error_TypeError(msg)) == msg);
axiom [Error_getAttributeError_AttributeError]:
    (forall msg : string ::
        Error_getAttributeError(Error_AttributeError(msg)) == msg);
axiom [Error_getUnimplemented_Unimplemented]:
    (forall msg : string ::
        Error_getUnimplemented(Error_Unimplemented(msg)) == msg);

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

type ExceptErrorRegex := Except Error regex;

// Constructors
function ExceptErrorRegex_mkOK(x : regex) : ExceptErrorRegex;
function ExceptErrorRegex_mkErr(x : Error) : ExceptErrorRegex;
// Testers
function ExceptErrorRegex_isOK(x : ExceptErrorRegex) : bool;
function ExceptErrorRegex_isErr(x : ExceptErrorRegex) : bool;
// Destructors
function ExceptErrorRegex_getOK(x : ExceptErrorRegex) : regex;
function ExceptErrorRegex_getErr(x : ExceptErrorRegex) : Error;
// Axioms
// Testers of Constructors
axiom [ExceptErrorRegex_isOK_mkOK]:
    (forall x : regex :: {(ExceptErrorRegex_mkOK(x))}
        ExceptErrorRegex_isOK(ExceptErrorRegex_mkOK(x)));
axiom [ExceptErrorRegex_isError_mkErr]:
    (forall e : Error :: {(ExceptErrorRegex_mkErr(e))}
        ExceptErrorRegex_isErr(ExceptErrorRegex_mkErr(e)));
// Destructors of Constructors
axiom [ExceptErrorRegex_getOK_mkOK]:
    (forall x : regex :: {(ExceptErrorRegex_mkOK(x))}
        ExceptErrorRegex_getOK(ExceptErrorRegex_mkOK(x)) == x);
axiom [ExceptErrorRegex_getError_mkError]:
    (forall e : Error :: {(ExceptErrorRegex_mkErr(e))}
        ExceptErrorRegex_getErr(ExceptErrorRegex_mkErr(e)) == e);

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

/////////////////////////////////////////////////////////////////////////////////////

// List of strings
type ListStr;
function ListStr_nil() : (ListStr);
function ListStr_cons(x0 : string, x1 : ListStr) : (ListStr);

/////////////////////////////////////////////////////////////////////////////////////

// Uninterpreted procedures
procedure importFrom(module : string, names : ListStr, level : int) returns ();
procedure import(names : ListStr) returns ();
procedure print(msg : string) returns ();

/////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////

// Temporary Types

type ExceptOrNone;
type ExceptCode := string;
type ExceptNone;
const Except_none : ExceptNone;
type ExceptOrNoneTag;
const EN_STR_TAG : ExceptOrNoneTag;
const EN_NONE_TAG : ExceptOrNoneTag;
function ExceptOrNone_tag(v : ExceptOrNone) : ExceptOrNoneTag;
function ExceptOrNone_code_val(v : ExceptOrNone) : ExceptCode;
function ExceptOrNone_none_val(v : ExceptOrNone) : ExceptNone;
function ExceptOrNone_mk_code(s : ExceptCode) : ExceptOrNone;
function ExceptOrNone_mk_none(v : ExceptNone) : ExceptOrNone;
axiom [ExceptOrNone_mk_code_axiom]: (forall s : ExceptCode :: {(ExceptOrNone_mk_code(s))}
        ExceptOrNone_tag(ExceptOrNone_mk_code(s)) == EN_STR_TAG &&
        ExceptOrNone_code_val(ExceptOrNone_mk_code(s)) == s);
axiom [ExceptOrNone_mk_none_axiom]: (forall n : ExceptNone :: {(ExceptOrNone_mk_none(n))}
        ExceptOrNone_tag(ExceptOrNone_mk_none(n)) == EN_NONE_TAG &&
        ExceptOrNone_none_val(ExceptOrNone_mk_none(n)) == n);
axiom [ExceptOrNone_tag_axiom]: (forall v : ExceptOrNone :: {ExceptOrNone_tag(v)}
        ExceptOrNone_tag(v) == EN_STR_TAG ||
        ExceptOrNone_tag(v) == EN_NONE_TAG);
axiom [unique_ExceptOrNoneTag]: EN_STR_TAG != EN_NONE_TAG;

// IntOrNone
type IntOrNone;
type IntOrNoneTag;
const IN_INT_TAG : IntOrNoneTag;
const IN_NONE_TAG : IntOrNoneTag;
function IntOrNone_tag(v : IntOrNone) : IntOrNoneTag;
function IntOrNone_int_val(v : IntOrNone) : int;
function IntOrNone_none_val(v : IntOrNone) : None;
function IntOrNone_mk_int(i : int) : IntOrNone;
function IntOrNone_mk_none(v : None) : IntOrNone;
axiom (forall i : int :: {(IntOrNone_mk_int(i))}
        IntOrNone_tag(IntOrNone_mk_int(i)) == IN_INT_TAG &&
        IntOrNone_int_val(IntOrNone_mk_int(i)) == i);
axiom (forall n : None :: {(IntOrNone_mk_none(n))}
        IntOrNone_tag(IntOrNone_mk_none(n)) == IN_NONE_TAG &&
        IntOrNone_none_val(IntOrNone_mk_none(n)) == n);
axiom (forall v : IntOrNone :: {IntOrNone_tag(v)}
        IntOrNone_tag(v) == IN_INT_TAG ||
        IntOrNone_tag(v) == IN_NONE_TAG);
axiom [unique_IntOrNoneTag]: IN_INT_TAG != IN_NONE_TAG;

// StrOrNone
type StrOrNone;
type StrOrNoneTag;
const SN_STR_TAG : StrOrNoneTag;
const SN_NONE_TAG : StrOrNoneTag;
function StrOrNone_tag(v : StrOrNone) : StrOrNoneTag;
function StrOrNone_str_val(v : StrOrNone) : string;
function StrOrNone_none_val(v : StrOrNone) : None;
function StrOrNone_mk_str(s : string) : StrOrNone;
function StrOrNone_mk_none(v : None) : StrOrNone;

axiom [StrOrNone_tag_of_mk_str_axiom]: (forall s : string :: {StrOrNone_tag(StrOrNone_mk_str(s)), (StrOrNone_mk_str(s))}
        StrOrNone_tag(StrOrNone_mk_str(s)) == SN_STR_TAG);
axiom [StrOrNone_val_of_mk_str_axiom]: (forall s : string :: {StrOrNone_str_val(StrOrNone_mk_str(s)), (StrOrNone_mk_str(s))}
        StrOrNone_str_val(StrOrNone_mk_str(s)) == s);
axiom [StrOrNone_mk_none_axiom]: (forall n : None :: {(StrOrNone_mk_none(n))}
        StrOrNone_tag(StrOrNone_mk_none(n)) == SN_NONE_TAG &&
        StrOrNone_none_val(StrOrNone_mk_none(n)) == n);
axiom [StrOrNone_tag_axiom]: (forall v : StrOrNone :: {StrOrNone_tag(v)}
        StrOrNone_tag(v) == SN_STR_TAG ||
        StrOrNone_tag(v) == SN_NONE_TAG);
axiom [unique_StrOrNoneTag]: SN_STR_TAG != SN_NONE_TAG;

function strOrNone_toObject(v : StrOrNone) : Object;
// Injectivity axiom: different StrOrNone map to different objects.
axiom (forall s1:StrOrNone, s2: StrOrNone :: {strOrNone_toObject(s1), strOrNone_toObject(s2)}
        s1 != s2 ==>
        strOrNone_toObject(s1) != strOrNone_toObject(s2));
axiom (forall s : StrOrNone :: {StrOrNone_tag(s)}
        StrOrNone_tag(s) == SN_STR_TAG ==>
        Object_len(strOrNone_toObject(s)) == str.len(StrOrNone_str_val(s)));

// AnyOrNone
type AnyOrNone;
type AnyOrNoneTag;
const AN_ANY_TAG : AnyOrNoneTag;
const AN_NONE_TAG : AnyOrNoneTag;
function AnyOrNone_tag(v : AnyOrNone) : AnyOrNoneTag;
function AnyOrNone_str_val(v : AnyOrNone) : string;
function AnyOrNone_none_val(v : AnyOrNone) : None;
function AnyOrNone_mk_str(s : string) : AnyOrNone;
function AnyOrNone_mk_none(v : None) : AnyOrNone;
axiom (forall s : string :: {(AnyOrNone_mk_str(s))}
        AnyOrNone_tag(AnyOrNone_mk_str(s)) == AN_ANY_TAG &&
        AnyOrNone_str_val(AnyOrNone_mk_str(s)) == s);
axiom (forall n : None :: {(AnyOrNone_mk_none(n))}
        AnyOrNone_tag(AnyOrNone_mk_none(n)) == AN_NONE_TAG &&
        AnyOrNone_none_val(AnyOrNone_mk_none(n)) == n);
axiom (forall v : AnyOrNone :: {AnyOrNone_tag(v)}
        AnyOrNone_tag(v) == AN_ANY_TAG ||
        AnyOrNone_tag(v) == AN_NONE_TAG);
axiom [unique_AnyOrNoneTag]: AN_ANY_TAG != AN_NONE_TAG;

// BoolOrNone
type BoolOrNone;
type  BoolOrNoneTag;
const BN_BOOL_TAG : BoolOrNoneTag;
const BN_NONE_TAG : BoolOrNoneTag;
function BoolOrNone_tag(v : BoolOrNone) : BoolOrNoneTag;
function BoolOrNone_str_val(v : BoolOrNone) : string;
function BoolOrNone_none_val(v : BoolOrNone) : None;
function BoolOrNone_mk_str(s : string) : BoolOrNone;
function BoolOrNone_mk_none(v : None) : BoolOrNone;
axiom (forall s : string :: {BoolOrNone_mk_str(s)}
        BoolOrNone_tag(BoolOrNone_mk_str(s)) == BN_BOOL_TAG &&
        BoolOrNone_str_val(BoolOrNone_mk_str(s)) == s);
axiom (forall n : None :: {BoolOrNone_mk_none(n)}
        BoolOrNone_tag(BoolOrNone_mk_none(n)) == BN_NONE_TAG &&
        BoolOrNone_none_val(BoolOrNone_mk_none(n)) == n);
axiom (forall v : BoolOrNone :: {BoolOrNone_tag(v)}
        BoolOrNone_tag(v) == BN_BOOL_TAG ||
        BoolOrNone_tag(v) == BN_NONE_TAG);
axiom [unique_BoolOrNoneTag]: BN_BOOL_TAG != BN_NONE_TAG;

// BoolOrStrOrNone
type BoolOrStrOrNone;
type BoolOrStrOrNoneTag;
const BSN_BOOL_TAG : BoolOrStrOrNoneTag;
const BSN_STR_TAG : BoolOrStrOrNoneTag;
const BSN_NONE_TAG : BoolOrStrOrNoneTag;
function BoolOrStrOrNone_tag(v : BoolOrStrOrNone) : BoolOrStrOrNoneTag;
function BoolOrStrOrNone_bool_val(v : BoolOrStrOrNone) : bool;
function BoolOrStrOrNone_str_val(v : BoolOrStrOrNone) : string;
function BoolOrStrOrNone_none_val(v : BoolOrStrOrNone) : None;
function BoolOrStrOrNone_mk_bool(b : bool) : BoolOrStrOrNone;
function BoolOrStrOrNone_mk_str(s : string) : BoolOrStrOrNone;
function BoolOrStrOrNone_mk_none(v : None) : BoolOrStrOrNone;
axiom (forall b : bool :: {BoolOrStrOrNone_mk_bool(b)}
        BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_bool(b)) == BSN_BOOL_TAG &&
        BoolOrStrOrNone_bool_val(BoolOrStrOrNone_mk_bool(b)) == b);
axiom (forall s : string :: {BoolOrStrOrNone_mk_str(s)}
        BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_str(s)) == BSN_STR_TAG &&
        BoolOrStrOrNone_str_val(BoolOrStrOrNone_mk_str(s)) == s);
axiom (forall n : None :: {BoolOrStrOrNone_mk_none(n)}
        BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_none(n)) == BSN_NONE_TAG &&
        BoolOrStrOrNone_none_val(BoolOrStrOrNone_mk_none(n)) == n);
axiom (forall v : BoolOrStrOrNone :: {BoolOrStrOrNone_tag(v)}
        BoolOrStrOrNone_tag(v) == BSN_BOOL_TAG ||
        BoolOrStrOrNone_tag(v) == BSN_STR_TAG ||
        BoolOrStrOrNone_tag(v) == BSN_NONE_TAG);
axiom [unique_BoolOrStrOrNoneTag]: BSN_BOOL_TAG != BSN_STR_TAG && BSN_BOOL_TAG != BSN_NONE_TAG && BSN_STR_TAG != BSN_NONE_TAG;
procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [req_opt_name_none_or_str]: (if (StrOrNone_tag(opt_name) != SN_NONE_TAG) then (StrOrNone_tag(opt_name) == SN_STR_TAG) else true);
  requires [req_opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) == SN_STR_TAG) then (StrOrNone_str_val(opt_name) == "bar") else true);
  ensures [ensures_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
}
{
  assert [assert_name_is_foo]: req_name == "foo";
  assert [assert_opt_name_none_or_str]: (if (StrOrNone_tag(opt_name) != SN_NONE_TAG) then (StrOrNone_tag(opt_name) == SN_STR_TAG) else true);
  assert [assert_opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) == SN_STR_TAG) then (StrOrNone_str_val(opt_name) == "bar") else true);
  assume [assume_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
};

#end

def Boogie.prelude : Boogie.Program :=
   Boogie.getProgram Strata.boogiePrelude |>.fst

end Strata
