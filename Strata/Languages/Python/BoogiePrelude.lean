/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Verifier

namespace Strata

open Boogie Lambda

def errorDatatype : LDatatype Boogie.Visibility :=
  { name := "Error"
    typeArgs := []
    constrs := [
      { name := ⟨"TypeError", Boogie.Visibility.unres⟩
        args := [(⟨"Error_getTypeError", Boogie.Visibility.unres⟩, LMonoTy.string)]
        testerName := "Error_isTypeError" },
      { name := ⟨"AttributeError", Boogie.Visibility.unres⟩
        args := [(⟨"Error_getAttributeError", Boogie.Visibility.unres⟩, LMonoTy.string)]
        testerName := "Error_isAttributeError" },
      { name := ⟨"RePatternError", Boogie.Visibility.unres⟩
        args := [(⟨"Error_getRePatternError", Boogie.Visibility.unres⟩, LMonoTy.string)]
        testerName := "Error_isRePatternError" },
      { name := ⟨"Unimplemented", Boogie.Visibility.unres⟩
        args := [(⟨"Error_getUnimplemented", Boogie.Visibility.unres⟩, LMonoTy.string)]
        testerName := "Error_isUnimplemented" }
    ]
    constrs_ne := by decide }

def exceptDatatype : LDatatype Boogie.Visibility :=
  { name := "Except"
    typeArgs := ["err", "ok"]
    constrs := [
      { name := ⟨"mkOK", Boogie.Visibility.unres⟩
        args := [(⟨"Except_getOK", Boogie.Visibility.unres⟩, LMonoTy.ftvar "ok")]
        testerName := "Except_isOK" },
      { name := ⟨"mkErr", Boogie.Visibility.unres⟩
        args := [(⟨"Except_getErr", Boogie.Visibility.unres⟩, LMonoTy.ftvar "err")]
        testerName := "Except_isErr"}
    ]
    constrs_ne := by decide }

def exceptErrorRegexSynonym : Boogie.TypeSynonym :=
  { name := "ExceptErrorRegex"
    typeArgs := []
    type := LMonoTy.tcons "Except" [LMonoTy.tcons "Error" [], LMonoTy.tcons "regex" []] }

def pyReMatchStrFunc : Boogie.Function :=
  { name := ⟨"PyReMatchStr", Boogie.Visibility.unres⟩
    typeArgs := []
    inputs := [
      (⟨"pattern", Boogie.Visibility.unres⟩, LMonoTy.string),
      (⟨"str", Boogie.Visibility.unres⟩, LMonoTy.string),
      (⟨"flags", Boogie.Visibility.unres⟩, LMonoTy.int)
    ]
    output := LMonoTy.tcons "Except" [LMonoTy.tcons "Error" [], LMonoTy.bool]
    body := none }

-- ExceptOrNone related definitions
def exceptCodeSynonym : Boogie.TypeSynonym :=
  { name := "ExceptCode"
    typeArgs := []
    type := LMonoTy.string }

def exceptNoneConstructor : Boogie.TypeConstructor :=
  { name := "ExceptNone"
    numargs := 0 }

def exceptOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "ExceptOrNoneTag"
    numargs := 0 }

def exceptOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "ExceptOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"ExceptOrNone_mk_code", Boogie.Visibility.unres⟩
        args := [(⟨"ExceptOrNone_code_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "ExceptCode" [])],
        testerName := "ExceptOrNone_isCode" },
      { name := ⟨"ExceptOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"ExceptOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "ExceptNone" [])],
        testerName := "ExceptOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- IntOrNone related definitions
def intOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "IntOrNoneTag"
    numargs := 0 }

def intOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "IntOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"IntOrNone_mk_int", Boogie.Visibility.unres⟩
        args := [(⟨"IntOrNone_int_val", Boogie.Visibility.unres⟩, LMonoTy.int)],
        testerName := "IntOrNone_isInt" },
      { name := ⟨"IntOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"IntOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "None" [])],
        testerName := "IntOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- StrOrNone related definitions
def strOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "StrOrNoneTag"
    numargs := 0 }

def strOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "StrOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"StrOrNone_mk_str", Boogie.Visibility.unres⟩
        args := [(⟨"StrOrNone_str_val", Boogie.Visibility.unres⟩, LMonoTy.string)],
        testerName := "StrOrNone_isStr" },
      { name := ⟨"StrOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"StrOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "None" [])],
        testerName := "StrOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- AnyOrNone related definitions
def anyOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "AnyOrNoneTag"
    numargs := 0 }

def anyOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "AnyOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"AnyOrNone_mk_str", Boogie.Visibility.unres⟩
        args := [(⟨"AnyOrNone_str_val", Boogie.Visibility.unres⟩, LMonoTy.string)],
        testerName := "AnyOrNone_isStr" },
      { name := ⟨"AnyOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"AnyOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "None" [])],
        testerName := "AnyOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- BoolOrNone related definitions
def boolOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "BoolOrNoneTag"
    numargs := 0 }

def boolOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "BoolOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"BoolOrNone_mk_str", Boogie.Visibility.unres⟩
        args := [(⟨"BoolOrNone_str_val", Boogie.Visibility.unres⟩, LMonoTy.string)],
        testerName := "BoolOrNone_isStr" },
      { name := ⟨"BoolOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"BoolOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "None" [])],
        testerName := "BoolOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- BoolOrStrOrNone related definitions
def boolOrStrOrNoneTagConstructor : Boogie.TypeConstructor :=
  { name := "BoolOrStrOrNoneTag"
    numargs := 0 }

def boolOrStrOrNoneDatatype : LDatatype Boogie.Visibility :=
  { name := "BoolOrStrOrNone"
    typeArgs := []
    constrs := [
      { name := ⟨"BoolOrStrOrNone_mk_bool", Boogie.Visibility.unres⟩
        args := [(⟨"BoolOrStrOrNone_bool_val", Boogie.Visibility.unres⟩, LMonoTy.bool)],
        testerName := "BoolOrStrOrNone_isBool" },
      { name := ⟨"BoolOrStrOrNone_mk_str", Boogie.Visibility.unres⟩
        args := [(⟨"BoolOrStrOrNone_str_val", Boogie.Visibility.unres⟩, LMonoTy.string)],
        testerName := "BoolOrStrOrNone_isStr" },
      { name := ⟨"BoolOrStrOrNone_mk_none", Boogie.Visibility.unres⟩
        args := [(⟨"BoolOrStrOrNone_none_val", Boogie.Visibility.unres⟩, LMonoTy.tcons "None" [])],
        testerName := "BoolOrStrOrNone_isNone" }
    ]
    constrs_ne := by decide }

-- None type and constant
def noneConstructor : Boogie.TypeConstructor :=
  { name := "None"
    numargs := 0 }

def noneNoneConstant : Boogie.Function :=
  { name := ⟨"None_none", Boogie.Visibility.unres⟩
    typeArgs := []
    inputs := []
    output := LMonoTy.tcons "None" []
    body := none }

-- Object type for strOrNone_toObject
def objectConstructor : Boogie.TypeConstructor :=
  { name := "Object"
    numargs := 0 }

-- strOrNone_toObject function
def strOrNoneToObjectFunc : Boogie.Function :=
  { name := ⟨"strOrNone_toObject", Boogie.Visibility.unres⟩
    typeArgs := []
    inputs := [(⟨"v", Boogie.Visibility.unres⟩, LMonoTy.tcons "StrOrNone" [])]
    output := LMonoTy.tcons "Object" []
    body := none }

def errorProgram : Boogie.Program :=
  { decls := [
      Boogie.Decl.type (Boogie.TypeDecl.con noneConstructor),
      Boogie.Decl.func noneNoneConstant,
      Boogie.Decl.type (Boogie.TypeDecl.con objectConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data errorDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.data exceptDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.syn exceptErrorRegexSynonym),
      Boogie.Decl.func pyReMatchStrFunc,
      Boogie.Decl.type (Boogie.TypeDecl.syn exceptCodeSynonym),
      Boogie.Decl.type (Boogie.TypeDecl.con exceptNoneConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.con exceptOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data exceptOrNoneDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.con intOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data intOrNoneDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.con strOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data strOrNoneDatatype),
      Boogie.Decl.func strOrNoneToObjectFunc,
      Boogie.Decl.type (Boogie.TypeDecl.con anyOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data anyOrNoneDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.con boolOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data boolOrNoneDatatype),
      Boogie.Decl.type (Boogie.TypeDecl.con boolOrStrOrNoneTagConstructor),
      Boogie.Decl.type (Boogie.TypeDecl.data boolOrStrOrNoneDatatype)
    ] }

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

// /////////////////////////////////////////////////////////////////////////////////////
// /////////////////////////////////////////////////////////////////////////////////////
// Regular Expressions

// NOTE: `re.match` returns a `Re.Match` object, but for now, we are interested
// only in match/nomatch, which is why we return `bool` here.
function PyReMatchRegex(pattern : regex, str : string, flags : int) : bool;
// We only support Re.Match when flags == 0.
axiom [PyReMatchRegex_def_noFlg]:
  (forall pattern : regex, str : string :: {PyReMatchRegex(pattern, str, 0)}
    PyReMatchRegex(pattern, str, 0) == str.in.re(str, pattern));

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
   {decls := errorProgram.decls ++ (Boogie.getProgram Strata.boogiePrelude |>.fst).decls}

end Strata
