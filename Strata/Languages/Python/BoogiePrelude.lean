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
type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Type constructors
type ListStr;
type None;
type Object;
type ExceptOrNone;
type ExceptNone;
type ExceptOrNoneTag;
type StrOrNone;
type StrOrNoneTag;
type AnyOrNone;
type AnyOrNoneTag;
type BoolOrNone;
type BoolOrNoneTag;
type BoolOrStrOrNone;
type BoolOrStrOrNoneTag;
type IntOrNone;
type IntOrNoneTag;
type BytesOrStrOrNone;
type BytesOrStrOrNoneTag;
type MappingStrStrOrNone;
type MappingStrStrOrNoneTag;
type DictStrAny;
type S3Client;
type CloudWatchClient;
type Client;
type ClientTag;

// Type synonyms
type ExceptCode := string;

// Constants
const None_none : None;
const Except_none : ExceptNone;
const EN_STR_TAG : ExceptOrNoneTag;
const EN_NONE_TAG : ExceptOrNoneTag;
const SN_STR_TAG : StrOrNoneTag;
const SN_NONE_TAG : StrOrNoneTag;
const AN_ANY_TAG : AnyOrNoneTag;
const AN_NONE_TAG : AnyOrNoneTag;
const BN_BOOL_TAG : BoolOrNoneTag;
const BN_NONE_TAG : BoolOrNoneTag;
const BSN_BOOL_TAG : BoolOrStrOrNoneTag;
const BSN_STR_TAG : BoolOrStrOrNoneTag;
const BSN_NONE_TAG : BoolOrStrOrNoneTag;
const C_S3_TAG : ClientTag;
const C_CW_TAG : ClientTag;


function ListStr_nil() : (ListStr);
function ListStr_cons(x0 : string, x1 : ListStr) : (ListStr);
function Object_len(x : Object) : (int);
function inheritsFrom(child : string, parent : string) : (bool);
function ExceptOrNone_tag(v : ExceptOrNone) : (ExceptOrNoneTag);
function ExceptOrNone_code_val(v : ExceptOrNone) : (ExceptCode);
function ExceptOrNone_none_val(v : ExceptOrNone) : (ExceptNone);
function ExceptOrNone_mk_code(s : ExceptCode) : (ExceptOrNone);
function ExceptOrNone_mk_none(v : ExceptNone) : (ExceptOrNone);
function StrOrNone_tag(v : StrOrNone) : (StrOrNoneTag);
function StrOrNone_str_val(v : StrOrNone) : (string);
function StrOrNone_none_val(v : StrOrNone) : (None);
function StrOrNone_mk_str(s : string) : (StrOrNone);
function StrOrNone_mk_none(v : None) : (StrOrNone);
function strOrNone_toObject(x0 : StrOrNone) : (Object);
function AnyOrNone_tag(v : AnyOrNone) : (AnyOrNoneTag);
function AnyOrNone_str_val(v : AnyOrNone) : (string);
function AnyOrNone_none_val(v : AnyOrNone) : (None);
function AnyOrNone_mk_str(s : string) : (AnyOrNone);
function AnyOrNone_mk_none(v : None) : (AnyOrNone);
function IntOrNone_mk_none(v : None) : (IntOrNone);
function BytesOrStrOrNone_mk_none(v : None) : (BytesOrStrOrNone);
function BytesOrStrOrNone_mk_str(s : string) : (BytesOrStrOrNone);
function MappingStrStrOrNone_mk_none(v : None) : (MappingStrStrOrNone);
function BoolOrNone_tag(v : BoolOrNone) : (BoolOrNoneTag);
function BoolOrNone_str_val(v : BoolOrNone) : (string);
function BoolOrNone_none_val(v : BoolOrNone) : (None);
function BoolOrNone_mk_str(s : string) : (BoolOrNone);
function BoolOrNone_mk_none(v : None) : (BoolOrNone);
function BoolOrStrOrNone_tag(v : BoolOrStrOrNone) : (BoolOrStrOrNoneTag);
function BoolOrStrOrNone_bool_val(v : BoolOrStrOrNone) : (bool);
function BoolOrStrOrNone_str_val(v : BoolOrStrOrNone) : (string);
function BoolOrStrOrNone_none_val(v : BoolOrStrOrNone) : (None);
function BoolOrStrOrNone_mk_bool(b : bool) : (BoolOrStrOrNone);
function BoolOrStrOrNone_mk_str(s : string) : (BoolOrStrOrNone);
function BoolOrStrOrNone_mk_none(v : None) : (BoolOrStrOrNone);
function Client_tag(v : Client) : (ClientTag);

// Unique const axioms
axiom [unique_ExceptOrNoneTag]: EN_STR_TAG != EN_NONE_TAG;
axiom [unique_StrOrNoneTag]: SN_STR_TAG != SN_NONE_TAG;
axiom [unique_AnyOrNoneTag]: AN_ANY_TAG != AN_NONE_TAG;
axiom [unique_BoolOrNoneTag]: BN_BOOL_TAG != BN_NONE_TAG;
axiom [unique_BoolOrStrOrNoneTag]: BSN_BOOL_TAG != BSN_STR_TAG && BSN_BOOL_TAG != BSN_NONE_TAG && BSN_STR_TAG != BSN_NONE_TAG;
axiom [unique_ClientTag]: C_S3_TAG != C_CW_TAG;

// Axioms
axiom [ax_l61c1]: (forall x: Object :: {Object_len(x)} (Object_len(x) >= 0));
axiom [ax_l93c1]: (forall s: string :: {inheritsFrom(s, s)} inheritsFrom(s, s));
axiom [ax_l114c1]: (forall s: ExceptCode :: {ExceptOrNone_mk_code(s)} ((ExceptOrNone_tag(ExceptOrNone_mk_code(s)) == EN_STR_TAG) && (ExceptOrNone_code_val(ExceptOrNone_mk_code(s)) == s)));
axiom [ax_l117c1]: (forall n: ExceptNone :: {ExceptOrNone_mk_none(n)} ((ExceptOrNone_tag(ExceptOrNone_mk_none(n)) == EN_NONE_TAG) && (ExceptOrNone_none_val(ExceptOrNone_mk_none(n)) == n)));
axiom [ax_l120c1]: (forall v: ExceptOrNone :: {ExceptOrNone_tag(v)} ((ExceptOrNone_tag(v) == EN_STR_TAG) || (ExceptOrNone_tag(v) == EN_NONE_TAG)));
axiom [ax_l141c1]: (forall s: string :: {StrOrNone_mk_str(s)} ((StrOrNone_tag(StrOrNone_mk_str(s)) == SN_STR_TAG) && (StrOrNone_str_val(StrOrNone_mk_str(s)) == s)));
axiom [ax_l144c1]: (forall n: None :: {StrOrNone_mk_none(n)} ((StrOrNone_tag(StrOrNone_mk_none(n)) == SN_NONE_TAG) && (StrOrNone_none_val(StrOrNone_mk_none(n)) == n)));
axiom [ax_l147c1]: (forall v: StrOrNone :: {StrOrNone_tag(v)} ((StrOrNone_tag(v) == SN_STR_TAG) || (StrOrNone_tag(v) == SN_NONE_TAG)));
axiom [ax_l153c1]: (forall s1: StrOrNone, s2: StrOrNone :: {strOrNone_toObject(s1), strOrNone_toObject(s2)} ((s1 != s2) ==> (strOrNone_toObject(s1) != strOrNone_toObject(s2))));
axiom [ax_l155c1]: (forall s: StrOrNone :: {StrOrNone_tag(s)} ((StrOrNone_tag(s) == SN_STR_TAG) ==> (Object_len(strOrNone_toObject(s)) == str.len(StrOrNone_str_val(s)))));
axiom [ax_l170c1]: (forall s: string :: {AnyOrNone_mk_str(s)} ((AnyOrNone_tag(AnyOrNone_mk_str(s)) == AN_ANY_TAG) && (AnyOrNone_str_val(AnyOrNone_mk_str(s)) == s)));
axiom [ax_l173c1]: (forall n: None :: {AnyOrNone_mk_none(n)} ((AnyOrNone_tag(AnyOrNone_mk_none(n)) == AN_NONE_TAG) && (AnyOrNone_none_val(AnyOrNone_mk_none(n)) == n)));
axiom [ax_l176c1]: (forall v: AnyOrNone :: {AnyOrNone_tag(v)} ((AnyOrNone_tag(v) == AN_ANY_TAG) || (AnyOrNone_tag(v) == AN_NONE_TAG)));
axiom [ax_l191c1]: (forall s: string :: {BoolOrNone_mk_str(s)} ((BoolOrNone_tag(BoolOrNone_mk_str(s)) == BN_BOOL_TAG) && (BoolOrNone_str_val(BoolOrNone_mk_str(s)) == s)));
axiom [ax_l194c1]: (forall n: None :: {BoolOrNone_mk_none(n)} ((BoolOrNone_tag(BoolOrNone_mk_none(n)) == BN_NONE_TAG) && (BoolOrNone_none_val(BoolOrNone_mk_none(n)) == n)));
axiom [ax_l197c1]: (forall v: BoolOrNone :: {BoolOrNone_tag(v)} ((BoolOrNone_tag(v) == BN_BOOL_TAG) || (BoolOrNone_tag(v) == BN_NONE_TAG)));
axiom [ax_l215c1]: (forall b: bool :: {BoolOrStrOrNone_mk_bool(b)} ((BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_bool(b)) == BSN_BOOL_TAG) && (BoolOrStrOrNone_bool_val(BoolOrStrOrNone_mk_bool(b)) <==> b)));
axiom [ax_l218c1]: (forall s: string :: {BoolOrStrOrNone_mk_str(s)} ((BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_str(s)) == BSN_STR_TAG) && (BoolOrStrOrNone_str_val(BoolOrStrOrNone_mk_str(s)) == s)));
axiom [ax_l221c1]: (forall n: None :: {BoolOrStrOrNone_mk_none(n)} ((BoolOrStrOrNone_tag(BoolOrStrOrNone_mk_none(n)) == BSN_NONE_TAG) && (BoolOrStrOrNone_none_val(BoolOrStrOrNone_mk_none(n)) == n)));
axiom [ax_l224c1]: (forall v: BoolOrStrOrNone :: {BoolOrStrOrNone_tag(v)} (((BoolOrStrOrNone_tag(v) == BSN_BOOL_TAG) || (BoolOrStrOrNone_tag(v) == BSN_STR_TAG)) || (BoolOrStrOrNone_tag(v) == BSN_NONE_TAG)));

// Uninterpreted procedures
procedure importFrom(module : string, names : ListStr, level : int) returns ()
;

procedure import(names : ListStr) returns ()
;

procedure print(msg : string) returns ()
;

function str_len(s : string) : int;

procedure test_helper_procedure(req_name : string, opt_name : StrOrNone) returns (maybe_except: ExceptOrNone)
spec {
  requires [req_name_is_foo]: req_name == "foo";
  requires [opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) != SN_NONE_TAG) then (StrOrNone_tag(opt_name) == SN_STR_TAG) else true);
  requires [opt_name_none_or_bar]: (if (StrOrNone_tag(opt_name) == SN_STR_TAG) then (StrOrNone_str_val(opt_name) == "bar") else true);
  free ensures [ensures_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
}
{};

#end

def Boogie.prelude : Boogie.Program :=
   Boogie.getProgram Strata.boogiePrelude |>.fst

end Strata
