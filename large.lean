import Strata.DDM.Integration.Lean

namespace Strata

#dialect
dialect Boogie;

type bool;
type int;
type string;
type real;
// TODO: make these parameterized
type bv1;
type bv8;
type bv16;
type bv32;
type bv64;
type Map (dom : Type, range : Type);

category TypeArgs;
op type_args (args : CommaSepBy Ident) : TypeArgs => "<" args ">";

category Bind;
@[declare(v, tp)]
op bind_mk (v : Ident, targs : Option TypeArgs, @[scope(targs)] tp : Type) : Bind =>
  v ":" targs tp;

category DeclList;
@[scope(b)]
op declAtom (b : Bind) : DeclList => b;
@[scope(b)]
op declPush (dl : DeclList, @[scope(dl)] b : Bind) : DeclList => dl "," b;

category MonoBind;
@[declare(v, tp)]
op mono_bind_mk (v : Ident, tp : Type) : MonoBind =>
  v ":" tp;

category MonoDeclList;
@[scope(b)]
op monoDeclAtom (b : MonoBind) : MonoDeclList => b;
@[scope(b)]
op monoDeclPush (dl : MonoDeclList, @[scope(dl)] b : MonoBind) : MonoDeclList =>
  dl "," b;

fn not (b : bool) : bool => "!" b;

fn natToInt (n : Num) : int => n;
fn bv1Lit (n : Num) : bv1 => "bv{1}" "(" n ")";
fn bv8Lit (n : Num) : bv8 => "bv{8}" "(" n ")";
fn bv16Lit (n : Num) : bv16 => "bv{16}" "(" n ")";
fn bv32Lit (n : Num) : bv32 => "bv{32}" "(" n ")";
fn bv64Lit (n : Num) : bv64 => "bv{64}" "(" n ")";
fn strLit (s : Str) : string => s;
fn realLit (d : Decimal) : real => d;

fn if (tp : Type, c : bool, t : tp, f : tp) : tp => "if " c:0 " then " t:50 "else " f:50;

fn old (tp : Type, v : tp) : tp => "old" "(" v ")";

fn map_get (K : Type, V : Type, m : Map K V, k : K) : V => m "[" k "]";
fn map_set (K : Type, V : Type, m : Map K V, k : K, v : V) : Map K V =>
  m "[" k ":=" v "]";

// FIXME: Define polymorphic length and concat functions?
fn str_len (a : string) : int => "str.len" "(" a  ")";
fn str_concat (a : string, b : string) : string => "str.concat" "(" a "," b ")";

fn btrue : bool => "true";
fn bfalse : bool => "false";
fn equiv (a : bool, b : bool) : bool => @[prec(4)] a "<==>" b;
fn implies (a : bool, b : bool) : bool => @[prec(5), rightassoc] a "==>" b;
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a "&&" b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a "||" b;

fn equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a "==" b;
fn not_equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a "!=" b;
fn le (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a "<=" b;
fn lt (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a "<" b;
fn ge (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a ">=" b;
fn gt (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a ">" b;

fn neg_expr (tp : Type, a : tp) : tp => "-" a;
fn add_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a "+" b;
fn sub_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a "-" b;
fn mul_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a "*" b;
fn div_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a "div" b;
fn mod_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a "mod" b;

fn bvnot (tp : Type, a : tp) : tp => "~" a;
fn bvand (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "&" b;
fn bvor (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "|" b;
fn bvxor (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "^" b;
fn bvshl (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "<<" b;
fn bvushr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a ">>" b;
fn bvsshr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a ">>s" b;
fn bvsdiv (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "sdiv" b;
fn bvsmod (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a "smod" b;
fn bvslt (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a "<s" b;
fn bvsle (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a "<=s" b;
fn bvsgt (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a ">s" b;
fn bvsge (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a ">=s" b;

fn bvconcat8 (a : bv8, b : bv8) : bv16 => "bvconcat{8}{8}" "(" a "," b ")";
fn bvconcat16 (a : bv16, b : bv16) : bv32 => "bvconcat{16}{16}" "(" a "," b ")";
fn bvconcat32 (a : bv32, b : bv32) : bv64 => "bvconcat{32}{32}" "(" a "," b ")";

fn bvextract_7_7 (a : bv8) : bv1 => "bvextract{7}{7}{8}" "(" a ")";
fn bvextract_15_15 (a : bv16) : bv1 => "bvextract{15}{15}{16}" "(" a ")";
fn bvextract_31_31 (a : bv32) : bv1 => "bvextract{31}{31}{32}" "(" a ")";
fn bvextract_7_0_16 (a : bv16) : bv8 => "bvextract{7}{0}{16}" "(" a ")";
fn bvextract_7_0_32 (a : bv32) : bv8 => "bvextract{7}{0}{32}" "(" a ")";
fn bvextract_15_0_32 (a : bv32) : bv16 => "bvextract{15}{0}{32}" "(" a ")";
fn bvextract_7_0_64 (a : bv64) : bv8 => "bvextract{7}{0}{64}" "(" a ")";
fn bvextract_15_0_64 (a : bv64) : bv16 => "bvextract{15}{0}{64}" "(" a ")";
fn bvextract_31_0_64 (a : bv64) : bv32 => "bvextract{31}{0}{64}" "(" a ")";

category TriggerGroup;
category Triggers;
op trigger (exprs : CommaSepBy Expr) : TriggerGroup =>
  "{" exprs "}";
op triggersAtom (group : TriggerGroup) : Triggers =>
  group;
op triggersPush (triggers : Triggers, group : TriggerGroup) : Triggers =>
  triggers group;

// Quantifiers without triggers
fn forall (d : DeclList, @[scope(d)] b : bool) : bool =>
  "forall" d "::" b:3;
fn exists (d : DeclList, @[scope(d)] b : bool) : bool =>
  "exists" d "::" b:3;

// Quantifiers with triggers
fn forallT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "forall" d "::" triggers b:3;
fn existsT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "exists" d "::" triggers b:3;

category Lhs;
op lhsIdent (v : Ident) : Lhs => v;
op lhsArray (tp : Type, a : Lhs, idx : tp) : Lhs => a "[" idx "]";

category Statement;
category Block;
category Else;
category Label;

op label (l : Ident) : Label => "[" l "]:";

@[scope(dl)]
op varStatement (dl : DeclList) : Statement => "var " dl ";\n";
@[declare(v, tp)]
op initStatement (tp : Type, v : Ident, e : tp) : Statement => "var " v " : " tp " := " e ";\n";
op assign (tp : Type, v : Lhs, e : tp) : Statement => v " := " e ";\n";
op assume (label : Option Label, c : bool) : Statement => "assume " label c ";\n";
op assert (label : Option Label, c : bool) : Statement => "assert " label c ";\n";
op if_statement (c : bool, t : Block, f : Else) : Statement => "if" "(" c ")" t f;
op else0 () : Else =>;
op else1 (f : Block) : Else => "else" f;
op havoc_statement (v : Ident) : Statement => "havoc " v ";\n";

category Invariant;
op invariant (e : Expr) : Invariant => "invariant" e ";";

op while_statement (c : bool, i : Option Invariant, body : Block) : Statement =>
  "while" "(" c ")" i body;

op call_statement (vs : CommaSepBy Ident, f : Ident, expr : CommaSepBy Expr) : Statement =>
   "call" vs ":=" f "(" expr ")" ";\n";
op call_unit_statement (f : Ident, expr : CommaSepBy Expr) : Statement =>
   "call" f "(" expr ")" ";\n";

op block (c : Seq Statement) : Block => " {\n" indent(2, c:40) "}\n";
op block_statement (label : Ident, b : Block) : Statement => label ": " b;
op goto_statement (label : Ident) : Statement => "goto " label ";\n";

category SpecElt;
category Free;
op free () : Free => "free";
op modifies_spec (nm : Ident) : SpecElt => "modifies " nm ";\n";
op ensures_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free? "ensures " label b ";\n";
op requires_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free? "requires " label b ";\n";

category Spec;
op spec_mk (elts : Seq SpecElt) : Spec => "spec" "{\n" indent(2, elts) "}";

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

op command_procedure (name : Ident,
                      typeArgs : Option TypeArgs,
                      @[scope(typeArgs)] b : Bindings,
                      @[scope(b)] ret : Option MonoDeclList,
                      @[scope(ret)] s: Option Spec,
                      @[scope(ret)] body : Option Block) :
  Command =>
  @[prec(10)] "procedure " name typeArgs b "returns" "(" ret ")\n"
              indent(2, s) body ";\n";

// (FIXME) Change when DDM supports type declarations like so:
// type Array a;
// instead of
// type Array (a : Type);
// where the former is what's needed for Boogie.
@[declareType(name, some args)]
op command_typedecl (name : Ident, args : Option Bindings) : Command =>
  "type " name args ";\n";

@[aliasType(name, some args, rhs)]
op command_typesynonym (name : Ident,
                        args : Option Bindings,
                        targs : Option TypeArgs,
                        @[scope(args)] rhs : Type) : Command =>
  "type " name args ":=" targs rhs ";\n";

@[declare(name, r)]
op command_constdecl (name : Ident,
                      typeArgs : Option TypeArgs,
                      r : Type) : Command =>
  "const " name ":" typeArgs r ";\n";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope (typeArgs)] r : Type) : Command =>
  "function " name typeArgs b ":" r ";\n";

category Inline;
op inline () : Inline => "inline";

@[declareFn(name, b, r)]
op command_fndef (name : Ident,
                  typeArgs : Option TypeArgs,
                  @[scope (typeArgs)] b : Bindings,
                  @[scope (typeArgs)] r : Type,
                  @[scope(b)] c : r,
                  // Prefer adding the inline attribute here so
                  // that the order of the arguments in the fndecl and fndef
                  // agree.
                  inline? : Option Inline) : Command =>
  inline? "function " name typeArgs b " : " r " {\n" indent(2, c) "\n}\n";

@[scope(b)]
op command_var (b : Bind) : Command =>
  @[prec(10)] "var " b ";\n";

op command_axiom (label : Option Label, e : bool) : Command =>
  "axiom " label e ";\n";

op command_distinct (label : Option Label, exprs : CommaSepBy Expr) : Command =>
  "distinct " label "[" exprs "]" ";\n";

#end

set_option maxRecDepth 512
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
// const VALID_SERVICES : (Map string bool);
const C_S3_TAG : ClientTag;
const C_CW_TAG : ClientTag;

// Functions
inline function VALID_SERVICES (s : string) : bool {
  (s == "s3" || s == "cloudwatch" || s == "ec2" || s == "dynamodb" ||
   s == "lambda" || s == "iam" || s == "sns" || s == "sqs" ||
   s == "rds" || s == "elasticache" || s == "cloudformation" ||
   s == "ecs" || s == "eks" || s == "kinesis")
}
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
function Client_s3_val(v : Client) : (S3Client);
function Client_cloudwatch_val(v : Client) : (CloudWatchClient);
function Client_mk_s3(s : S3Client) : (Client);
function Client_mk_cloudwatch(c : CloudWatchClient) : (Client);

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
// axiom [ax_l231c1]: (((((((((((((VALID_SERVICES["s3"] && VALID_SERVICES["cloudwatch"]) && VALID_SERVICES["ec2"]) && VALID_SERVICES["dynamodb"]) && VALID_SERVICES["lambda"]) && VALID_SERVICES["iam"]) && VALID_SERVICES["sns"]) && VALID_SERVICES["sqs"]) && VALID_SERVICES["rds"]) && VALID_SERVICES["elasticache"]) && VALID_SERVICES["cloudformation"]) && VALID_SERVICES["ecs"]) && VALID_SERVICES["eks"]) && VALID_SERVICES["kinesis"]);
// axiom [ax_l231c1]: (forall s: string :: (VALID_SERVICES[s] <==> ((((((((((((((s == "s3") || (s == "cloudwatch")) || (s == "ec2")) || (s == "dynamodb")) || (s == "lambda")) || (s == "iam")) || (s == "sns")) || (s == "sqs")) || (s == "rds")) || (s == "elasticache")) || (s == "cloudformation")) || (s == "ecs")) || (s == "eks")) || (s == "kinesis"))));
axiom [ax_l259c1]: (forall s: S3Client :: {Client_mk_s3(s)} ((Client_tag(Client_mk_s3(s)) == C_S3_TAG) && (Client_s3_val(Client_mk_s3(s)) == s)));
axiom [ax_l262c1]: (forall c: CloudWatchClient :: {Client_mk_cloudwatch(c)} ((Client_tag(Client_mk_cloudwatch(c)) == C_CW_TAG) && (Client_cloudwatch_val(Client_mk_cloudwatch(c)) == c)));

// Uninterpreted procedures
procedure importFrom(module : string, names : ListStr, level : int) returns ()
;

procedure import(names : ListStr) returns ()
;

procedure print(msg : string) returns ()
;

// Implementations
procedure botomoog_client(service_name : string, region_name : StrOrNone, api_version : StrOrNone, use_ssl : BoolOrNone, verify : BoolOrStrOrNone, endpoint_url : StrOrNone, aws_access_key_id : StrOrNone, aws_secret_access_key : StrOrNone, aws_session_token : StrOrNone, config : AnyOrNone, aws_account_id : StrOrNone) returns (result : Client, maybe_except : ExceptOrNone)
spec {
  requires [requires_valid_services]: VALID_SERVICES(service_name);
  requires [requires_region_name_tag]: (if (StrOrNone_tag(region_name) != SN_NONE_TAG) then (StrOrNone_tag(region_name) == SN_STR_TAG) else true);
  requires [requires_region_name_len]: (Object_len(strOrNone_toObject(region_name)) > 0);
  free ensures [ensures_maybe_except_none]: (ExceptOrNone_tag(maybe_except) == EN_NONE_TAG);
  free ensures [ensures_s3_tag]: ((service_name == "s3") ==> (Client_tag(result) == C_S3_TAG));
  free ensures [ensures_cloudwatch_tag]: ((service_name == "cloudwatch") ==> (Client_tag(result) == C_CW_TAG));
}
{
  anon0: {
  }
  end : {}
};
#end

-- def Boogie.prelude : Boogie.Program :=
--    Boogie.getProgram Strata.boogiePrelude |>.fst

end Strata
