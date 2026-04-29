/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/- NOTE: This grammar is the source of truth for Core.st syntax. If you change
   keywords, operators, types, or built-in functions here, regenerate the
   editor syntax files by running:
     lake env lean --run editors/GenSyntax.lean all
-/
module

public import Strata.DDM.AST
public import Strata.DDM.HNF
import Strata.DDM.Integration.Lean
public import Strata.DDM.Integration.Lean.OfAstM

---------------------------------------------------------------------
public section
namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

-- Sequence operations and lambda/application syntax increase the grammar size enough
-- to require higher recursion and heartbeat limits.
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

/- DDM support for parsing and pretty-printing Strata Core -/

#dialect
dialect Core;

// Declare Strata Core-specific metadata for datatype declarations
metadata declareDatatype (name : Ident, typeParams : Ident,
constructors : Ident, testerTemplate : FunctionTemplate,
accessorTemplate : FunctionTemplate,
unsafeAccessorTemplate : FunctionTemplate);

type bool;
type int;
type string;
type regex;
type real;
// TODO: make these parameterized
type bv1;
type bv8;
type bv16;
type bv32;
type bv64;
type Map (dom : Type, range : Type);
type Sequence (elem : Type);

category TypeVar;
@[declareTVar(name)]
op type_var (name : Ident) : TypeVar => name;

category TypeArgs;
@[scope(args)]
op type_args (args : CommaSepBy TypeVar) : TypeArgs => "<" args ">";

category Bind;
@[declare(v, tp)]
op bind_mk (v : Ident, targs : Option TypeArgs, @[scope(targs)] tp : Type) : Bind =>
  v " : " targs tp;

category DeclList;
@[scope(b)]
op declAtom (b : Bind) : DeclList => b;
@[scope(b)]
op declPush (dl : DeclList, @[scope(dl)] b : Bind) : DeclList => dl:0 ", " b:0;

category MonoBind;
@[declare(v, tp)]
op mono_bind_mk (v : Ident, tp : Type) : MonoBind =>
  v " : " tp;

category MonoDeclList;
@[scope(b)]
op monoDeclAtom (b : MonoBind) : MonoDeclList => b;
@[scope(b)]
op monoDeclPush (dl : MonoDeclList, @[scope(dl)] b : MonoBind) : MonoDeclList =>
  dl:0 ", " b:0;

fn not (b : bool) : bool => "!" b;

fn natToInt (n : Num) : int => n;
fn bv1Lit (n : Num) : bv1 => "bv{1}" "(" n ")";
fn bv8Lit (n : Num) : bv8 => "bv{8}" "(" n ")";
fn bv16Lit (n : Num) : bv16 => "bv{16}" "(" n ")";
fn bv32Lit (n : Num) : bv32 => "bv{32}" "(" n ")";
fn bv64Lit (n : Num) : bv64 => "bv{64}" "(" n ")";
fn strLit (s : Str) : string => s;
fn realLit (d : Decimal) : real => d;

fn if (tp : Type, c : bool, t : tp, f : tp) : tp => "if " c:0 " then " t:0 " else " f:0;

fn old (tp : Type, v : tp) : tp => "old " v;

fn map_get (K : Type, V : Type, m : Map K V, k : K) : V => m "[" k "]";
fn map_set (K : Type, V : Type, m : Map K V, k : K, v : V) : Map K V =>
  m "[" k ":=" v "]";

// TODO: seq_empty is not yet supported in the grammar because the DDM parser
// cannot currently handle 0-ary polymorphic functions (no arguments to infer
// the type parameter from). The Factory definition exists for programmatic use.
fn seq_length (A : Type, s : Sequence A) : int => "Sequence.length" "(" s ")";
fn seq_select (A : Type, s : Sequence A, i : int) : A => "Sequence.select" "(" s ", " i ")";
fn seq_append (A : Type, s1 : Sequence A, s2 : Sequence A) : Sequence A =>
  "Sequence.append" "(" s1 ", " s2 ")";
fn seq_build (A : Type, s : Sequence A, v : A) : Sequence A =>
  "Sequence.build" "(" s ", " v ")";
fn seq_update (A : Type, s : Sequence A, i : int, v : A) : Sequence A =>
  "Sequence.update" "(" s ", " i ", " v ")";
fn seq_contains (A : Type, s : Sequence A, v : A) : bool =>
  "Sequence.contains" "(" s ", " v ")";
fn seq_take (A : Type, s : Sequence A, n : int) : Sequence A =>
  "Sequence.take" "(" s ", " n ")";
fn seq_drop (A : Type, s : Sequence A, n : int) : Sequence A =>
  "Sequence.drop" "(" s ", " n ")";

// FIXME: Define polymorphic length and concat functions?
fn str_len (a : string) : int => "str.len" "(" a  ")";
fn str_concat (a : string, b : string) : string => "str.concat" "(" a ", " b ")";
fn str_substr (a : string, i : int, n : int) : string => "str.substr" "(" a ", " i ", " n ")";
fn str_toregex (a : string) : regex => "str.to.re" "(" a ")";
fn str_inregex (s : string, a : regex) : bool => "str.in.re" "(" s ", " a ")";
fn re_allchar () : regex => "re.allchar" "(" ")";
fn re_all () : regex => "re.all" "(" ")";
fn re_range (s1 : string, s2 : string) : regex => "re.range" "(" s1 ", " s2 ")";
fn re_concat (r1 : regex, r2 : regex) : regex => "re.concat" "(" r1 ", " r2 ")";
fn re_star (r : regex) : regex => "re.*" "(" r ")";
fn re_plus (r : regex) : regex => "re.+" "(" r ")";
fn re_loop (r : regex, i : int, j : int) : regex => "re.loop" "(" r ", " i ", " j")";
fn re_union (r1 : regex, r2 : regex) : regex => "re.union" "(" r1 ", " r2 ")";
fn re_inter (r1 : regex, r2 : regex) : regex => "re.inter" "(" r1 ", " r2 ")";
fn re_comp (r : regex) : regex => "re.comp" "(" r ")";
fn re_none () : regex => "re.none" "(" ")";

fn btrue : bool => "true";
fn bfalse : bool => "false";
fn equiv (a : bool, b : bool) : bool => @[prec(4)] a " <==> " b;
fn implies (a : bool, b : bool) : bool => @[prec(5), rightassoc] a " ==> " b;
fn and (a : bool, b : bool) : bool => @[prec(10), leftassoc] a " && " b;
fn or (a : bool, b : bool) : bool => @[prec(8), leftassoc] a " || " b;

fn equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " != " b;
fn le (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " <= " b;
fn lt (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " < "  b;
fn ge (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " >= " b;
fn gt (tp : Type, a : tp, b : tp) : bool => @[prec(15)] a " > "  b;

fn neg_expr (tp : Type, a : tp) : tp => "-" a;
fn add_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a " + " b;
fn sub_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a " - " b;
fn mul_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " * " b;
fn div_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " div " b;
fn mod_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " mod " b;
fn safediv_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " / " b;
fn safemod_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " % " b;
fn divt_expr (tp : Type, a : tp, b : tp) : tp => "Int.DivT(" a ", " b ")";
fn modt_expr (tp : Type, a : tp, b : tp) : tp => "Int.ModT(" a ", " b ")";
fn safedivt_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " /t " b;
fn safemodt_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " %t " b;

fn bvnot (tp : Type, a : tp) : tp => "~" a;
fn bvand (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " & " b;
fn bvor (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " | " b;
fn bvxor (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " ^ " b;
fn bvshl (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " << " b;
fn bvushr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " >> " b;
fn bvsshr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " >>s " b;
fn bvsdiv (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " sdiv " b;
fn bvsmod (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " smod " b;
fn safeadd_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a " safe+ " b;
fn safesub_expr (tp : Type, a : tp, b : tp) : tp => @[prec(25), leftassoc] a " safe- " b;
fn safemul_expr (tp : Type, a : tp, b : tp) : tp => @[prec(30), leftassoc] a " safe* " b;
fn safeneg_expr (tp : Type, a : tp) : tp => "safe_neg " a;
fn safesdiv_expr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " safesdiv " b;
fn safesmod_expr (tp : Type, a : tp, b : tp) : tp => @[prec(20), leftassoc] a " safesmod " b;
fn bvslt (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a " <s " b;
fn bvsle (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a " <=s " b;
fn bvsgt (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a " >s " b;
fn bvsge (tp : Type, a : tp, b : tp) : bool => @[prec(20), leftassoc] a " >=s " b;

fn bvconcat8 (a : bv8, b : bv8) : bv16 => "bvconcat{8}{8}" "(" a ", " b ")";
fn bvconcat16 (a : bv16, b : bv16) : bv32 => "bvconcat{16}{16}" "(" a ", " b ")";
fn bvconcat32 (a : bv32, b : bv32) : bv64 => "bvconcat{32}{32}" "(" a ", " b ")";

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
  " { " exprs " }\n  ";
op triggersAtom (group : TriggerGroup) : Triggers =>
  group;
op triggersPush (triggers : Triggers, group : TriggerGroup) : Triggers =>
  triggers group;

// Lambda abstraction
fn lambda (tp : Type, d : DeclList, @[scope(d)] body : tp) : fnOf(d, tp) =>
  "fun " d " => " body:3;

// Application of an expression to an argument
fn apply_expr (inTp : Type, outTp : Type, f : inTp -> outTp, x : inTp) : outTp =>
  "(" f ")" "(" x ")";

// Quantifiers without triggers
fn forall (d : DeclList, @[scope(d)] b : bool) : bool =>
  "forall " d " :: " b:3;
fn exists (d : DeclList, @[scope(d)] b : bool) : bool =>
  "exists " d " :: " b:3;

// Quantifiers with triggers
fn forallT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "forall " d " :: " triggers indent(2, b:3);
fn existsT (d : DeclList, @[scope(d)] triggers : Triggers,  @[scope(d)] b : bool) : bool =>
  "exists " d " :: " triggers indent(2, b:3);

category Lhs;
op lhsIdent (v : Ident) : Lhs => v;
op lhsArray (tp : Type, a : Lhs, idx : tp) : Lhs => a "[" idx "]";

category Statement;
category Block;
category Else;
category Label;
category ReachCheck;

op label (l : Ident) : Label => "[" l "]: ";
op reachCheck () : ReachCheck => "@[reachCheck] ";

@[scope(dl)]
op varStatement (dl : DeclList) : Statement => "var " dl ";";
@[declare(v, tp)]
op initStatement (tp : Type, v : Ident, e : tp) : Statement => "var " v " : " tp " := " e ";";
op assign (tp : Type, v : Lhs, e : tp) : Statement => v:0 " := " e ";";
op assume (label : Option Label, c : bool) : Statement => "assume " label c ";";
op assert (reachCheck? : Option ReachCheck, label : Option Label, c : bool) : Statement =>
  reachCheck?:0 "assert " label c ";";
op cover (reachCheck? : Option ReachCheck, label : Option Label, c : bool) : Statement =>
  reachCheck?:0 "cover " label c ";";
category ExprOrNondet;
op condDet (c : bool) : ExprOrNondet => "(" c ")";
op condNondet : ExprOrNondet => "*";

op if_statement (c : ExprOrNondet, t : Block, f : Else) : Statement => "if " c:0 " " t:0 f:0;
op else0 () : Else =>;
op else1 (f : Block) : Else => " else " f:0;
op havoc_statement (v : Ident) : Statement => "havoc " v ";";

category Invariant;
op invariant (e : Expr) : Invariant => "invariant" e ";";

category Invariants;
op nilInvariants : Invariants => ;
op consInvariants(e : Expr, is : Invariants) : Invariants =>
  "invariant " e "\n" is:0;

category Measure;
op measure_mk (e : Expr) : Measure => "decreases " e "\n";

op while_statement (c : ExprOrNondet, m : Option Measure, is : Invariants, body : Block) : Statement =>
  "while " c:0 "\n" m:0 is body:0;

category CallArg;
op callArgExpr (e : Expr) : CallArg => e;
op callArgOut (v : Ident) : CallArg => "out " v;
op callArgInout (v : Ident) : CallArg => "inout " v;

op call_statement (f : Ident, args : CommaSepBy CallArg) : Statement =>
   "call " f "(" args ")" ";";

@[scope(c)]
op block (c : NewlineSepBy Statement) : Block => "{\n  " indent(2, c) "\n}";
op block_statement (label : Ident, b : Block) : Statement => label ": " b:0;
op exit_statement (label : Ident) : Statement => "exit " label ";";
op exit_unlabeled_statement : Statement => "exit;";

category SpecElt;
category Free;
op free () : Free => "free ";
op ensures_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free?:0 "ensures " label b ";\n";
op requires_spec (label : Option Label, free? : Option Free, b : bool) : SpecElt =>
  free?:0 "requires " label b ";\n";
op decreases_spec (e : Expr) : SpecElt =>
  "decreases " e ";\n";

category Spec;
op spec_mk (elts : Seq SpecElt) : Spec => "spec " indent(2, "{\n" elts "} ");

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name " : " tp:0;
@[declare(name, tp)]
op outBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "out " name " : " tp:0;
@[declare(name, tp)]
op inoutBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "inout " name " : " tp:0;
@[declare(name, tp)]
op casesBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] "@[cases] " name " : " tp:0;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => " (" bindings ")";

op command_procedure (name : Ident,
                      typeArgs : Option TypeArgs,
                      @[scope(typeArgs)] b : Bindings,
                      @[scope(b)] s: Option Spec,
                      @[scope(b)] body : Option Block) :
  Command =>
  @[prec(10)] "procedure " name typeArgs b "\n"
              s body ";\n";

// (FIXME) Change when DDM supports type declarations like so:
// type Array a;
// instead of
// type Array (a : Type);
// where the former is what Boogie does.
@[declareType(name, some args)]
op command_typedecl (name : Ident, args : Option Bindings) : Command =>
  "type " name args ";\n";

@[aliasType(name, some args, rhs)]
op command_typesynonym (name : Ident,
                        args : Option Bindings,
                        targs : Option TypeArgs,
                        @[scope(args)] rhs : Type) : Command =>
  "type " name args " := " targs rhs ";\n";

@[declare(name, r)]
op command_constdecl (name : Ident,
                      typeArgs : Option TypeArgs,
                      r : Type) : Command =>
  "const " name ":" typeArgs r ";\n";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope(typeArgs)] r : Type) : Command =>
  "function " name typeArgs b " : " r ";\n";

category Inline;
op inline () : Inline => "inline";

// Note: when editing command_fndef, consider whether recfn_decl needs
// matching edits.
@[declareFn(name, b, r)]
op command_fndef (name : Ident,
                  typeArgs : Option TypeArgs,
                  @[scope(typeArgs)] b : Bindings,
                  @[scope(typeArgs)] r : Type,
                  @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
                  @[scope(b)] c : r,
                  // Prefer adding the inline attribute here so
                  // that the order of the arguments in the fndecl and fndef
                  // agree.
                  inline? : Option Inline) : Command =>
  inline? "function " name typeArgs b " : " r indent(2, preconds) " {\n  " indent(2, c) "\n}\n";

// Recursive (and mutually recursive) function declarations.
// A single recursive function is a 1-element block, just like datatypes.
category RecFnDecl;

@[declareFn(name, b, r)]
op recfn_decl (name : Ident,
               typeArgs : Option TypeArgs,
               @[scope(typeArgs)] b : Bindings,
               @[scope(typeArgs)] r : Type,
               @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
               @[scope(b)] c : r) : RecFnDecl =>
  "function " name typeArgs b " : " r indent(2, preconds) "\n{\n  " indent(2, c) "\n}";

@[scope(recfns), preRegisterFunctions(recfns)]
op command_recfndefs (recfns : NewlineSepBy RecFnDecl) : Command =>
  "rec " recfns ";\n";

// Function declaration statement
@[declareFn(name, b, r)]
op funcDecl_statement (name : Ident,
                       typeArgs : Option TypeArgs,
                       @[scope(typeArgs)] b : Bindings,
                       @[scope(typeArgs)] r : Type,
                       @[scope(b)] preconds : SpacePrefixSepBy SpecElt,
                       @[scope(b)] body : r,
                       inline? : Option Inline) : Statement =>
  inline? "function " name typeArgs b " : " r indent(2, preconds) " { " body " }";

// Type declaration statement
@[declareScopedType(name, some args)]
op typeDecl_statement (name : Ident, args : Option Bindings) : Statement =>
  "type " name args ";";

op command_axiom (label : Option Label, e : bool) : Command =>
  "axiom " label e ";\n";

op command_distinct (label : Option Label, exprs : CommaSepBy Expr) : Command =>
  "distinct " label "[" exprs "]" ";\n";

// Top-level block command for parsing statements directly
op command_block (b : Block) : Command =>
  b ";\n";

// =====================================================================
// Datatype Syntax Categories
// =====================================================================

// Constructor syntax for datatypes
category Constructor;
category ConstructorList;

@[constructor(name, fields)]
op constructor_mk (name : Ident, fields : Option (CommaSepBy Binding)) :
    Constructor => name "(" fields ")";

@[constructorListAtom(c)]
op constructorListAtom (c : Constructor) : ConstructorList => "\n  " c:0;

@[constructorListPush(cl, c)]
op constructorListPush (cl : ConstructorList, c : Constructor)
    : ConstructorList => cl:0 ",\n  " c:0;

// preRegisterTypes on command_datatypes handles bringing datatype names into
// scope; @[scopeTVar(typeParams)] brings type parameters into scope for constructors.
category DatatypeDecl;

@[declareDatatype(name, typeParams, constructors,
    perConstructor([.datatype, .literal "..is", .constructor],
                   [.datatype], .builtin "bool"),
    perField([.datatype, .literal "..", .field], [.datatype], .fieldType),
    perField([.datatype, .literal "..", .field, .literal "!"], [.datatype], .fieldType))]
op datatype_decl (name : Ident,
                  typeParams : Option Bindings,
                  @[scopeTVar(typeParams)] constructors : ConstructorList)
      : DatatypeDecl =>
      "datatype " name typeParams " {" constructors "\n}";

// Unified datatype command: one or more datatype declarations separated by
// newlines, ending with a semicolon.
@[scope(datatypes), preRegisterTypes(datatypes)]
op command_datatypes (datatypes : NewlineSepBy DatatypeDecl) : Command =>
  datatypes ";\n";

#end

---------------------------------------------------------------------

namespace CoreDDM

#strata_gen Core

end CoreDDM

---------------------------------------------------------------------

end Strata
end
