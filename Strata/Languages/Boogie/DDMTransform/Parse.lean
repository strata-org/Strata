/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.Boogie.Boogie

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing Boogie -/

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

category Trigger;
category Triggers;
op trigger (exprs : CommaSepBy Expr) : Trigger =>
  "{" exprs "}";
op triggersAtom (trigger : Trigger) : Triggers =>
  trigger;
op triggersPush (triggers : Triggers, trigger : Trigger) : Triggers =>
  triggers trigger;

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
  "const" name ":" typeArgs r ";\n";

@[declareFn(name, b, r)]
op command_fndecl (name : Ident,
                   typeArgs : Option TypeArgs,
                   @[scope(typeArgs)] b : Bindings,
                   @[scope (typeArgs)] r : Type) : Command =>
  "function" name typeArgs b ":" r ";\n";

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

op command_axiom (label : Option Label, e : bool) : Command => "axiom " label e ";\n";

#end

namespace BoogieDDM

--#strata_gen Boogie

end BoogieDDM

---------------------------------------------------------------------

end Strata
