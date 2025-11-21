/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format
import Strata.Languages.B3.Stmt

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
---------------------------------------------------------------------

/- DDM support for parsing and pretty-printing B3 -/

#dialect
dialect B3;

type Expression;

fn not (e : Expr) : Expression => @[prec(35)] "!" e;

fn natLit (n : Num) : Expression => n;
fn strLit (s : Str) : Expression => s;

fn btrue : Expression => "true";
fn bfalse : Expression => "false";

fn id (name : Ident) : Expression => name;

fn letExpr (name : Ident, value : Expr, body : Expr) : Expression =>
  @[prec(2)] "val " name " := " value:0 " " body:2;

fn labeledExpr (label : Ident, e : Expr) : Expression => @[prec(1)] label ": " e:1;

fn ite (c : Expr, t : Expr, f : Expr) : Expression => @[prec(3)] "if " c:0 " then " indent(2, t:3) " else " indent(2, f:3);
fn iff (a : Expr, b : Expr) : Expression => @[prec(4)] a " <==> " b;
fn implies (a : Expr, b : Expr) : Expression => @[prec(5), rightassoc] a " ==> " b;
fn impliedBy (a : Expr, b : Expr) : Expression => @[prec(5), rightassoc] a " <== " b;
fn and (a : Expr, b : Expr) : Expression => @[prec(10), leftassoc] a " && " b;
fn or (a : Expr, b : Expr) : Expression => @[prec(8), leftassoc] a " || " b;

fn equal (a : Expr, b : Expr) : Expression => @[prec(15)] a " == " b;
fn not_equal (a : Expr, b : Expr) : Expression => @[prec(15)] a " != " b;
fn le (a : Expr, b : Expr) : Expression => @[prec(15)] a " <= " b;
fn lt (a : Expr, b : Expr) : Expression => @[prec(15)] a " < " b;
fn ge (a : Expr, b : Expr) : Expression => @[prec(15)] a " >= " b;
fn gt (a : Expr, b : Expr) : Expression => @[prec(15)] a " > " b;

fn neg (e : Expr) : Expression => "-" e;
fn add (a : Expr, b : Expr) : Expression => @[prec(25), leftassoc] a " + " b;
fn sub (a : Expr, b : Expr) : Expression => @[prec(25), leftassoc] a " - " b;
fn mul (a : Expr, b : Expr) : Expression => @[prec(30), leftassoc] a " * " b;
fn div (a : Expr, b : Expr) : Expression => @[prec(30), leftassoc] a " div " b;
fn mod (a : Expr, b : Expr) : Expression => @[prec(30), leftassoc] a " mod " b;

fn functionCall (name : Ident, args : CommaSepBy Expr) : Expression => @[prec(40)] name "(" args ")";

category Pattern;
op pattern (e : Expr) : Pattern => "pattern " e:0 ", ";

category Patterns;
op patternsAtom (p : Pattern) : Patterns => @[prec(0)] p:0;
op patternsPush (ps : Patterns, p : Pattern) : Patterns => @[prec(0)] ps:0 p:0;

fn forall_expr (var : Ident, ty : Ident, patterns : Option Patterns, body : Expr) : Expression =>
  @[prec(1)] "forall " var " : " ty " " patterns body:1;

fn exists_expr (var : Ident, ty : Ident, patterns : Option Patterns, body : Expr) : Expression =>
  @[prec(1)] "exists " var " : " ty " " patterns body:1;

category Statement;

op assign (v : Ident, e : Expr) : Statement => "\n" v:0 " := " e:0;

category CallArg;
op call_arg_expr (e : Expr) : CallArg => e:0;
op call_arg_out (id : Ident) : CallArg => "out " id:0;
op call_arg_inout (id : Ident) : CallArg => "inout " id:0;

op call_statement (proc : Ident, args : CommaSepBy CallArg) : Statement =>
  "\n" proc "(" args ")";

op check (c : Expr) : Statement => "\ncheck " c:0;
op assume (c : Expr) : Statement => "\nassume " c:0;
op reach (c : Expr) : Statement => "\nreach " c:0;
op assert (c : Expr) : Statement => "\nassert " c:0;

category Else;
op else_none () : Else => "";
op else_some (s : Statement) : Else => @[prec(0)] "\nelse " indent(2, s:0);

op if_statement (c : Expr, t : Statement, f : Else) : Statement =>
  "if " c:0 " " indent(2, t:0) f:0;

category Invariant;
op invariant (e : Expr) : Invariant => "\n  invariant " e:0;

op loop_statement (invs : Seq Invariant, body : Statement) : Statement =>
  "loop" invs " " body:40;

op exit_statement (label : Option Ident) : Statement => "\nexit " label:0 ;
op return_statement () : Statement => "\nreturn";

op labeled_statement (label : Ident, s : Statement) : Statement => label:0 ": " s:0;

op probe (name : Ident) : Statement => "\nprobe " name:0 ;

category VarInit;
op var_init_none () : VarInit => "";
op var_init_some (e : Expr) : VarInit => " := " e:0;

category AutoInv;
op autoinv_none () : AutoInv => "";
op autoinv_some (e : Expr) : AutoInv => " autoinv " e:0;

op var_decl (name : Ident, ty : Ident, autoinv : AutoInv, init : VarInit) : Statement =>
  "\nvar " name " : " ty autoinv:0 init:0 ;

category ChoiceBranch;
op choice_branch (s : Statement) : ChoiceBranch => s:40;

category ChoiceBranches;
op choiceAtom (b : ChoiceBranch) : ChoiceBranches => b:0;
op choicePush (bs : ChoiceBranches, b : ChoiceBranch) : ChoiceBranches => bs:0 " or " b:0;

op choose_statement (branches : ChoiceBranches) : Statement =>
  "choose " branches:0;

category IfCaseBranch;
op if_case_branch (cond : Expr, body : Statement) : IfCaseBranch =>
  "\ncase " cond:0 " " body:40;

op if_case_statement (branches : Seq IfCaseBranch) : Statement =>
  "if" branches:0;

op aForall_statement (var : Ident, ty : Ident, body : Statement) : Statement =>
  "forall " var:0 " : " ty:0 " " body:40;

op block (c : Seq Statement) : Statement => "\n{" indent(2, c:0) "\n}";

#end

namespace B3DDM

#strata_gen B3

end B3DDM

---------------------------------------------------------------------

end Strata
