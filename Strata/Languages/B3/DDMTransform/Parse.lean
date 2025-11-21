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

fn ite (c : Expr, t : Expr, f : Expr) : Expression => @[prec(3)] "if " c:0 " then " t:3 " else " f:3;
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

fn functionCall1 (name : Ident, arg1 : Expr) : Expression => @[prec(40)] name "(" arg1:0 ")";
fn functionCall2 (name : Ident, arg1 : Expr, arg2 : Expr) : Expression => @[prec(40)] name "(" arg1:0 ", " arg2:0 ")";

fn forall_expr (var : Ident, ty : Ident, body : Expr) : Expression =>
  @[prec(1)] "forall " var " : " ty " " body:1;

fn exists_expr (var : Ident, ty : Ident, body : Expr) : Expression =>
  @[prec(1)] "exists " var " : " ty " " body:1;

fn forall_expr_1p (var : Ident, ty : Ident, p1 : Expr, body : Expr) : Expression =>
  @[prec(1)] "forall " var " : " ty " pattern " p1:0 ", " body:1;

fn exists_expr_1p (var : Ident, ty : Ident, p1 : Expr, body : Expr) : Expression =>
  @[prec(1)] "exists " var " : " ty " pattern " p1:0 ", " body:1;

fn forall_expr_2p (var : Ident, ty : Ident, p1 : Expr, p2 : Expr, body : Expr) : Expression =>
  @[prec(1)] "forall " var " : " ty " pattern " p1:0 ", pattern " p2:0 ", " body:1;

fn exists_expr_2p (var : Ident, ty : Ident, p1 : Expr, p2 : Expr, body : Expr) : Expression =>
  @[prec(1)] "exists " var " : " ty " pattern " p1:0 ", pattern " p2:0 ", " body:1;

fn forall_expr_3p (var : Ident, ty : Ident, p1 : Expr, p2 : Expr, p3 : Expr, body : Expr) : Expression =>
  @[prec(1)] "forall " var " : " ty " pattern " p1:0 ", pattern " p2:0 ", pattern " p3:0 ", " body:1;

fn exists_expr_3p (var : Ident, ty : Ident, p1 : Expr, p2 : Expr, p3 : Expr, body : Expr) : Expression =>
  @[prec(1)] "exists " var " : " ty " pattern " p1:0 ", pattern " p2:0 ", pattern " p3:0 ", " body:1;

category Statement;

op assign (v : Ident, e : Expr) : Statement => v:0 " := " e "\n";

category CallArg;
op call_arg_expr (e : Expr) : CallArg => e:0;
op call_arg_out (id : Ident) : CallArg => "out " id;
op call_arg_inout (id : Ident) : CallArg => "inout " id;

op call_no_return_2args (proc : Ident, arg1 : CallArg, arg2 : CallArg) : Statement =>
  proc "(" arg1 ", " arg2 ")\n";

op call_1return_2args (ret : Ident, proc : Ident, arg1 : CallArg, arg2 : CallArg) : Statement =>
  ret:0 " := " proc "(" arg1 ", " arg2 ")\n";

op check (c : Expr) : Statement => "check " c "\n";
op assume (c : Expr) : Statement => "assume " c "\n";
op reach (c : Expr) : Statement => "reach " c "\n";
op assert (c : Expr) : Statement => "assert " c "\n";

category Else;
op else_none () : Else => "";
op else_some (s : Statement) : Else => " else " s:40;

op if_statement (c : Expr, t : Statement, f : Else) : Statement =>
  "if " c:0 " " t:40 f;

category Invariant;
op invariant (e : Expr) : Invariant => "\n  invariant " e:0;

op loop_statement (invs : Seq Invariant, body : Statement) : Statement =>
  "loop" invs " " body:40;

op exit_statement (label : Option Ident) : Statement => "exit " label "\n";
op return_statement () : Statement => "return";

op labeled_statement (label : Ident, s : Statement) : Statement => label ": " s;

op probe (name : Ident) : Statement => "probe " name "\n";

category VarInit;
op var_init_none () : VarInit => "";
op var_init_some (e : Expr) : VarInit => " := " e:0;

category AutoInv;
op autoinv_none () : AutoInv => "";
op autoinv_some (e : Expr) : AutoInv => " autoinv " e:0;

op var_decl (name : Ident, ty : Ident, autoinv : AutoInv, init : VarInit) : Statement =>
  "var " name " : " ty autoinv init "\n";

op choose_statement (branch1 : Statement, branch2 : Statement) : Statement =>
  "choose " branch1:40 " or " branch2:40;

category IfCaseBranch;
op if_case_branch (cond : Expr, body : Statement) : IfCaseBranch =>
  "\ncase " cond:0 " " body:40;

op if_case_statement (branches : Seq IfCaseBranch) : Statement =>
  "if" branches;

op aForall_statement (var : Ident, ty : Ident, body : Statement) : Statement =>
  "forall " var " : " ty " " body:40;

op block (c : Seq Statement) : Statement => "{\n" indent(2, c:40) "}\n";

#end

namespace B3DDM

#strata_gen B3

end B3DDM

---------------------------------------------------------------------

end Strata
