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

category Statement;

op assign (v : Ident, e : Expr) : Statement => v:0 " := " e "\n";

op check (c : Expr) : Statement => "check " c "\n";
op assume (c : Expr) : Statement => "assume " c "\n";
op reach (c : Expr) : Statement => "reach " c "\n";
op assert (c : Expr) : Statement => "assert " c "\n";

category Else;
op else_none () : Else => "";
op else_some (s : Statement) : Else => " else " s;

op if_statement (c : Expr, t : Statement, f : Else) : Statement =>
  "if " c " " t f;

category Invariant;
op invariant (e : Expr) : Invariant => "\n  invariant " e;

op loop_statement (invs : Seq Invariant, body : Statement) : Statement =>
  "loop" invs " " body;

op exit_statement (label : Option Ident) : Statement => "exit " label "\n";
op return_statement () : Statement => "return";

op block (c : Seq Statement) : Statement => "{\n" indent(2, c:40) "}\n";

#end

namespace B3DDM

#strata_gen B3

end B3DDM

---------------------------------------------------------------------

end Strata
