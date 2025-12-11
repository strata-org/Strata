/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Minimal Laurel dialect for AssertFalse example
import Strata

#dialect
dialect Laurel;


// Boolean literals
type bool;
fn boolTrue : bool => "true";
fn boolFalse : bool => "false";

category StmtExpr;
op literalBool (b: bool): StmtExpr => b;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";\n";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";\n";
op block (stmts : Seq StmtExpr) : StmtExpr => @[prec(1000)] "{\n" stmts "}\n";

category Procedure;
op procedure (name : Ident, body : StmtExpr) : Procedure => "procedure " name "() " body:0;

op program (staticProcedures: Seq Procedure): Command => staticProcedures;

#end
