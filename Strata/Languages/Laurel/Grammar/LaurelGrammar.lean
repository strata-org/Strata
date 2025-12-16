/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Minimal Laurel dialect for AssertFalse example
import Strata

#dialect
dialect Laurel;

// Types
category LaurelType;
op intType : LaurelType => "int";
op boolType : LaurelType => "bool";

category StmtExpr;

op boolTrue() : StmtExpr => "true";
op boolFalse() : StmtExpr => "false";
op int(n : Num) : StmtExpr => n;

// Variable declarations
op varDecl (name: Ident, value: StmtExpr): StmtExpr => "var " name " := " value ";";
op varDeclTyped (name: Ident, varType: LaurelType): StmtExpr => "var " name ": " varType ";";

// Identifiers/Variables
op identifier (name: Ident): StmtExpr => name;
op parenthesis (inner: StmtExpr): StmtExpr => "(" inner ")";

// Assignment
op assign (target: StmtExpr, value: StmtExpr): StmtExpr => target " := " value ";";

// Binary operators
op add (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(60)] lhs " + " rhs;
op eq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " == " rhs;
op neq (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " != " rhs;
op gt (lhs: StmtExpr, rhs: StmtExpr): StmtExpr => @[prec(40)] lhs " > " rhs;

op call(callee: StmtExpr, args: CommaSepBy StmtExpr): StmtExpr => callee "(" args ")";

// If-else
op ifThenElse (cond: StmtExpr, thenBranch: StmtExpr, elseBranch: StmtExpr): StmtExpr =>
  @[prec(20)] "if (" cond ") " thenBranch:0 " else " elseBranch:0;

// If without else
op ifThen (cond: StmtExpr, thenBranch: StmtExpr): StmtExpr =>
  @[prec(20)] "if (" cond ") " thenBranch:0;

op assert (cond : StmtExpr) : StmtExpr => "assert " cond ";";
op assume (cond : StmtExpr) : StmtExpr => "assume " cond ";";
op return (value : StmtExpr) : StmtExpr => "return " value ";";
op block (stmts : Seq StmtExpr) : StmtExpr => @[prec(1000)] "{\n" stmts "\n}";

category Parameter;
op parameter (name: Ident, paramType: LaurelType): Parameter => name ":" paramType;

category Procedure;
op procedure (name : Ident, body : StmtExpr) : Procedure => "procedure " name "() " body:0;
op procedureWithReturnType (name : Ident, parameters: CommaSepBy Parameter, returnType : LaurelType, body : StmtExpr) : Procedure =>
  "procedure " name "(" parameters "): " returnType " " body:0;

op program (staticProcedures: Seq Procedure): Command => staticProcedures;

#end
