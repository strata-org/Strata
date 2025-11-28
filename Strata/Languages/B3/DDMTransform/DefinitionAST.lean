/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.DDM.Util.Format

---------------------------------------------------------------------

namespace Strata

---------------------------------------------------------------------
-- B3AST DDM Dialect for Abstract Syntax Tree
---------------------------------------------------------------------

#dialect
dialect B3AST;

category Literal;
category Expression;
category Pattern;
category BinaryOp;
category UnaryOp;
category QuantifierKind;

op intLit (n : Num) : Literal => n;
op boolLit (b : Bool) : Literal => b;
op stringLit (s : Str) : Literal => s;

op iff : BinaryOp => "iff";
op implies : BinaryOp => "implies";
op impliedBy : BinaryOp => "impliedBy";
op and : BinaryOp => "and";
op or : BinaryOp => "or";
op eq : BinaryOp => "eq";
op neq : BinaryOp => "neq";
op lt : BinaryOp => "lt";
op le : BinaryOp => "le";
op ge : BinaryOp => "ge";
op gt : BinaryOp => "gt";
op add : BinaryOp => "add";
op sub : BinaryOp => "sub";
op mul : BinaryOp => "mul";
op div : BinaryOp => "div";
op mod : BinaryOp => "mod";

op not : UnaryOp => "not";
op neg : UnaryOp => "neg";

op forall : QuantifierKind => "forall";
op exists : QuantifierKind => "exists";

op literal (val : Literal) : Expression => "#" val;
op id (index : Num) : Expression => index;
op ite (cond : Expression, thn : Expression, els : Expression) : Expression =>
  "ite " cond " " thn " " els;
op binaryOp (binOp : BinaryOp, lhs : Expression, rhs : Expression) : Expression =>
  "binop " binOp " " lhs " " rhs;
op unaryOp (unOp : UnaryOp, arg : Expression) : Expression =>
  "unop " unOp " " arg;
op functionCall (fnName : Ident, args : CommaSepBy Expression) : Expression =>
  "call " fnName " (" args ")";
op labeledExpr (label : Ident, expr : Expression) : Expression =>
  "labeled " label " " expr;
op letExpr (var : Ident, value : Expression, body : Expression) : Expression =>
  "let " var " = " value " in " body;
op quantifierExpr (quantifier : QuantifierKind, var : Ident, ty : Ident, patterns : Seq Pattern, body : Expression) : Expression =>
  "quant " quantifier " " var " : " ty " [" patterns "] " body;

op pattern (exprs : CommaSepBy Expression) : Pattern =>
  "pattern (" exprs ")";

category Statement;
category CallArg;
category OneIfCase;

op varDecl (name : Ident, ty : Option Ident, autoinv : Option Expression, init : Option Expression) : Statement =>
  "varDecl " name " : " ty " autoinv " autoinv " := " init;
op assign (lhs : Num, rhs : Expression) : Statement =>
  "assign @" lhs " := " rhs;
op reinit (name : Num) : Statement =>
  "reinit @" name;
op blockStmt (stmts : Seq Statement) : Statement =>
  "block {" stmts "}";
op call (procName : Ident, args : Seq CallArg) : Statement =>
  "call " procName "(" args ")";
op check (expr : Expression) : Statement =>
  "check " expr;
op assume (expr : Expression) : Statement =>
  "assume " expr;
op reach (expr : Expression) : Statement =>
  "reach " expr;
op assert (expr : Expression) : Statement =>
  "assert " expr;
op aForall (var : Ident, ty : Ident, body : Statement) : Statement =>
  "forall " var " : " ty " " body;
op choose (branches : Seq Statement) : Statement =>
  "choose " branches;
op ifStmt (cond : Expression, thenBranch : Statement, elseBranch : Option Statement) : Statement =>
  "if " cond " then " thenBranch " else " elseBranch;
op oneIfCase (cond : Expression, body : Statement): OneIfCase =>
  "oneIfCase " cond body;
op ifCase (cases : Seq OneIfCase) : Statement =>
  "ifcase " cases;
op loop (invariants : Seq Expression, body : Statement) : Statement =>
  "loop invariants " invariants " {" body "}";
op labeledStmt (label : Ident, stmt : Statement) : Statement =>
  "labelStmt " label " " stmt;
op exit (label : Option Ident) : Statement =>
  "exit " label;
op returnStmt : Statement =>
  "return";
op probe (label : Ident) : Statement =>
  "probe " label;

op callArgExpr (e : Expression) : CallArg =>
  "expr " e;
op callArgOut (id : Ident) : CallArg =>
  "out " id;
op callArgInout (id : Ident) : CallArg =>
  "inout " id;

category ParamMode;
category FParameter;
category PParameter;
category Spec;
category Decl;

op paramModeIn : ParamMode => "in";
op paramModeOut : ParamMode => "out";
op paramModeInout : ParamMode => "inout";

op fParameter (injective : Bool, name : Ident, ty : Ident) : FParameter =>
  "fparam " injective " " name " : " ty;

op pParameter (mode : ParamMode, name : Ident, ty : Ident, autoinv : Option Expression) : PParameter =>
  "pparam " mode " " name " : " ty " autoinv " autoinv;

op specRequires (expr : Expression) : Spec =>
  "requires " expr;
op specEnsures (expr : Expression) : Spec =>
  "ensures " expr;

op typeDecl (name : Ident) : Decl =>
  "type " name;
op tagger (name : Ident, forType : Ident) : Decl =>
  "tagger " name " for " forType;

category When;
op when (cond: Expression): When =>
  "when " cond;

category FunctionBody;
op functionBody (whens: Seq When, body: Expression): FunctionBody =>
  whens "{" body "}";

op function (name : Ident, params : Seq FParameter, resultType : Ident, tag : Option Ident, body : Option FunctionBody) : Decl =>
  "\nfunction " name " (" params ") : " resultType " tag " tag " body " body;

op axiom (explains : Seq Ident, expr : Expression) : Decl =>
  "\naxiom explains " explains "," expr;

op procedure (name : Ident, params : Seq PParameter, specs : Seq Spec, body : Option Statement) : Decl =>
  "\nprocedure " name " (" params ") specs " specs " body " body;

#end

namespace B3AST

#strata_gen B3AST

end B3AST
