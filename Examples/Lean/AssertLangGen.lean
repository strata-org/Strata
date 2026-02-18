/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Generate Lean types for an AssertLang dialect (based on the DDM manual).
-- Used to produce trace output for documentation.
import Strata.DDM.Integration.Lean

namespace Strata

#dialect
dialect BoolDialect;
type BoolType;
fn true_lit : BoolType => "true";
fn false_lit : BoolType => "false";
fn not_expr (a : BoolType) : BoolType => "-" a;
fn and (a : BoolType, b : BoolType) : BoolType => @[prec(10), leftassoc] a " && " b;
fn or (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " || " b;
fn imp (a : BoolType, b : BoolType) : BoolType => @[prec(8), leftassoc] a " ==> " b;
fn equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " == " b;
fn not_equal (tp : Type, a : tp, b : tp) : BoolType => @[prec(15)] a " != " b;
#end

#dialect
dialect Arith;
import BoolDialect;
type Int;
fn neg_expr (a : Int) : Int => "- " a;
fn add_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " + " b;
fn sub_expr (a : Int, b : Int) : Int => @[prec(25), leftassoc] a " - " b;
fn mul_expr (a : Int, b : Int) : Int => @[prec(30), leftassoc] a " * " b;
fn exp_expr (a : Int, b : Int) : Int => @[prec(32), rightassoc] a " ^ " b;
fn le (a : Int, b : Int) : BoolType => @[prec(15)] a " <= " b;
fn lt (a : Int, b : Int) : BoolType => @[prec(15)] a " < " b;
fn ge (a : Int, b : Int) : BoolType => @[prec(15)] a " >= " b;
fn gt (a : Int, b : Int) : BoolType => @[prec(15)] a " > " b;
#end

#dialect
dialect AssertLang;
import Arith;
op assert (b : BoolType) : Command => "assert " b ";";
category ArgDecl;
@[declare(var, tp)]
op decl (var : Ident, tp : Type) : ArgDecl => var " : " tp;
category ArgDecls;
op decls (l : CommaSepBy ArgDecl) : ArgDecls => "(" l ")";
@[declareFn(name, args, tp)]
op defFun (name : Ident, args : ArgDecls, tp : Type, @[scope(args)] value : tp)
  : Command => "def " name args "=" value ";";
fn forall_expr (args : ArgDecls, @[scope(args)] b : BoolType) : BoolType =>
  "forall " args ", " b;
fn exists_expr (args : ArgDecls, @[scope(args)] b : BoolType) : BoolType =>
  "exists " args ", " b;
#end

namespace AssertLang

/--
trace: [Strata.generator] Generating AssertLangType
---
trace: [Strata.generator] Generating AssertLangType.toAst
---
trace: [Strata.generator] Generating AssertLangType.ofAst
---
trace: [Strata.generator] Generating ArgDecl
---
trace: [Strata.generator] Generating ArgDecl.toAst
---
trace: [Strata.generator] Generating ArgDecl.ofAst
---
trace: [Strata.generator] Generating ArgDecls
---
trace: [Strata.generator] Generating ArgDecls.toAst
---
trace: [Strata.generator] Generating ArgDecls.ofAst
---
trace: [Strata.generator] Generating Expr
---
trace: [Strata.generator] Generating Expr.toAst
---
trace: [Strata.generator] Generating Expr.ofAst
---
trace: [Strata.generator] Generating Command
---
trace: [Strata.generator] Generating Command.toAst
---
trace: [Strata.generator] Generating Command.ofAst
---
trace: [Strata.generator] Declarations group: [Init.Type]
[Strata.generator] Declarations group: [AssertLang.ArgDecl]
[Strata.generator] Declarations group: [AssertLang.ArgDecls]
[Strata.generator] Declarations group: [Init.Expr]
[Strata.generator] Declarations group: [Init.Command]
-/
#guard_msgs in
set_option trace.Strata.generator true in
#strata_gen AssertLang

end AssertLang
end Strata
