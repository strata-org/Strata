/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

namespace Strata

class IsAST (α : Type _) (M : outParam Type) where
  toAst : α → M
  ofAst : M → OfAstM α

end Strata

#dialect
dialect TestDialect;

category Binding;
@[declare(name, tp)]
op mkBinding (name : Ident, tp : TypeP) : Binding => @[prec(40)] name ":" tp;

category Bindings;
@[scope(bindings)]
op mkBindings (bindings : CommaSepBy Binding) : Bindings => "(" bindings ")";

type bool;
fn trueExpr : bool => "true";
fn and (x : bool, y : bool) : bool => x " && " y;
fn lambda (tp : Type, b : Bindings, @[scope(b)] res : tp) : fnOf(b, tp) => "fun " b " => " res;

type set (a : Type);

category test;
op foo (a : bool) : test => "foo " a;
op identTest (a : Ident): test => "identTest " a;
op numTest (a : Num): test => "numTest " a;
op strTest (a : Str): test => "strTest " a;

category MutA;
category MutB;
op opA (b : MutB) : MutA => "opA " b;
op opB (a : MutA) : MutB => "opB " a;

category MutASeq;
op mkMutASeq (a : Seq MutA) : MutASeq => a;

category MutAOption;
op mkMutAOption (a : Option MutA) : MutAOption => a;

category MutACommaSep;
op mkMutACommaSep (a : CommaSepBy MutA) : MutACommaSep => a;
#end

namespace TestDialect

#strata_gen TestDialect

/--
info: inductive TestDialect.test : Type
number of parameters: 0
constructors:
TestDialect.test.foo : Expr → test
TestDialect.test.identTest : String → test
TestDialect.test.numTest : Nat → test
TestDialect.test.strTest : String → test
-/
#guard_msgs in
#print test

/--
info: inductive TestDialect.MutA : Type
number of parameters: 0
constructors:
TestDialect.MutA.opA : MutB → MutA
-/
#guard_msgs in
#print MutA

/--
info: inductive TestDialect.MutB : Type
number of parameters: 0
constructors:
TestDialect.MutB.opB : MutA → MutB
-/
#guard_msgs in
#print MutB

/--
info: inductive TestDialect.TypeP : Type
number of parameters: 0
constructors:
TestDialect.TypeP.expr : TestDialectType → TypeP
TestDialect.TypeP.type : TypeP
-/
#guard_msgs in
#print TypeP

/--
info: Strata.Expr.fvar 1
-/
#guard_msgs in
#eval Expr.fvar 1 |>.toAst

/--
info: opaque TestDialect.Expr.toAst : Expr → Strata.Expr
-/
#guard_msgs in
#print Expr.toAst

deriving instance DecidableEq for TestDialectType
deriving instance DecidableEq for TypeP
deriving instance DecidableEq for Binding
deriving instance DecidableEq for Bindings
deriving instance DecidableEq for Expr

instance : Strata.IsAST Expr Strata.Expr where
  toAst := Expr.toAst
  ofAst := Expr.ofAst

instance : Strata.IsAST TestDialectType Strata.TypeExpr where
  toAst := TestDialectType.toAst
  ofAst := TestDialectType.ofAst

def testRoundTrip {α M} [h : Strata.IsAST α M] [DecidableEq α] (e : α) : Bool :=
  match e |> Strata.IsAST.toAst |> Strata.IsAST.ofAst with
  | .error _ => false
  | .ok g => e = g

#guard testRoundTrip <| TestDialectType.bool
#guard testRoundTrip <| TestDialectType.set .bool

#guard testRoundTrip <| Expr.trueExpr
#guard testRoundTrip <| Expr.lambda .bool (Bindings.mkBindings #[]) .trueExpr
#guard testRoundTrip <| Expr.fvar 1

open Strata (OfAstM)

/--
info: (((Strata.Expr.fn { dialect := "TestDialect", name := "lambda" }).app
          (Strata.Arg.type (Strata.TypeExpr.ident { dialect := "TestDialect", name := "bool" } (Array.mkEmpty 0)))).app
      (Strata.Arg.op
        { name := { dialect := "TestDialect", name := "mkBindings" },
          args := (Array.mkEmpty 1).push (Strata.Arg.commaSepList (Array.mkEmpty 0)) })).app
  (Strata.Arg.expr (Strata.Expr.fn { dialect := "TestDialect", name := "trueExpr" }))
-/
#guard_msgs in
#eval Expr.lambda .bool (.mkBindings #[]) .trueExpr |>.toAst

end TestDialect
