/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean

namespace Strata

class IsAST (β : Type → Type) (M : outParam (Type → Type)) where
  toAst [Inhabited α] : β α → M α
  ofAst [Inhabited α] [Repr α] : M α → OfAstM (β α)

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
info: inductive TestDialect.test : Type → Type
number of parameters: 1
constructors:
TestDialect.test.foo : {α : Type} → α → Expr α → test α
TestDialect.test.identTest : {α : Type} → α → Strata.Ann String α → test α
TestDialect.test.numTest : {α : Type} → α → Strata.Ann Nat α → test α
TestDialect.test.strTest : {α : Type} → α → Strata.Ann String α → test α

-/
#guard_msgs in
#print test

/--
info: inductive TestDialect.MutA : Type → Type
number of parameters: 1
constructors:
TestDialect.MutA.opA : {α : Type} → α → MutB α → MutA α
-/
#guard_msgs in
#print MutA

/--
info: inductive TestDialect.MutB : Type → Type
number of parameters: 1
constructors:
TestDialect.MutB.opB : {α : Type} → α → MutA α → MutB α
-/
#guard_msgs in
#print MutB

/--
info: inductive TestDialect.TypeP : Type → Type
number of parameters: 1
constructors:
TestDialect.TypeP.expr : {α : Type} → TestDialectType α → TypeP α
TestDialect.TypeP.type : {α : Type} → α → TypeP α
-/
#guard_msgs in
#print TypeP

/--
info: Strata.ExprF.fvar () 1
-/
#guard_msgs in
#eval Expr.fvar () 1 |>.toAst

/--
info: opaque TestDialect.Expr.toAst : {α : Type} → [Inhabited α] → Expr α → Strata.ExprF α
-/
#guard_msgs in
#print Expr.toAst

deriving instance DecidableEq for TestDialectType
deriving instance DecidableEq for TypeP
deriving instance DecidableEq for Binding
deriving instance DecidableEq for Bindings
deriving instance DecidableEq for Expr

instance : Strata.IsAST Expr Strata.ExprF where
  toAst := Expr.toAst
  ofAst := Expr.ofAst

instance : Strata.IsAST TestDialectType Strata.TypeExprF where
  toAst := TestDialectType.toAst
  ofAst := TestDialectType.ofAst

def testRoundTrip {β M} [h : Strata.IsAST β M] [BEq (β Unit)] (e : β Unit) : Bool :=
  match e |> Strata.IsAST.toAst |> Strata.IsAST.ofAst with
  | .error _ => false
  | .ok g => e == g

#guard testRoundTrip <| TestDialectType.bool ()
#guard testRoundTrip <| TestDialectType.set () (.bool ())

#guard testRoundTrip <| Expr.trueExpr ()
#guard testRoundTrip <| Expr.lambda () (.bool ()) (Bindings.mkBindings () ⟨(), #[]⟩) (.trueExpr ())
#guard testRoundTrip <| Expr.fvar () 1

open Strata (OfAstM)

/--
info: Strata.ExprF.app ()
  (Strata.ExprF.app ()
    (Strata.ExprF.app () (Strata.ExprF.fn () { dialect := "TestDialect", name := "lambda" })
      (Strata.ArgF.type (Strata.TypeExprF.ident () { dialect := "TestDialect", name := "bool" } (Array.mkEmpty 0))))
    (Strata.ArgF.op
      { ann := (), name := { dialect := "TestDialect", name := "mkBindings" },
        args := (Array.mkEmpty 1).push (Strata.ArgF.commaSepList () (Array.mkEmpty 0)) }))
  (Strata.ArgF.expr (Strata.ExprF.fn () { dialect := "TestDialect", name := "trueExpr" }))
-/
#guard_msgs in
#eval Expr.lambda () (.bool ()) (.mkBindings () ⟨(), #[]⟩) (.trueExpr ()) |>.toAst

end TestDialect
