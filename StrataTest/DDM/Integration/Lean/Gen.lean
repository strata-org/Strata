/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DDM.Integration.Lean

/-!
Tests for `#strata_gen`: exercises empty dialects, a dialect with types,
expressions, and mutual recursion, and verifies round-trip correctness.
-/

namespace Strata

class IsAST (β : Type → Type) (M : outParam (Type → Type)) where
  toAst {α} [Inhabited α] : β α → M α
  ofAst {α} [Inhabited α] [Repr α] : M α → OfAstM (β α)

end Strata

-- Make sure empty dialect works
namespace EmptyD

#dialect
dialect EmptyDialect;
#end


#guard_msgs in
set_option trace.Strata.generator true in
#strata_gen EmptyDialect

end EmptyD


-- Make sure dialect with no types/expres works
namespace EmptyExprD

#dialect
dialect EmptyExprDialect;

op cmd (tp : Type, a : tp) : Command => "cmd " a;

#end


/--
trace: [Strata.generator] Generating EmptyExprDialectType
---
trace: [Strata.generator] Generating EmptyExprDialectType.toAst
---
trace: [Strata.generator] Generating EmptyExprDialectType.ofAst
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
[Strata.generator] Declarations group: [Init.Expr]
[Strata.generator] Declarations group: [Init.Command]
-/
#guard_msgs in
set_option trace.Strata.generator true in
#strata_gen EmptyExprDialect

end EmptyExprD


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
info: private inductive TestDialect.test : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.test.foo : {α : Type} → α → Expr α → test α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.test.identTest : {α : Type} →
  α → Strata.Ann String α → test α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.test.numTest : {α : Type} → α → Strata.Ann Nat α → test α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.test.strTest : {α : Type} → α → Strata.Ann String α → test α

-/
#guard_msgs in
#print test

/--
info: private inductive TestDialect.MutA : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.MutA.opA : {α : Type} → α → MutB α → MutA α
-/
#guard_msgs in
#print MutA

/--
info: private inductive TestDialect.MutB : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.MutB.opB : {α : Type} → α → MutA α → MutB α
-/
#guard_msgs in
#print MutB

/--
info: private inductive TestDialect.TypeP : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TypeP.expr : {α : Type} → TestDialectType α → TypeP α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TypeP.type : {α : Type} → α → TypeP α
-/
#guard_msgs in
#print TypeP

/--
info: Strata.ExprF.fvar () 1
-/
#guard_msgs in
#eval Expr.fvar () 1 |>.toAst

/--
info: private opaque TestDialect.Expr.toAst : {α : Type} → [Inhabited α] → Expr α → Strata.ExprF α
-/
#guard_msgs in
#print Expr.toAst

/--
info: private inductive TestDialect.Expr : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.fvar : {α : Type} → α → Nat → Expr α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.bvar : {α : Type} → α → Nat → Expr α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.app : {α : Type} → α → Expr α → Expr α → Expr α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.trueExpr : {α : Type} → α → Expr α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.and : {α : Type} → α → Expr α → Expr α → Expr α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.Expr.lambda : {α : Type} →
  α → TestDialectType α → Bindings α → Expr α → Expr α
-/
#guard_msgs in
#print Expr

/--
info: private inductive TestDialect.TestDialectType : Type → Type
number of parameters: 1
constructors:
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.bvar : {α : Type} →
  α → Nat → TestDialectType α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.tvar : {α : Type} →
  α → String → TestDialectType α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.fvar : {α : Type} →
  α → Nat → Array (TestDialectType α) → TestDialectType α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.arrow : {α : Type} →
  α → TestDialectType α → TestDialectType α → TestDialectType α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.bool : {α : Type} → α → TestDialectType α
_private.StrataTest.DDM.Integration.Lean.Gen.0.TestDialect.TestDialectType.set : {α : Type} →
  α → TestDialectType α → TestDialectType α
-/
#guard_msgs in
#print TestDialectType

deriving instance BEq for TestDialectType
deriving instance BEq for TypeP
deriving instance BEq for Binding
deriving instance BEq for Bindings
deriving instance BEq for Expr

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
#guard testRoundTrip <|
  Expr.lambda () (.bool ()) (Bindings.mkBindings () ⟨(), #[]⟩) (.trueExpr ())
#guard testRoundTrip <| Expr.fvar () 1
#guard testRoundTrip <| Expr.app () (.fvar () 0) (.trueExpr ())
#guard testRoundTrip <| Expr.app () (.app () (.fvar () 0) (.trueExpr ())) (.fvar () 1)

open Strata (OfAstM)

/--
info: Strata.ExprF.app ()
  (Strata.ExprF.app ()
    (Strata.ExprF.app () (Strata.ExprF.fn () { dialect := "TestDialect", name := "lambda" })
      (Strata.ArgF.type (Strata.TypeExprF.ident () { dialect := "TestDialect", name := "bool" } (Array.mkEmpty 0))))
    (Strata.ArgF.op
      { ann := (), name := { dialect := "TestDialect", name := "mkBindings" },
        args := (Array.mkEmpty 1).push (Strata.ArgF.seq () Strata.SepFormat.comma (Array.mkEmpty 0)) }))
  (Strata.ArgF.expr (Strata.ExprF.fn () { dialect := "TestDialect", name := "trueExpr" }))
-/
#guard_msgs in
#eval Expr.lambda () (.bool ()) (.mkBindings () ⟨(), #[]⟩) (.trueExpr ()) |>.toAst

end TestDialect
