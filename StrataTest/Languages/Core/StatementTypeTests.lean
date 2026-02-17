/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.StatementType

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)

open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
error: Application type mismatch: The argument
  LExpr.fvar () (CoreIdent.unres "xinit") none
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.fvar () (CoreIdent.unres "xinit") none)
---
error: Application type mismatch: The argument
  LExpr.fvar () (CoreIdent.unres "xinit") none
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "y";
    CoreIdent.unres s)
    (LTy.forAll ["α"] (LMonoTy.ftvar "α")) (LExpr.fvar () (CoreIdent.unres "xinit") none)
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext {types := [[("xinit", t[int])]] })
                   Program.init
                   none
                   [.init "x" t[int] eb[xinit],
                    .set "x" eb[xinit],
                    .init "y" t[∀α. %α] eb[xinit]]
         return format ans.fst


/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.boolConst true)
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "bool" [])) (LExpr.const () (LConst.boolConst true))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("x", t[bool])]] })
                   Program.init
                   none
                   [
                    .init "x" t[bool] eb[#true]
                   ]
         return format ans

/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 0))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.const () (LConst.intConst (Int.ofNat 0)))
---
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 6))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "y";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.const () (LConst.intConst (Int.ofNat 6)))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("zinit", t[bool])]] })
                    Program.init
                    none
                    [
                    .init "x" t[int] eb[#0],
                    .init "y" t[int] eb[#6],
                    .block "label_0"

                      [Statement.init "z" t[bool] (some eb[zinit]),
                       Statement.assume "z_false" eb[z == #false],

                      .ite eb[z == #false]
                        [Statement.set "x" eb[y]]
                        [Statement.assert "trivial" eb[#true]],

                      Statement.assert "x_eq_y_label_0" eb[x == y],
                      ],
                    .assert "x_eq_y" eb[x == y]
                    ]
          return format ans.snd

/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 0))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.const () (LConst.intConst (Int.ofNat 0)))
---
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 6))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "y";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.const () (LConst.intConst (Int.ofNat 6)))
---
error: Application type mismatch: The argument
  LExpr.ite () (LExpr.eq () (LExpr.fvar () (CoreIdent.unres "x") none) (LExpr.fvar () (CoreIdent.unres "y") none))
    (LExpr.const () (LConst.boolConst true)) (LExpr.const () (LConst.intConst (Int.ofNat 2)))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "z";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "bool" []))
    (LExpr.ite () (LExpr.eq () (LExpr.fvar () (CoreIdent.unres "x") none) (LExpr.fvar () (CoreIdent.unres "y") none))
      (LExpr.const () (LConst.boolConst true)) (LExpr.const () (LConst.intConst (Int.ofNat 2))))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] eb[#0],
                    .init "y" t[int] eb[#6],
                    .init "z" t[bool] eb[if (x == y) then #true else #2]
                    ]
          return format ans

/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.boolConst true)
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "bool" [])) (LExpr.const () (LConst.boolConst true))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[bool] eb[#true],
                    .block "label_0"
                      [ Statement.init "x" t[int] (some eb[#1]) ]
                    ]
          return format ans

/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 0))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll [] (LMonoTy.tcons "int" [])) (LExpr.const () (LConst.intConst (Int.ofNat 0)))
---
error: Application type mismatch: The argument
  LExpr.fvar () (CoreIdent.unres "x") none
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "y";
    CoreIdent.unres s)
    (LTy.forAll ["α"] (LMonoTy.ftvar "α")) (LExpr.fvar () (CoreIdent.unres "x") none)
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] eb[#0],
                    .ite eb[x == #3]
                    [
                      Statement.init "y" t[∀α. %α] eb[x],
                      Statement.assert "local_y_eq_3" eb[y == #3]
                    ]
                    [ Statement.init "z" t[bool] (some eb[#true]) ]
                    ]
          return format ans.snd

/--
error: Application type mismatch: The argument
  LExpr.const () (LConst.intConst (Int.ofNat 1))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "x";
    CoreIdent.unres s)
    (LTy.forAll ["a"] (LMonoTy.ftvar "a")) (LExpr.const () (LConst.intConst (Int.ofNat 1)))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
              [
              .init "x" t[∀a. %a] eb[#1],
              .set "x" eb[#2]
              ]
          return (format ans.fst)

/--
error: Application type mismatch: The argument
  LExpr.fvar () (CoreIdent.unres "fn") none
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "m1";
    CoreIdent.unres s)
    (LTy.forAll ["a"] (LMonoTy.tcons "arrow" [LMonoTy.ftvar "a", LMonoTy.tcons "int" []]))
    (LExpr.fvar () (CoreIdent.unres "fn") none)
---
error: Application type mismatch: The argument
  LExpr.absUntyped ()
    (LExpr.app () (LExpr.bvar () 0)
      (LExpr.app () (LExpr.fvar () (CoreIdent.unres "fn") none) (LExpr.const () (LConst.boolConst true))))
has type
  LExpr { Metadata := CoreExprMetadata, IDMeta := Visibility }.mono
but is expected to have type
  Option Expression.Expr
in the application
  @init
    (have s := "m2";
    CoreIdent.unres s)
    (LTy.forAll ["a"] (LMonoTy.tcons "arrow" [LMonoTy.ftvar "a", LMonoTy.tcons "int" []]))
    (LExpr.absUntyped ()
      (LExpr.app () (LExpr.bvar () 0)
        (LExpr.app () (LExpr.fvar () (CoreIdent.unres "fn") none) (LExpr.const () (LConst.boolConst true)))))
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("fn", t[∀a. %a → %a])]] })
                      Program.init none
              [
              .init "m1" t[∀a. %a → int] eb[fn], -- var m : <a>[a]int
              .init "m2" t[∀a. %a → int] eb[(λ (%0 (fn #true)))],
              ]
          return (format ans.snd)

end Tests

---------------------------------------------------------------------

section FuncDeclTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
Test funcDecl type checking: declare a function and call it in a subsequent statement.
The function should be added to the type context so the call can be type-checked.
-/
def testFuncDeclTypeCheck : List Statement :=
  let identityFunc : PureFunc Expression := {
    name := CoreIdent.unres "identity",
    typeArgs := [],
    isConstr := false,
    inputs := [(CoreIdent.unres "x", .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[x],  -- Simple identity function
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl identityFunc,
    .init "y" t[int] eb[(~identity #5)],  -- Call the declared function
    .assert "y_eq_5" eb[y == #5]
  ]

/--
error: aborting evaluation since the expression depends on the 'sorry' axiom, which can lead to runtime instability and crashes.

To attempt to evaluate anyway despite the risks, use the '#eval!' command.
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none testFuncDeclTypeCheck
         return format ans.fst

end FuncDeclTests

end Core
