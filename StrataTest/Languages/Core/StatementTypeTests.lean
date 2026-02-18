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
info: ok: {
  init (x : int) := (xinit : int)
  x := (xinit : int)
  init (y : int) := (xinit : int)
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext {types := [[("xinit", t[int])]] })
                   Program.init
                   none
                   [.init "x" t[int] (some eb[xinit]),
                    .set "x" eb[xinit],
                    .init "y" t[∀α. %α] (some eb[xinit])]
         return format ans.fst


/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("x", t[bool])]] })
                   Program.init
                   none
                   [
                    .init "x" t[bool] (some eb[#true])
                   ]
         return format ans

/--
info: ok: context:
types:   [(zinit, bool) (x, int) (y, int)]
aliases: []
state:
tyGen: 1
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst:
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("zinit", t[bool])]] })
                    Program.init
                    none
                    [
                    .init "x" t[int] (some eb[#0]),
                    .init "y" t[int] (some eb[#6]),
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

/-- info: error: Impossible to unify bool with int. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (some eb[#0]),
                    .init "y" t[int] (some eb[#6]),
                    .init "z" t[bool] (some eb[if (x == y) then #true else #2])
                    ]
          return format ans

/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[bool] (some eb[#true]),
                    .block "label_0"
                      [ Statement.init "x" t[int] (some eb[#1]) ]
                    ]
          return format ans

/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 2
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst: [($__ty0, int)]
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (some eb[#0]),
                    .ite eb[x == #3]
                    [
                      Statement.init "y" t[∀α. %α] (some eb[x]),
                      Statement.assert "local_y_eq_3" eb[y == #3]
                    ]
                    [ Statement.init "z" t[bool] (some eb[#true]) ]
                    ]
          return format ans.snd

/--
info: ok: {
  init (x : int) := #1
  x := #2
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
              [
              .init "x" t[∀a. %a] (some eb[#1]),
              .set "x" eb[#2]
              ]
          return (format ans.fst)

/--
info: ok: context:
types:   [(fn, ∀[a]. (arrow a a)) (m1, (arrow int int)) (m2, (arrow (arrow bool int) int))]
aliases: []
state:
tyGen: 10
tyPrefix: $__ty
exprGen: 1
exprPrefix: $__var
subst: [($__ty0, int) ($__ty2, int) ($__ty6, (arrow bool int)) ($__ty7, bool) ($__ty5, (arrow bool int)) ($__ty3, (arrow bool int)) ($__ty9, int)]
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("fn", t[∀a. %a → %a])]] })
                      Program.init none
              [
              .init "m1" t[∀a. %a → int] (some eb[fn]), -- var m : <a>[a]int
              .init "m2" t[∀a. %a → int] (some eb[(λ (%0 (fn #true)))]),
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
    .init "y" t[int] (some eb[(~identity #5)]),  -- Call the declared function
    .assert "y_eq_5" eb[y == #5]
  ]

/--
info: ok: {
  funcDecl <function>
  init (y : int) := ((~identity : (arrow int int)) #5)
  assert [y_eq_5] ((y : int) == #5)
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none testFuncDeclTypeCheck
         return format ans.fst

end FuncDeclTests

end Core
