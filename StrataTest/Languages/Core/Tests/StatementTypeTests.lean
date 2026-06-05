/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.StatementType

meta section

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)

open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: ok: {
  var x : int := xinit;
  x := xinit;
  var y : int := xinit;
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext {types := [[("xinit", t[int])]] })
                   Program.init
                   none
                   [.init "x" t[int] (.det eb[xinit]) .empty,
                    .set "x" eb[xinit] .empty,
                    .init "y" t[∀α. %α] (.det eb[xinit]) .empty]
         return format ans.fst


/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("x", t[bool])]] })
                   Program.init
                   none
                   [
                    .init "x" t[bool] (.det eb[#true]) .empty
                   ]
         return format ans

/--
info: ok: context:
types:   [(zinit, bool) (x, int) (y, int)]
aliases: []
state:
tyGen: 0
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
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .init "y" t[int] (.det eb[#6]) .empty,
                    .block "label_0"

                      [Statement.init "z" t[bool] (.det eb[zinit]) .empty,
                       Statement.assume "z_false" eb[z == #false] .empty,

                      .ite (.det eb[z == #false])
                        [Statement.set "x" eb[y] .empty]
                        [Statement.assert "trivial" eb[#true] .empty]
                        .empty,

                      Statement.assert "x_eq_y_label_0" eb[x == y] .empty,
                      ]
                      .empty,
                    .assert "x_eq_y" eb[x == y] .empty
                    ]
          return format ans.snd

/-- info: error: Impossible to unify bool with int. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .init "y" t[int] (.det eb[#6]) .empty,
                    .init "z" t[bool] (.det eb[if (x == y) then #true else #2]) .empty
                    ]
          return format ans

/-- info: error: Variable x of type bool already in context. -/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[bool] (.det eb[#true]) .empty,
                    .block "label_0"
                      [ Statement.init "x" t[int] (.det eb[#1]) .empty ]
                      .empty
                    ]
          return format ans

/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 1
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst: [($__ty0, int)]
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .ite (.det eb[x == #3])
                    [
                      Statement.init "y" t[∀α. %α] (.det eb[x]) .empty,
                      Statement.assert "local_y_eq_3" eb[y == #3] .empty
                    ]
                    [ Statement.init "z" t[bool] (.det eb[#true]) .empty ]
                    .empty
                    ]
          return format ans.snd

/--
info: ok: {
  var x : int := 1;
  x := 2;
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
              [
              .init "x" t[∀a. %a] (.det eb[#1]) .empty,
              .set "x" eb[#2] .empty
              ]
          return (format ans.fst)

/--
info: ok: context:
types:   [(fn, ∀[a]. (arrow a a)) (m1, (arrow int int)) (m2, (arrow (arrow bool int) int))]
aliases: []
state:
tyGen: 8
tyPrefix: $__ty
exprGen: 1
exprPrefix: $__var
subst: [($__ty0, int) ($__ty1, int) ($__ty4, (arrow bool int)) ($__ty5, bool) ($__ty3, (arrow bool int)) ($__ty2, (arrow bool int)) ($__ty7, int)]
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default (TEnv.default.updateContext { types := [[("fn", t[∀a. %a → %a])]] })
                      Program.init none
              [
              .init "m1" t[∀a. %a → int] (.det eb[fn]) .empty, -- var m : <a>[a]int
              .init "m2" t[∀a. %a → int] (.det eb[(λ (%0 (fn #true)))]) .empty,
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
    name := ⟨"identity", ()⟩,
    typeArgs := [],
    isConstr := false,
    inputs := [(⟨"x", ()⟩, .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[x],  -- Simple identity function
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl identityFunc .empty,
    .init "y" t[int] (.det eb[(~identity #5)]) .empty,  -- Call the declared function
    .assert "y_eq_5" eb[y == #5] .empty
  ]

/--
info: ok: {
  funcDecl <function>
  var y : int := identity(5);
  ⏎
  -- Errors encountered during conversion:
  Unsupported construct in handleUnaryOps: unknown operation, rendering as generic call: identity
  Context: Global scope:
  assert [y_eq_5]: y == 5;
}
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none testFuncDeclTypeCheck
         return format ans.fst

-- Regression test for #1289: outer type variable captured in local function body.
def testOuterTyVarCapture : List Statement :=
  let localFunc : PureFunc Expression := {
    name := ⟨"f", ()⟩,
    typeArgs := ["b"],
    isConstr := false,
    inputs := [(⟨"y", ()⟩, .forAll [] (.ftvar "b"))],
    output := .forAll [] (.ftvar "b"),
    body := some (.app () (.abs () "z" (some (.ftvar "a")) (.bvar () 0))
                          (.fvar () ⟨"y", ()⟩ none)),
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [.funcDecl localFunc .empty]

/--
info: error: Function 'f': body contains undeclared type variables [a] (not in typeArgs [b])
-/
#guard_msgs in
#eval do
  -- "a" is in the outer context as a type variable (simulating a polymorphic procedure)
  let Env := TEnv.default.updateContext {types := [[("x", .forAll ["a"] (.ftvar "a"))]]}
  let ans ← typeCheck LContext.default Env Program.init none testOuterTyVarCapture
  return format ans.fst

end FuncDeclTests

section NondetCondTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (ExprOrNondet)

-- Type checking a nondet if: both branches should type-check
/--
info: ok: context:
types:   [(x, int)]
aliases: []
state:
tyGen: 0
tyPrefix: $__ty
exprGen: 0
exprPrefix: $__var
subst:
-/
#guard_msgs in
#eval do let ans ← typeCheck LContext.default TEnv.default Program.init none
                    [
                    .init "x" t[int] (.det eb[#0]) .empty,
                    .ite .nondet
                      [Statement.set "x" eb[#1] .empty]
                      [Statement.set "x" eb[#2] .empty]
                      .empty,
                    .assert "x_pos" eb[(x == x)] .empty
                    ]
         return format ans.snd

end NondetCondTests

section CallOutArgTests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (ExprOrNondet)

/-- A test procedure: `procedure Foo(inout x: int, out y: int)` -/
private def testProc : Procedure :=
  { header := {
      name := ⟨"Foo", ()⟩,
      typeArgs := [],
      inputs := [(⟨"x", ()⟩, .int)],
      outputs := [(⟨"x", ()⟩, .int), (⟨"y", ()⟩, .int)] },
    spec := { preconditions := [], postconditions := [] },
    body := [] }

private def testProgram : Program :=
  { decls := [.proc testProc .empty] }

-- Passing `x == x` (which contains output variable `x` inside an expression) should fail.
/--
info: error: [call Foo(x == x, out x, out y);]: In-out arguments (parameters appearing in both inputs and outputs) must be simple variable references
-/
#guard_msgs in
#eval do
  let env := TEnv.default.updateContext { types := [[("x", t[int]), ("y", t[int])]] }
  let ans ← typeCheck LContext.default env testProgram none
    [.cmd (.call "Foo" [.inArg eb[x == x], .outArg ⟨"x", ()⟩, .outArg ⟨"y", ()⟩] .empty)]
  return format ans

-- Passing a bare variable `x` as an inout argument should succeed.
/-- info: ok: () -/
#guard_msgs in
#eval do
  let env := TEnv.default.updateContext { types := [[("x", t[int]), ("y", t[int])]] }
  let _ ← typeCheck LContext.default env testProgram none
    [.cmd (.call "Foo" [.inArg eb[x], .outArg ⟨"x", ()⟩, .outArg ⟨"y", ()⟩] .empty)]
  return format ()

end CallOutArgTests

end Core

end
