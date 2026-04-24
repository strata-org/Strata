/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core

namespace Core

---------------------------------------------------------------------

section Tests
open Std (ToFormat Format format)
open Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax

def bad_prog : Program := { decls := [
      -- type Foo a b;
      .type (.con { name := "Foo", params := ["a", "b"]}) .empty,
      -- type FooAlias a = Foo bool bool;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo bool bool]}) .empty,
      -- const fooAliasVal : FooAlias bool;
      .func { name := "fooAliasVal", inputs := [], output := mty[FooAlias bool]} .empty,
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]} .empty,
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)] .empty
              ]
      } .empty
]}

/--
info: error: Impossible to unify (Foo bool bool) with (Foo int bool).
First mismatch: bool with int.
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default bad_prog
         return (format ans)

def good_prog : Program := { decls := [
      -- type Foo a b;
      .type (.con { name := "Foo", params := ["a", "b"]}) .empty,
      -- type FooAlias a = Foo int bool;
      .type (.syn { name := "FooAlias", typeArgs := ["a"], type := mty[Foo int bool]}) .empty,
      -- const fooAliasVal : ∀α. FooAlias α;
      .func { name := "fooAliasVal", typeArgs := ["α"], inputs := [], output := mty[FooAlias α]} .empty,
      -- const fooVal : Foo int bool;
      .func { name := "fooVal", inputs := [], output := mty[Foo int bool]} .empty,
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [],
                         outputs := [] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.assert "test" eb[(~fooAliasVal == ~fooVal)] .empty
              ]
      } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: test
Property: assert
Obligation:
fooAliasVal == fooVal

---
info: ok: program Core;

type Foo (a : Type, b : Type);
type FooAlias (a : Type) := Foo int bool;
function fooAliasVal () : Foo int bool;
function fooVal () : Foo int bool;
procedure $obl_0 ()
{
  assert [test]: fooAliasVal == fooVal;
};
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default good_prog
         return (format ans)

---------------------------------------------------------------------

def outOfScopeVarProg : Program := { decls := [
      .proc { header := {name := "P",
                         typeArgs := [],
                         inputs := [("x", mty[bool])],
                         outputs := [("y", mty[bool])] },
              spec := {
                  preconditions := [],
                  postconditions := [] },
              body := [
                Statement.set "y" eb[((~Bool.Or x) x)] .empty,
                .ite (.det eb[(x == #true)])
                  [Statement.init "q" t[int] (.det eb[#0]) .empty,
                           Statement.set "q" eb[#1] .empty,
                           Statement.set "y" eb[#true] .empty]
                  [Statement.init "q" t[int] (.det eb[#0]) .empty,
                           Statement.set "q" eb[#2] .empty,
                           Statement.set "y" eb[#true] .empty]
                  .empty,
                Statement.assert "y_check" eb[y == #true] .empty,
                Statement.assert "q_check" eb[q == #1] .empty
              ]
      } .empty
]}

/--
info: error: [assert [q_check] (q == #1)] No free variables are allowed here!
Free Variables: [q]
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default outOfScopeVarProg
         return (format ans)

---------------------------------------------------------------------

def polyFuncProg : Program := { decls := [
  -- function identity<a>(x : a) : a;
  .func { name := "identity",
          typeArgs := ["a"],
          inputs := [("x", .ftvar "a")],
          output := .ftvar "a" } .empty,
  -- function makePair<a, b>(x : a, y : b) : Map a b;
  .func { name := "makePair",
          typeArgs := ["a", "b"],
          inputs := [("x", .ftvar "a"), ("y", .ftvar "b")],
          output := .tcons "Map" [.ftvar "a", .ftvar "b"] } .empty,
  -- procedure Test()
  .proc { header := { name := "Test",
                      typeArgs := [],
                      inputs := [],
                      outputs := [] },
          spec := { preconditions := [],
                    postconditions := [] },
          body := [
            -- var m : Map int bool;
            Statement.init "m" (.forAll [] (.tcons "Map" [.tcons "int" [], .tcons "bool" []])) Imperative.ExprOrNondet.nondet .empty,
            -- m := makePair(identity(42), identity(true));
            Statement.set "m" eb[((~makePair (~identity #42)) (~identity #true))] .empty
          ]
  } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function identity<$__ty0> (x : $__ty0) : $__ty0;
function makePair<$__ty1, $__ty2> (x : $__ty1, y : $__ty2) : Map $__ty1 $__ty2;
procedure Test ()
{
  var m : (Map int bool);
  m := makePair(identity(42), identity(true));
};
-/
#guard_msgs in
#eval do
  let ans ← typeCheck .default polyFuncProg
  return (format ans)


section
def intIdentityFnPgm : Program := { decls := [
  .func { name := "intID",
          typeArgs := [],
          inputs := [],
          output := .arrow .int .int,
          body := some eb[λ %0]
          } .empty
]}

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info: ok: program Core;

function intID () : int -> int {
  lambda __q0 : int :: __q0
}
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndBuildObligationProgram .default intIdentityFnPgm
          return (format ans)
end

---------------------------------------------------------------------

/-- A `Decl.func` with `isRecursive := true` should be rejected.
    `Decl.func` is for non-recursive functions only; recursive functions
    must use `Decl.recFuncBlock`. -/
def recursiveFuncDeclProg : Program := { decls := [
  .func { name := "bad", isRecursive := true, inputs := [("x", .int)], output := .int } .empty
]}

/--
info: error: Decl.func does not allow recursive functions. Use recFuncBlock instead: 'bad'
-/
#guard_msgs in
#eval do let (ans, _) ← typeCheckAndEval .default recursiveFuncDeclProg
         return (format ans)

---------------------------------------------------------------------

end Tests
end Core
