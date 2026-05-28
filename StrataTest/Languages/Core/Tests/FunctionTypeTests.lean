/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Function Type Soundness Tests

Tests for the alpha-equivalence check on function bodies. The type checker
ensures that a polymorphic function's body does not constrain declared type
parameters to concrete types or identify distinct type parameters.

We also verify that body annotations use the declared type parameter names
(required by the denotational semantics).
-/

namespace Core.FunctionTypeTests

open Std (ToFormat Format format)
open Lambda Imperative
open LTy.Syntax LExpr.SyntaxMono

private def C : Core.Expression.TyContext := LContext.default
private def Env : Core.Expression.TyEnv := default

---------------------------------------------------------------------
-- Tests that should PASS
---------------------------------------------------------------------

-- 1. Inferred bound variable with consistent type.
-- wrapId<T>(x:T):T { (\y.y)(x) }
-- The lambda binder y has no annotation; inference assigns it a fresh variable
-- that ends up consistent with T via alpha-equivalence.
-- Body annotations should use the declared type arg name ($__ty0).
private def inferredBinderFunc : Core.Function :=
  { name := ⟨"wrapId", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app () (.abs () "y" none (.bvar () 0)) (.fvar () ⟨"x", ()⟩ none)) }

/--
info: ok: typeArgs: [$__ty0]
inputs: (x, $__ty0)
output: $__ty0
body: some (fun y : ($__ty0) => y)(x)
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env inferredBinderFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- 2. Multiple type parameters, all used consistently.
-- fst<a,b>(x:a, y:b):a { x }
private def fstFunc : Core.Function :=
  { name := ⟨"fst", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")],
    output := .ftvar "a",
    body := some (LExpr.fvar () ⟨"x", ()⟩ none) }

/--
info: ok: typeArgs: [$__ty0, $__ty1]
inputs: (x, $__ty0) (y, $__ty1)
output: $__ty0
body: some x
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env fstFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- 3. Identity with annotated binder.
-- id<T>(x:T):T { (\(y:T).y)(x) }
-- The binder has annotation T; after type checking, it should be $__ty0.
private def annotatedBinderFunc : Core.Function :=
  { name := ⟨"id", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app () (.abs () "y" (some (.ftvar "T")) (.bvar () 0)) (.fvar () ⟨"x", ()⟩ none)) }

/--
info: ok: typeArgs: [$__ty0]
inputs: (x, $__ty0)
output: $__ty0
body: some (fun y : ($__ty0) => y)(x)
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env annotatedBinderFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

---------------------------------------------------------------------
-- Regression tests
---------------------------------------------------------------------

-- Issue #1287: Free type variables in function declarations can be captured.
-- f<T>(x : T, y : $__ty0) : T { y }
-- $__ty0 is NOT in typeArgs — semantically a different type from T.
private def issue1287_func : Core.Function :=
  { name := ⟨"bad", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T"), (⟨"y", ()⟩, .ftvar "$__ty0")],
    output := .ftvar "T",
    body := some (LExpr.fvar () ⟨"y", ()⟩ none) }

/--
info: error: Function 'bad': type variables [$__ty0] appear in the signature but are not declared in typeArgs [T]
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env issue1287_func
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}"

-- Issue #586: Soundness bug in program-level type inference.
-- foo<a>(x : a) : a { x + 1 } should be rejected because the body constrains
-- a to int, but the function claims to be polymorphic.
open Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax in
def issue586_pgm : Program := { decls := [
  .func { name := "foo",
          typeArgs := ["a"],
          inputs := [("x", .ftvar "a")],
          output := .ftvar "a",
          body := some eb[((~Int.Add x) #1)] } .empty,
  .proc { header := { name := "callFoo",
                      typeArgs := [],
                      inputs := [],
                      outputs := [] },
          spec := { preconditions := [],
                    postconditions := [] },
          body := [
            Statement.init "s" (.forAll [] .string) (.det eb[#hello]) .empty,
            Statement.init "r" (.forAll [] .string) (.det eb[(~foo s)]) .empty
          ]
  } .empty
]}

/--
info: error: Function 'foo': body constrains the type to '(arrow int int)', incompatible with declared polymorphic signature '(arrow $__ty0 $__ty0)'
-/
#guard_msgs in
#eval (typeCheck .default issue586_pgm)

---------------------------------------------------------------------
-- Tests that should FAIL
---------------------------------------------------------------------

-- 4. Two distinct type params identified by the body.
-- swap<a,b>(x:a, y:b):a { y } forces b = a.
private def identifyParamsFunc : Core.Function :=
  { name := ⟨"swap", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")],
    output := .ftvar "a",
    body := some (LExpr.fvar () ⟨"y", ()⟩ none) }

/--
info: error: Function 'swap': body constrains the type to '(arrow $__ty1 (arrow $__ty1 $__ty1))', incompatible with declared polymorphic signature '(arrow $__ty0 (arrow $__ty1 $__ty0))'
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env identifyParamsFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- 5. Binder with incorrect concrete annotation in a polymorphic function.
-- bad<T>(x:T):T { (\(y:int).y)(x) }
-- The binder annotation `int` forces the type param to int.
private def wrongAnnotFunc : Core.Function :=
  { name := ⟨"bad", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app () (.abs () "y" (some .int) (.bvar () 0)) (.fvar () ⟨"x", ()⟩ none)) }

/--
info: error: Function 'bad': body constrains the type to '(arrow int int)', incompatible with declared polymorphic signature '(arrow $__ty0 $__ty0)'
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env wrongAnnotFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

end Core.FunctionTypeTests
