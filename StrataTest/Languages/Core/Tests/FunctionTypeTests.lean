/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Function Type Soundness Tests

Tests for the alpha-equivalence check on function bodies and the closedness
check on type variables. We verify that body annotations are consistent with
the function's instantiated typeArgs.
-/

namespace Core.FunctionTypeTests

open Std (ToFormat Format format)
open Lambda Imperative
open LTy.Syntax LExpr.SyntaxMono

private def C : Core.Expression.TyContext := LContext.default
private def Env : Core.Expression.TyEnv := default

---------------------------------------------------------------------
-- Should PASS
---------------------------------------------------------------------

-- Unannotated lambda binder; inference assigns a consistent type.
-- wrapId<T>(x:T):T { (\y.y)(x) }
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

-- Multiple type parameters, all used consistently.
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

-- Annotated binder renamed to match instantiated typeArgs.
-- id<T>(x:T):T { (\(y:T).y)(x) }
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
-- Should FAIL
---------------------------------------------------------------------

-- Two distinct type params identified by the body.
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

-- Binder with incorrect concrete annotation in a polymorphic function.
-- bad<T>(x:T):T { (\(y:int).y)(x) } forces T = int.
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

-- Body introduces a type variable not in typeArgs via a lambda annotation.
-- id<T>(x:T):T { (\(y:U).y)(x) } — U is not in typeArgs.
private def strayBodyVarFunc : Core.Function :=
  { name := ⟨"id", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app () (.abs () "y" (some (.ftvar "U")) (.bvar () 0)) (.fvar () ⟨"x", ()⟩ none)) }

/--
info: error: Function 'id': body contains undeclared type variables [U] (not in typeArgs [T])
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayBodyVarFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

---------------------------------------------------------------------
-- Regression tests
---------------------------------------------------------------------

-- Issue #1287: Undeclared free type variable in signature.
-- f<T>(x : T, y : $__ty0) : T { y }
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

-- Issue #586: Body constrains polymorphic type arg to concrete type.
-- foo<a>(x:a):a { x + 1 } then called as foo("hello").
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

end Core.FunctionTypeTests
