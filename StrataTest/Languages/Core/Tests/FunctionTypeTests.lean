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
open Strata in
private def fstPgm :=
#strata
program Core;

function fst<a, b>(x : a, y : b) : a {
  x
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function fst<$__ty0, $__ty1> (x : $__ty0, y : $__ty1) : $__ty0 {
  x
}
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram fstPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

-- Annotated binder renamed to match instantiated typeArgs.
-- id<T>(x:T):T { (fun y:T => y)(x) }
open Strata in
private def annotatedBinderPgm :=
#strata
program Core;

function id<T>(x : T) : T {
  (fun y : T => y)(x)
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function id<$__ty0> (x : $__ty0) : $__ty0 {
  (fun y : ($__ty0) => y)(x)
}
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram annotatedBinderPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

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
info: error: Function 'swap': body constrains the type to '(arrow b (arrow b b))', incompatible with declared polymorphic signature '(arrow a (arrow b a))'
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env identifyParamsFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- Binder with incorrect concrete annotation in a polymorphic function.
-- bad<T>(x:T):T { (fun y:int => y)(x) } forces T = int.
open Strata in
private def wrongAnnotPgm :=
#strata
program Core;

function bad<T>(x : T) : T {
  (fun y : int => y)(x)
}
#end

/--
info: error: Function 'bad': body constrains the type to '(arrow int int)', incompatible with declared polymorphic signature '(arrow T T)'
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram wrongAnnotPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

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
info: error: Function 'foo': body constrains the type to '(arrow int int)', incompatible with declared polymorphic signature '(arrow a a)'
-/
#guard_msgs in
#eval (typeCheck .default issue586_pgm)

-- Quantifier annotation referencing an undeclared type var.
-- f<T>(x:T):T { (forall y:U. y)(x) } — U is not in typeArgs.
private def strayQuantVarFunc : Core.Function :=
  { name := ⟨"f", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app ()
      (.quant () .all "y" (some (.ftvar "U")) (.bvar () 0) (.bvar () 0))
      (.fvar () ⟨"x", ()⟩ none)) }

/--
info: error: Function 'f': body contains undeclared type variables [U] (not in typeArgs [T])
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayQuantVarFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- fvar annotation referencing an undeclared type var.
-- g<T>(x:T):T { x } where x carries annotation (ftvar "V").
private def strayFvarAnnotFunc : Core.Function :=
  { name := ⟨"g", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.fvar () ⟨"x", ()⟩ (some (.ftvar "V"))) }

/--
info: error: Function 'g': body contains undeclared type variables [V] (not in typeArgs [T])
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayFvarAnnotFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- Non-trivial bwdMap: unannotated binder creates fresh type variables that
-- get renamed back via the alpha-equivalence witness map.
-- wrap<a,b>(f: a->b, x: a): b { (\y.f(y))(x) }
private def nonTrivialBwdFunc : Core.Function :=
  { name := ⟨"wrap", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(⟨"f", ()⟩, .arrow (.ftvar "a") (.ftvar "b")), (⟨"x", ()⟩, .ftvar "a")],
    output := .ftvar "b",
    body := some (.app ()
      (.abs () "y" none (.app () (.fvar () ⟨"f", ()⟩ none) (.bvar () 0)))
      (.fvar () ⟨"x", ()⟩ none)) }

/--
info: ok: typeArgs: [$__ty0, $__ty1]
inputs: (f, (arrow $__ty0 $__ty1)) (x, $__ty0)
output: $__ty1
body: some (fun y : ($__ty0) => f(y))(x)
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env nonTrivialBwdFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- Higher-order function with multiple type args.
-- apply<a,b>(f: a -> b, x: a): b { f(x) }
open Strata in
def higherOrderPgm :=
#strata
program Core;

inline function apply<a, b>(f : a -> b, x : a) : b {
  f(x)
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

inline function apply<$__ty0, $__ty1> (f : $__ty0 -> $__ty1, x : $__ty0) : $__ty1 {
  f(x)
}
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram higherOrderPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

---------------------------------------------------------------------
-- alphaEquivMap unit tests
---------------------------------------------------------------------

-- Reflexive: a type is alpha-equivalent to itself.
#guard (LMonoTy.alphaEquivMap (.ftvar "a") (.ftvar "a")).isSome

-- Consistent renaming: (a → a) ≈ (b → b).
#guard (LMonoTy.alphaEquivMap
  (.tcons "arrow" [.ftvar "a", .ftvar "a"])
  (.tcons "arrow" [.ftvar "b", .ftvar "b"])).isSome

-- Non-injective (capture): (a → b) ≉ (c → c) — two vars mapped to one.
#guard (LMonoTy.alphaEquivMap
  (.tcons "arrow" [.ftvar "a", .ftvar "b"])
  (.tcons "arrow" [.ftvar "c", .ftvar "c"])).isNone

-- Distinct ftvars with crossing: (a → b) ≈ (b → a).
#guard (LMonoTy.alphaEquivMap
  (.tcons "arrow" [.ftvar "a", .ftvar "b"])
  (.tcons "arrow" [.ftvar "b", .ftvar "a"])).isSome

-- Mismatched constructors: arrow ≉ pair.
#guard (LMonoTy.alphaEquivMap
  (.tcons "arrow" [.ftvar "a", .ftvar "b"])
  (.tcons "pair" [.ftvar "a", .ftvar "b"])).isNone

-- Mismatched arity: (a → b) ≉ (a).
#guard (LMonoTy.alphaEquivMap
  (.tcons "arrow" [.ftvar "a", .ftvar "b"])
  (.tcons "arrow" [.ftvar "a"])).isNone

end Core.FunctionTypeTests
