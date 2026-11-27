/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Verifier
import StrataTest.Languages.Core.Tests.TestUtil

/-! ## Function Type Soundness Tests

Tests for function type checking and unit tests for `alphaEquivMap`.
-/

namespace Core.FunctionTypeTests
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"

open Std (ToFormat Format format)
open Core.TestUtil (aliasEnv coreVerdict firstLineOf functionVerdict programVerdict rigidA
  translate verdictOf)
open _root_.Lambda Imperative
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
    body := some (.app testLoc (.abs testLoc "y" none (.bvar testLoc 0)) (.fvar testLoc ⟨"x",
        ()⟩ none)) }

/--
info: ok: typeArgs: [T]
inputs: (x, T)
output: T
body: some (fun y : T => y)(x)
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

function fst<a, b> (x : a, y : b) : a {
  x
}
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate fstPgm))

-- The annotated binder keeps its written type name `T`.
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

function id<T> (x : T) : T {
  (fun y : T => y)(x)
}
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate annotatedBinderPgm))

-- An op annotation's type variables belong to the op: in the body of `f<a>`, `idf` annotated
-- `a → a`, `c → c` or not at all may be used at `bool`.
open Core.TestUtil (idfDecl idfTrueEq printIdfVerdicts) in
/--
info: ACCEPTED
ACCEPTED
ACCEPTED
-/
#guard_msgs in
#eval printIdfVerdicts fun ann => { decls := [idfDecl,
  .func { name := "f", typeArgs := ["a"], inputs := [("x", .ftvar "a")], output := .bool,
          body := some (idfTrueEq ann) } .empty] }

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
    body := some (LExpr.fvar testLoc ⟨"y", ()⟩ none) }

/--
info: error: Rigid type variable 'b' was refined to 'a'
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env identifyParamsFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- `Nil() == x` refines the rigid `a` to a list; the unsolved element type prints as `_`.
open Strata in
private def rigidUnsolvedListFuncPgm :=
#strata
program Core;
datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };
function f<a>(x : a) : bool { Nil() == x }
#end

/--
info: error: Rigid type variable 'a' was refined to '(List _)'
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate rigidUnsolvedListFuncPgm))

-- A generated type variable or type constructor name prints as `_`; the name `Pair` is not
-- generated, so it prints as is.
/--
info: some "Rigid type variable 'a' was refined to '(Pair _ _ int)'"
-/
#guard_msgs in
#eval
  Core.refineUnifyError? Lambda.KnownTypes.default [("a", "$__rigid_a")]
    (.ImpossibleToUnify (.ftvar "a",
      .tcons "Pair" [.ftvar "$__ty0", .tcons "$__tyC" [], .int]))

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
info: error: Rigid type variable 'T' was refined to 'int'
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate wrongAnnotPgm))

-- Body introduces a type variable not in typeArgs via a lambda annotation.
-- id<T>(x:T):T { (\(y:U).y)(x) } — U is not in typeArgs.
private def strayBodyVarFunc : Core.Function :=
  { name := ⟨"id", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.app testLoc (.abs testLoc "y" (some (.ftvar "U")) (.bvar testLoc 0)) (.fvar
        testLoc ⟨"x", ()⟩ none)) }

/--
info: error: Function 'id': type variable `U` is not in scope
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
    body := some (LExpr.fvar testLoc ⟨"y", ()⟩ none) }

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
          body := .structured [
            Statement.init "s" (.forAll [] .string) (.det eb[#hello]) .empty,
            Statement.init "r" (.forAll [] .string) (.det eb[(~foo s)]) .empty
          ] false
  } .empty
]}

/--
info: error: Rigid type variable 'a' was refined to 'int'
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
    body := some (.app testLoc
      (.quant testLoc .all "y" (some (.ftvar "U")) (.bvar testLoc 0) (.bvar testLoc 0))
      (.fvar testLoc ⟨"x", ()⟩ none)) }

/--
info: error: Function 'f': type variable `U` is not in scope
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayQuantVarFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

-- A free-variable annotation may not reference an undeclared type variable.
-- g<T>(x:T):T { x } where x carries annotation (ftvar "V").
private def strayFvarAnnotFunc : Core.Function :=
  { name := ⟨"g", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.fvar testLoc ⟨"x", ()⟩ (some (.ftvar "V"))) }

/--
info: error: Function 'g': type variable `V` is not in scope
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayFvarAnnotFunc
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\nbody: {func'.body}"

/-- A function `name<typeArgs>(x : T) : T { x }` with an axiom whose binder has type `U`. -/
private def axiomBinderUFunc (name : String) (typeArgs : List String) : Core.Function :=
  { name := ⟨name, ()⟩,
    typeArgs,
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none),
    axioms := [.quant Core.coreLoc .all "y" (some (.ftvar "U"))
               (.const Core.coreLoc (.boolConst true))
      (.const Core.coreLoc (.boolConst true))] }

-- A quantifier annotation in an axiom may not reference an undeclared type variable.
private def strayAxiomVarFunc : Core.Function := axiomBinderUFunc "f" ["T"]

/--
info: error: Function 'f': type variable `U` is not in scope
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayAxiomVarFunc
  return format f!"typeArgs: {func'.typeArgs}"

-- A lambda annotation in a precondition may not reference an undeclared type variable.
private def strayPreconditionExpr : Expression.Expr :=
  .app Core.coreLoc (.abs Core.coreLoc "y" (some (.ftvar "U"))
                     (.const Core.coreLoc (.boolConst true)))
    (.const Core.coreLoc (.boolConst true))

private def strayPreconditionVarFunc : Core.Function :=
  { name := ⟨"g", ()⟩,
    typeArgs := ["T"],
    inputs := [(⟨"x", ()⟩, .ftvar "T")],
    output := .ftvar "T",
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none),
    preconditions := [{ expr := strayPreconditionExpr, md := default }] }

/--
info: error: Function 'g': type variable `U` is not in scope
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env strayPreconditionVarFunc
  return format f!"typeArgs: {func'.typeArgs}"

-- A type parameter that only an axiom's binder mentions is rejected.
private def axiomOnlyTypeArgFunc : Core.Function := axiomBinderUFunc "h" ["T", "U"]

/--
info: error: Function 'h': type parameters [U] occur in neither an input type nor the output type, so a call could not determine them
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env axiomOnlyTypeArgFunc
  return format f!"typeArgs: {func'.typeArgs}"

-- An unannotated binder's type is inferred from the function's rigid parameters.
-- wrap<a,b>(f: a->b, x: a): b { (\y.f(y))(x) }
private def nonTrivialBwdFunc : Core.Function :=
  { name := ⟨"wrap", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(⟨"f", ()⟩, .arrow (.ftvar "a") (.ftvar "b")), (⟨"x", ()⟩, .ftvar "a")],
    output := .ftvar "b",
    body := some (.app testLoc
      (.abs testLoc "y" none (.app testLoc (.fvar testLoc ⟨"f", ()⟩ none) (.bvar testLoc 0)))
      (.fvar testLoc ⟨"x", ()⟩ none)) }

/--
info: ok: typeArgs: [a, b]
inputs: (f, (arrow a b)) (x, a)
output: b
body: some (fun y : a => f(y))(x)
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

inline function apply<a, b> (f : a -> b, x : a) : b {
  f(x)
}
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate higherOrderPgm))

---------------------------------------------------------------------
-- Type parameter order
---------------------------------------------------------------------

-- Type parameters whose first occurrences in the signature are out of
-- declaration order keep their declared names and order.
-- h<a,b>(x:b, y:a):a, without and with a body.
private def outOfOrderDecl : Core.Function :=
  { name := ⟨"h", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(⟨"x", ()⟩, .ftvar "b"), (⟨"y", ()⟩, .ftvar "a")],
    output := .ftvar "a",
    body := none }

/--
info: ok: typeArgs: [a, b]
inputs: (x, b) (y, a)
output: a
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env outOfOrderDecl
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}"

open Strata in
private def outOfOrderPgm :=
#strata
program Core;

function h<a, b>(x : b, y : a) : a {
  y
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function h<a, b> (x : b, y : a) : a {
  y
}
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram outOfOrderPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

-- An alias that reorders its parameters: `Swap a b` resolves to `Map b a`,
-- so `b` occurs first in the resolved signature.
open Strata in
private def swapAliasPgm :=
#strata
program Core;

type Swap (a : Type, b : Type) := Map b a;
function f<a, b>(x : Swap a b) : a;
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type Swap (a : Type, b : Type) := Map b a;
function f<a, b> (x : Map b a) : a;
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram swapAliasPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

-- An alias that repeats its parameter: `Dup b` resolves to `Map b b`.
open Strata in
private def dupAliasPgm :=
#strata
program Core;

type Dup (a : Type) := Map a a;
function g<a, b>(x : Dup b, y : a) : a;
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

type Dup (a : Type) := Map a a;
function g<a, b> (x : Map b b, y : a) : a;
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram dupAliasPgm)).fst
  Std.format (Core.typeCheck .default pgm.stripMetaData)

-- Declaration order differs from alphabetical and first-occurrence order.
-- f<b,a>(x:a, y:b):b keeps [b, a].
private def reverseDeclOrder : Core.Function :=
  { name := ⟨"f", ()⟩,
    typeArgs := ["b", "a"],
    inputs := [(⟨"x", ()⟩, .ftvar "a"), (⟨"y", ()⟩, .ftvar "b")],
    output := .ftvar "b",
    body := none }

/--
info: ok: typeArgs: [b, a]
inputs: (x, a) (y, b)
output: b
-/
#guard_msgs in
#eval do
  let (func', _) ← Function.typeCheck C Env reverseDeclOrder
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}"

-- A declared type parameter that occurs in no input or output type is rejected,
-- since no call could determine it.
open Strata in
private def phantomPgm :=
#strata
program Core;

function f<a, b>(x : a) : a;
#end

/--
info: error: Function 'f': type parameters [b] occur in neither an input type nor the output type, so a call could not determine them
-/
#guard_msgs in
open Strata in
#eval
  let pgm := (TransM.run Inhabited.default (translateProgram phantomPgm)).fst
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

/-! ## Polymorphic signatures -/

/-- The checked function's type parameters, inputs, output and body, or the error. -/
private def checkedSummary (func : Core.Function) : Except Format Format := do
  let (func', _) ← Function.typeCheck C Env func
  return format f!"typeArgs: {func'.typeArgs}\ninputs: {func'.inputs}\noutput: {func'.output}\n\
    body: {func'.body}"

-- An identity function preserves its rigid parameter type.
private def polymorphicIdentityFunc : Core.Function :=
  { name := ⟨"id", ()⟩, typeArgs := ["a"],
    inputs := [(⟨"x", ()⟩, .ftvar "a")], output := .ftvar "a",
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none) }

/--
info: ok: typeArgs: [a]
inputs: (x, a)
output: a
body: some x
-/
#guard_msgs in
#eval checkedSummary polymorphicIdentityFunc

-- An annotated lambda may use the function's rigid parameter types consistently.
private def annotatedLambdaWrapperFunc : Core.Function :=
  { name := ⟨"wrap", ()⟩, typeArgs := ["a", "b"],
    inputs := [(⟨"f", ()⟩, .arrow (.ftvar "a") (.ftvar "b")), (⟨"x", ()⟩, .ftvar "a")],
    output := .ftvar "b",
    body := some (.app Core.coreLoc
      (.abs Core.coreLoc "y" (some (.ftvar "a"))
        (.app Core.coreLoc (.fvar Core.coreLoc ⟨"f", ()⟩ none) (.bvar Core.coreLoc 0)))
      (.fvar Core.coreLoc ⟨"x", ()⟩ none)) }

/--
info: ok: typeArgs: [a, b]
inputs: (f, (arrow a b)) (x, a)
output: b
body: some (fun y : a => f(y))(x)
-/
#guard_msgs in
#eval checkedSummary annotatedLambdaWrapperFunc

/-! ## Type parameters and body types -/

-- A type parameter that occurs only in quantifier binders is rejected.
open Strata in
private def binderOnlyTypeArgPgm :=
#strata
program Core;

function isSingleton<a>() : bool { forall x : a, y : a :: x == y }
function bz() : bool { isSingleton() }
#end

/--
info: error: Function 'isSingleton': type parameters [a] occur in neither an input type nor the output type, so a call could not determine them
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate binderOnlyTypeArgPgm))

-- A binder annotated with the function's own type parameter denotes that parameter, so
-- `forall y : a :: y == y` in a function body is checked and verified at every `a`.
open Strata in
private def binderAtTypeParamPgm :=
#strata
program Core;

function allEq<a>(x : a) : bool { forall y : a :: y == y }
procedure P() { assert [allEqInt]: allEq(1); };
#end

/--
info:
Obligation: allEqInt
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify binderAtTypeParamPgm (options := .quiet)

-- Such a binder cannot be used at another type: `y == 5` would refine `a` to `int`.
open Strata in
private def binderAtTypeParamRefinedPgm :=
#strata
program Core;

function allFive<a>(x : a) : bool { forall y : a :: y == 5 }
#end

/--
info: error: Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate binderAtTypeParamRefinedPgm))

-- A type parameter mentioned nowhere is rejected.
open Strata in
private def unusedTypeArgPgm :=
#strata
program Core;

function k<a>(x : int) : int { x }
#end

/--
info: error: Function 'k': type parameters [a] occur in neither an input type nor the output type, so a call could not determine them
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate unusedTypeArgPgm))

-- A type parameter that occurs only in the output type, or only in an input type, is accepted.
open Strata in
private def signatureTypeArgPgm :=
#strata
program Core;

function anyval<c>() : c;
function isSome<a>(x : a) : bool { true }
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function anyval<c> () : c;
function isSome<a> (x : a) : bool {
  true
}
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate signatureTypeArgPgm))

-- A body whose `anyval()` instances have no fixed type is rejected.
open Strata in
private def openInstanceBodyPgm :=
#strata
program Core;

function anyval<c>() : c;
function f() : bool { anyval() == anyval() }
#end

/--
info: error: Function 'f': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate openInstanceBodyPgm))

-- An unannotated quantifier binder is inferred as `bool` from its body.
private def inferredBoolQuantifierFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [], inputs := [], output := .bool,
    body := some (.quant Core.coreLoc .exist "x" none (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))
        }

/--
info: ok: typeArgs: []
inputs:
output: bool
body: some exists x : bool :: x
-/
#guard_msgs (whitespace := lax) in
#eval checkedSummary inferredBoolQuantifierFunc

-- A body annotation naming a declared type parameter means that parameter: the binder of
-- `forall y : a :: y == y` is typed at the function's own `a`, though nothing else ties `y`
-- to `x`.
open Strata in
private def ownParamBinderPgm :=
#strata
program Core;

function f<a>(x : a) : a { if (forall y : a :: y == y) then x else x }
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function f<a> (x : a) : a {
  if forall y : a :: y == y then x else x
}
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate ownParamBinderPgm))

-- An unannotated quantified variable used only at its own type has a type that no call can
-- fix, so the body is rejected, in a polymorphic function and in a monomorphic one.
-- f<a>(x : a) : a { if (forall y :: y == y) then x else x }
private def undeterminedBinderFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["a"],
    inputs := [(⟨"x", ()⟩, .ftvar "a")], output := .ftvar "a",
    body := some (.ite Core.coreLoc
      (.quant Core.coreLoc .all "y" none (.bvar Core.coreLoc 0)
        (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0)))
      (.fvar Core.coreLoc ⟨"x", ()⟩ none) (.fvar Core.coreLoc ⟨"x", ()⟩ none)) }

/--
info: error: Function 'f': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval checkedSummary undeterminedBinderFunc

-- f(x : int) : int { if (forall y :: y == y) then x else x }
private def undeterminedBinderMonoFunc : Core.Function :=
  { undeterminedBinderFunc with typeArgs := [], inputs := [(⟨"x", ()⟩, .int)], output := .int }

/--
info: error: Function 'f': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval checkedSummary undeterminedBinderMonoFunc

-- An undetermined type with no binder: the element type of an empty sequence whose length is
-- compared with 0.
-- f(x : int) : bool { Sequence.length(Sequence.empty()) == 0 }
private def undeterminedEmptySeqPgm : Program :=
  { decls :=
      [.func { name := "f", typeArgs := [], inputs := [("x", .int)], output := .bool,
               body := some (.eq Core.coreLoc
                 (.app Core.coreLoc (.op Core.coreLoc ⟨"Sequence.length", ()⟩ none)
                   (.op Core.coreLoc ⟨"Sequence.empty", ()⟩ none))
                 (.intConst Core.coreLoc 0)) } .empty] }

/--
info: REJECTED: Function 'f': the body, the decreases expression, a precondition or an axiom is typed at a generated type variable that is not declared. Nothing fixes the type of a polymorphic instance there; annotate it, or use a type parameter the signature mentions
-/
#guard_msgs in
#eval programVerdict undeterminedEmptySeqPgm

-- An integer measure using `x : a` would refine the rigid `a` to `int`.
open Strata in
private def measureRefinePgm :=
#strata
program Core;

rec function f<a>(x : a) : a
decreases int.add(x, 0)
{
  f(x)
};
#end

/--
info: error: Rigid type variable 'a' was refined to 'int'
-/
#guard_msgs (whitespace := lax) in
#eval
  Std.format (Core.typeCheck .default (translate measureRefinePgm))

/-! ## Names with reserved prefixes, parameter collisions, and constructor bodies -/

-- A function name with the generated-variable prefix `$__ty` is accepted.
private def reservedNameFunc : Core.Function :=
  { name := ⟨"$__tyBad", ()⟩, typeArgs := [], inputs := [], output := .bool,
    body := none }

/-- info: ok: $__tyBad -/
#guard_msgs in
#eval match Function.typeCheck C Env reservedNameFunc with
  | .ok (f, _) => f!"ok: {f.name}"
  | .error e => f!"error: {e}"

-- A function with a repeated type parameter is rejected.
private def dupTypeArgsFunc : Core.Function :=
  { name := ⟨"dupTypeArgs", ()⟩, typeArgs := ["a", "a"], inputs := [], output := .bool,
    body := none }

/--
info: REJECTED: Function 'dupTypeArgs': duplicate type arguments [a, a]
-/
#guard_msgs in
#eval functionVerdict dupTypeArgsFunc C Env

-- A repeated type parameter with a reserved prefix is reported as written.
private def dupReservedTypeArgsFunc : Core.Function :=
  { name := ⟨"dupTypeArgs", ()⟩, typeArgs := ["$__ty0", "$__ty0"], inputs := [],
    output := .bool, body := none }

/--
info: REJECTED: Function 'dupTypeArgs': duplicate type arguments [$__ty0, $__ty0]
-/
#guard_msgs in
#eval functionVerdict dupReservedTypeArgsFunc C Env

-- A type parameter with the generated-variable prefix `$__ty` is renamed to a fresh name
-- throughout the function.
private def reservedTypeArgFunc : Core.Function :=
  { name := ⟨"reservedTypeArg", ()⟩, typeArgs := ["$__ty0"], inputs := [],
    output := .ftvar "$__ty0", body := none }

/-- info: ok: [a] a -/
#guard_msgs in
#eval match Function.typeCheck C Env reservedTypeArgFunc with
  | .ok (f, _) => f!"ok: {f.typeArgs} {f.output}"
  | .error e => f!"error: {e}"

-- The fresh name avoids a type variable that only the body mentions, so an annotation at an
-- undeclared `a` is still rejected.
private def reservedTypeArgBodyAnnotFunc : Core.Function :=
  { name := ⟨"bodyAnnot", ()⟩, typeArgs := ["$__ty0"],
    inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "$__ty0",
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "a"))) }

/-- info: REJECTED: Function 'bodyAnnot': type variable `a` is not in scope -/
#guard_msgs in
#eval functionVerdict reservedTypeArgBodyAnnotFunc C Env

-- A `PureFunc` signature is checked as written.
private def reservedTypeArgPureFunc : PureFunc Expression :=
  { name := ⟨"p", ()⟩, typeArgs := ["$__ty0"],
    inputs := [(⟨"x", ()⟩, .forAll [] (.ftvar "b"))], output := .forAll [] .int }

/--
info: REJECTED: Function 'p': type variables [b] appear in the signature but are not declared in typeArgs [$__ty0]
-/
#guard_msgs in
#eval verdictOf (PureFunc.typeCheck C Env reservedTypeArgPureFunc)

/-- The recursive block checker's verdict on `funcs`. -/
private def recBlockResult (funcs : List Core.Function) : Format :=
  verdictOf (RecFuncBlock.typeCheck C Env funcs)

-- A recursive block member's signature names are checked as written.
private def recUndeclaredTyVarFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := ["$__ty0"], isRecursive := true,
    inputs := [(⟨"x", ()⟩, .ftvar "$__ty0")], output := .ftvar "b", body := none }

/--
info: REJECTED: Function 'f': type variables [b] appear in the signature but are not declared in typeArgs [$__ty0]
-/
#guard_msgs in
#eval recBlockResult [recUndeclaredTyVarFunc]

/--
info: REJECTED: Function 'f': duplicate type arguments [$__ty0, $__ty0]
-/
#guard_msgs in
#eval recBlockResult
  [{ name := ⟨"f", ()⟩, typeArgs := ["$__ty0", "$__ty0"], isRecursive := true, inputs := [],
     output := .int, body := none }]

/-- The type variables of the annotations in `f`'s preconditions, axioms and
measure, one line each. -/
private def annotTyVarLines {IdentT TyT MetadataT : Type}
    (f : Strata.DL.Util.Func IdentT Expression.Expr TyT MetadataT) : Format :=
  let pre := f.preconditions.map (annotTyVars ∘ Strata.DL.Util.FuncPrecondition.expr)
  f!"precondition: {pre}\naxiom: {f.axioms.map annotTyVars}\n\
     measure: {f.measure.map annotTyVars}"

-- The renaming also covers a type parameter in a precondition, an axiom and the measure: the
-- type variables of their annotations are printed.
private def reservedTypeArgEverywhere : Core.Function :=
  let x : Expression.Expr := .fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "$__ty0"))
  let n : Expression.Expr := .fvar Core.coreLoc ⟨"n", ()⟩ none
  { name := ⟨"reservedEverywhere", ()⟩, typeArgs := ["$__ty0"], isRecursive := true,
    inputs := [(⟨"x", ()⟩, .ftvar "$__ty0"), (⟨"n", ()⟩, .int)], output := .int,
    body := some n,
    preconditions := [{ expr := .eq Core.coreLoc x x, md := Core.coreLoc }],
    axioms := [LExpr.all Core.coreLoc "y" (some (.ftvar "$__ty0"))
               (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))],
    measure := some (.ite Core.coreLoc (.eq Core.coreLoc x x) n n) }

/--
info: ok: [a]
precondition: [[a, a]]
axiom: [[a]]
measure: some [a, a]
-/
#guard_msgs in
#eval match Function.typeCheck C Env reservedTypeArgEverywhere with
  | .ok (f, _) => f!"ok: {f.typeArgs}\n{annotTyVarLines f}"
  | .error e => f!"error: {e}"

-- A parameter with the generated-variable prefix `$__ty` is accepted.
private def reservedParamFunc : Core.Function :=
  { name := ⟨"reservedParam", ()⟩, typeArgs := [], inputs := [("$__ty0", .int)],
    output := .bool, body := none }

/-- info: ok: [$__ty0] -/
#guard_msgs in
#eval match Function.typeCheck C Env reservedParamFunc with
  | .ok (f, _) => f!"ok: {f.inputs.keys}"
  | .error e => f!"error: {e}"

-- A parameter named like an in-scope function (the constant `x`) shadows it.
open Strata in
private def funcParamCollidesPgm :=
#strata
program Core;

const x : int;
function f(x : int) : int {
  x
}
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

function x () : int;
function f (x : int) : int {
  x
}
-/
#guard_msgs in
#eval
  Std.format (Core.typeCheck .default (translate funcParamCollidesPgm))

-- A recursive block member's parameter named like a member of the block, another or itself,
-- shadows it.
private def recMember (name param : String) : Core.Function :=
  { name := ⟨name, ()⟩, typeArgs := [], isRecursive := true, inputs := [(⟨param, ()⟩, .int)],
    output := .int, body := none }

/--
info: ACCEPTED
-/
#guard_msgs in
#eval recBlockResult [recMember "f" "g", recMember "g" "y"]

/--
info: ACCEPTED
-/
#guard_msgs in
#eval recBlockResult [recMember "f" "f"]

-- A constructor with a body is rejected.
private def constrWithBodyFunc : Core.Function :=
  { name := ⟨"mkThing", ()⟩, typeArgs := [], isConstr := true,
    inputs := [(⟨"x", ()⟩, .bool)], output := .bool,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none) }

/--
info: REJECTED: Function 'mkThing': a constructor must not have a body
-/
#guard_msgs in
#eval functionVerdict constrWithBodyFunc C Env

-- A constructor without a body is accepted.
private def constrNoBodyFunc : Core.Function :=
  { name := ⟨"mkThing", ()⟩, typeArgs := [], isConstr := true,
    inputs := [(⟨"x", ()⟩, .bool)], output := .bool, body := none }

/--
info: ok: isConstr: true, body: none
-/
#guard_msgs in
#eval match Function.typeCheck C Env constrNoBodyFunc with
  | .ok (func', _) => f!"ok: isConstr: {func'.isConstr}, body: {func'.body}"
  | .error e => f!"error: {e}"

-- An ordinary function with a body is accepted.
private def nonConstrWithBodyFunc : Core.Function :=
  { name := ⟨"idBool", ()⟩, typeArgs := [], isConstr := false,
    inputs := [(⟨"x", ()⟩, .bool)], output := .bool,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none) }

/--
info: ok: isConstr: false, body: some x
-/
#guard_msgs in
#eval match Function.typeCheck C Env nonConstrWithBodyFunc with
  | .ok (func', _) => f!"ok: isConstr: {func'.isConstr}, body: {func'.body}"
  | .error e => f!"error: {e}"

/-! ## Reserved type names in annotations -/

section AnnotationHygiene
open Core.TestUtil (xId)

/-- The initial context with `fn` added to its factory. -/
def ctxWith (fn : Core.Function) : Expression.TyContext :=
  initTyContext.addFactoryFunction fn.toLFunc

/-- The factory checker's verdict on the builtins plus `fn`, with any rejection message. -/
def runCheck (fn : Core.Function) (Env : Expression.TyEnv := TEnv.default) : Format :=
  Core.TestUtil.verdictOf (Core.Factory.typeCheck (ctxWith fn) Env)

private def bodyAnnotated : Function :=
  { name := ⟨"bodyAnnotated", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .ftvar "a")],
    output := .ftvar "a",
    body := some (.fvar Core.coreLoc xId (some rigidA)) }

private def preconditionAnnotated : Function :=
  { name := ⟨"preconditionAnnotated", ()⟩,
    typeArgs := ["a"],
    isRecursive := true,
    inputs := [(xId, .ftvar "a")],
    output := .ftvar "a",
    body := some (.fvar Core.coreLoc xId none),
    preconditions := [{
      expr := .eq Core.coreLoc (.fvar Core.coreLoc xId (some rigidA))
          (.fvar Core.coreLoc xId (some rigidA)),
      md := Core.coreLoc
    }] }

private def measureAnnotated : Function :=
  { name := ⟨"measureAnnotated", ()⟩,
    typeArgs := ["a"],
    isRecursive := true,
    inputs := [(xId, .ftvar "a")],
    output := .ftvar "a",
    body := some (.fvar Core.coreLoc xId none),
    measure := some (.fvar Core.coreLoc xId (some rigidA)) }

private def topLevelProgram : Program :=
  { decls := [.func bodyAnnotated .empty] }

private def recursiveBlockProgram : Program :=
  { decls := [.recFuncBlock [preconditionAnnotated] .empty] }

-- A top-level function body annotation naming a type with the rigid prefix is rejected.
/-- info: REJECTED: Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| programVerdict topLevelProgram

-- A recursive function's precondition annotation naming a type with the rigid prefix is rejected.
/-- info: REJECTED: Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| programVerdict recursiveBlockProgram

-- A factory function's measure annotation naming a type with the rigid prefix is rejected.
/-- info: REJECTED: Type $__rigid_a is not an instance of a previously registered type! -/
#guard_msgs in
#eval Core.TestUtil.firstLineOf (runCheck measureAnnotated)

-- A bare-parameter measure annotated at a rigid-named type variable is rejected.
private def measureRigidVar : Function :=
  { name := ⟨"measureRigidVar", ()⟩,
    typeArgs := ["a"],
    isRecursive := true,
    inputs := [(xId, .ftvar "a")],
    output := .ftvar "a",
    body := some (.fvar Core.coreLoc xId none),
    measure := some (.fvar Core.coreLoc xId (some (.ftvar "$__rigid_q"))) }

/-- info: REJECTED: Function 'measureRigidVar': type variable `$__rigid_q` is not in scope -/
#guard_msgs in
#eval firstLineOf <| programVerdict { decls := [.recFuncBlock [measureRigidVar] .empty] }

-- A bare-parameter measure annotated at a generator-named type variable is rejected.
private def measureGeneratorVar : Function :=
  { name := ⟨"measureGeneratorVar", ()⟩,
    isRecursive := true,
    inputs := [(xId, .int)],
    output := .int,
    body := some (.fvar Core.coreLoc xId none),
    measure := some (.fvar Core.coreLoc xId (some (.ftvar "$__ty0"))) }

/-- info: REJECTED: Function 'measureGeneratorVar': type variable `$__ty0` is not in scope -/
#guard_msgs in
#eval firstLineOf <| programVerdict { decls := [.recFuncBlock [measureGeneratorVar] .empty] }

end AnnotationHygiene

/-! ## A function's expression positions reject an out-of-scope free variable -/

section FreeVariables
open Core.TestUtil (Env0)

/-- A quantified expression with the free variable `$__var0`, named like a generated binder. -/
def capturedExpr : Core.Expression.Expr :=
  .quant Core.coreLoc .all "q" (some Lambda.LMonoTy.bool) (.boolConst Core.coreLoc true)
    (.fvar Core.coreLoc ⟨"$__var0", ()⟩ (some Lambda.LMonoTy.bool))

/-- A quantified expression containing an ordinary out-of-scope free variable. -/
def strayExpr : Core.Expression.Expr :=
  .quant Core.coreLoc .all "q" (some Lambda.LMonoTy.bool) (.boolConst Core.coreLoc true)
    (.fvar Core.coreLoc ⟨"y", ()⟩ (some Lambda.LMonoTy.bool))

/-- `capturedExpr` as the condition of an integer `if`. -/
def capturedIntExpr : Core.Expression.Expr :=
  .ite Core.coreLoc capturedExpr (.intConst Core.coreLoc 1) (.intConst Core.coreLoc 0)

/-- A function whose body contains the capture-shaped free variable. -/
def bodyCapturedFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some capturedIntExpr }

/-- A function whose precondition contains the capture-shaped free variable. -/
def preCapturedFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := none,
    preconditions := [{ expr := capturedExpr, md := Core.coreLoc }] }

/-- A function whose axiom contains the capture-shaped free variable. -/
def axCapturedFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := none,
    axioms := [capturedExpr] }

/-- A recursive function whose computed measure contains the capture-shaped free variable. -/
def measureCapturedFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    isRecursive := true,
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none),
    measure := some capturedIntExpr }

/-- A function whose body contains an ordinary out-of-scope free variable. -/
def bodyStrayFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some (.ite Core.coreLoc strayExpr (.intConst Core.coreLoc 1) (.intConst Core.coreLoc 0))
        }

/-- Whether `f` is accepted, with the free variables of its checked expressions. -/
def runFunc (f : Core.Function) (Env : Core.Expression.TyEnv := Env0) : Std.Format :=
  match Core.Function.typeCheck C Env f with
  | .ok (f', _) =>
    f!"ACCEPTED freeVars={f'.exprs.map (fun e => (Lambda.LExpr.freeVars e).map (·.1.name))}"
  | .error m => f!"REJECTED {m}"

/-! ### The four expression positions -/

/--
info: REJECTED [(if (∀ (bvar:bool) ($__var0 : bool)) then #1 else #0)] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval runFunc bodyCapturedFunc

/--
info: REJECTED [(∀ (bvar:bool) ($__var0 : bool))] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval runFunc preCapturedFunc

/--
info: REJECTED [(∀ (bvar:bool) ($__var0 : bool))] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval runFunc axCapturedFunc

/--
info: REJECTED [(if (∀ (bvar:bool) ($__var0 : bool)) then #1 else #0)] No free variables are allowed here!
Free Variables: [$__var0]
-/
#guard_msgs in
#eval runFunc measureCapturedFunc

/-! ### An ordinary out-of-scope name

Function checking and direct expression resolution both reject the out-of-scope `y`. -/

/--
info: REJECTED [(if (∀ (bvar:bool) (y : bool)) then #1 else #0)] No free variables are allowed here!
Free Variables: [y]
-/
#guard_msgs in
#eval runFunc bodyStrayFunc

/-- info: ERR Cannot find this fvar in the context! y -/
#guard_msgs in
#eval match Lambda.LExpr.resolve C Env0 strayExpr with
      | .ok (et, _) => f!"OK {et}"
      | .error m => f!"ERR {m}"

/-! ### Variables bound outside the function

A function's body and preconditions may read only its inputs, not variables of the outer
environment. -/

/-- `Env0` with a variable `g : int` bound outside any function. -/
def EnvG : Core.Expression.TyEnv :=
  Env0.pushEmptyContext.addInNewestContext (T := CoreLParams)
    (Strata.Util.HMap.ofList [(⟨"g", ()⟩, Lambda.LTy.forAll [] Lambda.LMonoTy.int)])

/-- `f (x : int) : int := g`, whose body reads the outside variable `g`. -/
def bodyOutsideFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some (.fvar Core.coreLoc ⟨"g", ()⟩ none) }

/-- `f (x : int) : int := x` with the precondition `g == 0`, which reads the outside
    variable `g`. -/
def preOutsideFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none),
    preconditions := [{ expr := .eq Core.coreLoc (.fvar Core.coreLoc ⟨"g", ()⟩ none)
                         (.intConst Core.coreLoc 0), md := Core.coreLoc }] }

/-- `f (x : int) : int := x` with the precondition `x == 0`, which reads only its input. -/
def closedFunc : Core.Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, Lambda.LMonoTy.int)], output := Lambda.LMonoTy.int,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none),
    preconditions := [{ expr := .eq Core.coreLoc (.fvar Core.coreLoc ⟨"x", ()⟩ none)
                         (.intConst Core.coreLoc 0), md := Core.coreLoc }] }

/-- info: REJECTED Function 'f': body uses variables [g] that are not inputs -/
#guard_msgs in
#eval runFunc bodyOutsideFunc EnvG

/-- info: REJECTED Function 'f': precondition uses variables [g] that are not inputs -/
#guard_msgs in
#eval runFunc preOutsideFunc EnvG

/-- info: ACCEPTED freeVars=[[x], [x]] -/
#guard_msgs in
#eval runFunc closedFunc EnvG

end FreeVariables

/-! ## `Core.Factory.typeCheck` on factory functions -/

section FactoryFunctions
open Core.TestUtil (xId yId)

/-! ### Helpers -/

/-- The formal `x`, unannotated. -/
def xOcc : Expression.Expr := .fvar Core.coreLoc xId .none

/-- The type substitution in the environment the checker returns, or the rejection message. -/
def substAfter (fn : Core.Function) (Env : Expression.TyEnv := TEnv.default) : String :=
  match Core.Factory.typeCheck (ctxWith fn) Env with
  | .ok Env' => toString (Std.format Env'.stateSubstInfo.subst)
  | .error e => s!"REJECTED: {e}"

/-! ### Function checks apply to factory entries -/

/-- An ill-typed axiom is rejected even with a well-typed body. -/
def badAxiom : Core.Function :=
  { name := ⟨"badAxiom", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int)],
    output := .int,
    body := some xOcc,
    axioms := [.eq Core.coreLoc xOcc (.const Core.coreLoc (.boolConst true))] }

/-- info: REJECTED: Impossible to unify int with bool. -/
#guard_msgs in
#eval runCheck badAxiom

/-- A precondition must have type `bool`. -/
def badPrecondition : Core.Function :=
  { name := ⟨"badPrecondition", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int)],
    output := .int,
    body := some xOcc,
    preconditions := [{ expr := .const Core.coreLoc (.intConst 3), md := Core.coreLoc }] }

/-- info: REJECTED: Impossible to unify int with bool. -/
#guard_msgs in
#eval runCheck badPrecondition

/-- A measure of type `bool` is rejected: it must be an `int` or a datatype parameter. -/
def badMeasure : Core.Function :=
  { name := ⟨"badMeasure", ()⟩,
    typeArgs := [],
    isRecursive := true,
    inputs := [(xId, .int)],
    output := .int,
    body := some xOcc,
    measure := some (.const Core.coreLoc (.boolConst true)) }

/--
info: REJECTED: recursive function 'badMeasure': decreases expression must have type int or be a parameter of a datatype type, got 'bool'
-/
#guard_msgs in
#eval runCheck badMeasure

/-- Duplicate formal names are rejected. -/
def duplicateFormals : Core.Function :=
  { name := ⟨"duplicateFormals", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int), (xId, .bool)],
    output := .bool,
    body := some (.eq Core.coreLoc xOcc (.const Core.coreLoc (.boolConst true))) }

/-- info: REJECTED: Function 'duplicateFormals': duplicate parameter names [x, x] -/
#guard_msgs in
#eval runCheck duplicateFormals

/-- A constructor cannot carry a body. -/
def constructorWithBody : Core.Function :=
  { name := ⟨"constructorWithBody", ()⟩,
    typeArgs := [],
    isConstr := true,
    inputs := [(xId, .int)],
    output := .int,
    body := some xOcc }

/-- info: REJECTED: Function 'constructorWithBody': a constructor must not have a body -/
#guard_msgs in
#eval runCheck constructorWithBody

/-- A bodyless entry with valid conditions is accepted. -/
def validBodyless : Core.Function :=
  { name := ⟨"validBodyless", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int)],
    output := .int,
    body := none,
    axioms := [.eq Core.coreLoc xOcc xOcc] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck validBodyless

/-! ### A type-parameter formal used as both `int` and `bool` -/

def twoInstances : Core.Function :=
  { name := ⟨"twoInstances", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .ftvar "a")],
    output := .bool,
    body := some (.eq Core.coreLoc
      (.eq Core.coreLoc xOcc (.const Core.coreLoc (.intConst 1)))
      (.eq Core.coreLoc xOcc (.const Core.coreLoc (.boolConst true)))) }

/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval runCheck twoInstances

/-! ### Returning a type-parameter formal at result type `int` -/

def pickInt : Core.Function :=
  { name := ⟨"pickInt", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .ftvar "a")],
    output := .int,
    body := some xOcc }

/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval runCheck pickInt

/-! ### Returning an `int` formal at a type-parameter result -/

def bad : Core.Function :=
  { name := ⟨"bad", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .int)],
    output := .ftvar "a",
    body := some xOcc }

/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval runCheck bad

/-! ### Returning an integer constant at a type-parameter result no input mentions -/

def ghostOut : Core.Function :=
  { name := ⟨"ghostOut", ()⟩,
    typeArgs := ["a"],
    inputs := [],
    output := .ftvar "a",
    body := some (.const Core.coreLoc (.intConst 0)) }

/-- info: REJECTED: Rigid type variable 'a' was refined to 'int' -/
#guard_msgs in
#eval runCheck ghostOut

/-! ### An unused formal of an unregistered type -/

def unusedIn : Core.Function :=
  { name := ⟨"unusedIn", ()⟩,
    typeArgs := [],
    inputs := [(yId, .tcons "NoSuchType" [])],
    output := .bool,
    body := some (.const Core.coreLoc (.boolConst true)) }

/-- info: REJECTED: Function 'unusedIn': signature type NoSuchType is not a registered type -/
#guard_msgs in
#eval runCheck unusedIn

/-! ### A formal at an alias

A registered alias resolves in the signature; an unregistered name is rejected.
-/

def myIntAlias : TypeAlias := { name := "MyInt", typeArgs := [], type := .int }


/-- A function whose input and output use the registered alias `MyInt`. -/
def aliasIn : Core.Function :=
  { name := ⟨"aliasIn", ()⟩,
    typeArgs := [],
    inputs := [(xId, .tcons "MyInt" [])],
    output := .tcons "MyInt" [],
    body := some xOcc }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck aliasIn (aliasEnv [myIntAlias])

/-- Reports each formal name with its resolved signature type. -/
def formalScope (fn : Core.Function) (Env : Expression.TyEnv := TEnv.default)
    : Except Std.Format String := do
  let insR ← fn.inputs.values.mapM (fun ty => (LMonoTy.resolveAliases ty Env).map Prod.fst)
  let rigid := Function.rigidNames (scopeTyNameThunk (ctxWith fn) Env)
    (ctxWith fn) fn fun _ => fn.tyNames fn.annotTys
  let scope := Function.formalsEnv Env rigid (fn.inputs.keys.zip insR)
  .ok (toString (TContext.formatTypes scope.context.types))

-- The `MyInt` formal resolves to `int`.
/-- info: ok: [(x, int)] -/
#guard_msgs in
#eval formalScope aliasIn (aliasEnv [myIntAlias])

/-- A function whose signature uses the unregistered name `MyInt`. -/
def unusedAlias : Core.Function :=
  { name := ⟨"unusedAlias", ()⟩,
    typeArgs := [],
    inputs := [(yId, .tcons "MyInt" [])],
    output := .bool,
    body := some (.const Core.coreLoc (.boolConst true)) }

/-- info: REJECTED: Function 'unusedAlias': signature type MyInt is not a registered type -/
#guard_msgs in
#eval runCheck unusedAlias

-- `PureFunc.typeCheck` renames the type parameter throughout and resolves
-- `MyInt` in the signature; the result keeps fields it does not check, such as
-- `isRecursive` and `lemmas`.
private def aliasReservedPureFunc : PureFunc Expression :=
  let x : Expression.Expr := .fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "$__ty0"))
  let n : Expression.Expr := .fvar Core.coreLoc ⟨"n", ()⟩ none
  { name := ⟨"q", ()⟩, typeArgs := ["$__ty0"], isRecursive := true,
    inputs := [(⟨"x", ()⟩, .forAll [] (.ftvar "$__ty0")),
               (⟨"n", ()⟩, .forAll [] (.tcons "MyInt" []))],
    output := .forAll [] (.tcons "MyInt" []), body := some n,
    preconditions := [{ expr := .eq Core.coreLoc x x, md := Core.coreLoc }],
    axioms := [LExpr.all Core.coreLoc "y" (some (.ftvar "$__ty0"))
               (.eq Core.coreLoc (.bvar Core.coreLoc 0) (.bvar Core.coreLoc 0))],
    measure := some (.ite Core.coreLoc (.eq Core.coreLoc x x) n n), lemmas := ["q_wf"] }

/--
info: ok: [a] (x, a) (n, int) int
isRecursive: true lemmas: [q_wf]
precondition: [[a, a]]
axiom: [[a]]
measure: some [a, a]
-/
#guard_msgs in
#eval match PureFunc.typeCheck C (aliasEnv [myIntAlias]) aliasReservedPureFunc with
  | .ok (d, _, _) =>
    f!"ok: {d.typeArgs} {d.inputs} {d.output}\n\
       isRecursive: {d.isRecursive} lemmas: {d.lemmas}\n{annotTyVarLines d}"
  | .error e => f!"error: {e}"

/-! ### Monomorphic and polymorphic bodies -/

/-- A monomorphic function using its formal at the declared type. -/
def monoOk : Core.Function :=
  { name := ⟨"monoOk", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int)],
    output := .bool,
    body := some (.eq Core.coreLoc xOcc (.const Core.coreLoc (.intConst 1))) }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck monoOk

/-- A polymorphic identity function. -/
def idPoly : Core.Function :=
  { name := ⟨"idPoly", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .ftvar "a")],
    output := .ftvar "a",
    body := some xOcc }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck idPoly

/-- A polymorphic function returning the formal whose type matches the result. -/
def fstPoly : Core.Function :=
  { name := ⟨"fstPoly", ()⟩,
    typeArgs := ["a", "b"],
    inputs := [(xId, .ftvar "a"), (yId, .ftvar "b")],
    output := .ftvar "a",
    body := some xOcc }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck fstPoly

/-- A polymorphic function using its formal repeatedly at one type. -/
def eqPoly : Core.Function :=
  { name := ⟨"eqPoly", ()⟩,
    typeArgs := ["a"],
    inputs := [(xId, .ftvar "a")],
    output := .bool,
    body := some (.eq Core.coreLoc xOcc xOcc) }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck eqPoly

/-- A monomorphic body using a formal at another type is rejected. -/
def monoClash : Core.Function :=
  { name := ⟨"monoClash", ()⟩,
    typeArgs := [],
    inputs := [(xId, .int)],
    output := .bool,
    body := twoInstances.body }

/-- info: REJECTED: Impossible to unify int with bool. -/
#guard_msgs in
#eval runCheck monoClash

/-! ### Checking does not change an empty caller substitution -/

/-- info: "[]" -/
#guard_msgs in
#eval substAfter idPoly

/-! ### The default factory has no bodies and is accepted -/

/-- info: 0 -/
#guard_msgs in
#eval (Core.Factory.toArray.toList.filter (fun f => f.body.isSome)).length

/-- info: ACCEPTED -/
#guard_msgs in
#eval verdictOf (Core.Factory.typeCheck initTyContext TEnv.default)

end FactoryFunctions

/-! ## Bare-variable decreases expressions

A decreases expression reads only formals and has type `int`, or is a formal of a datatype type.
-/

/-- The formal parameter `x`. -/
private def measureX : CoreIdent := ⟨"x", ()⟩

/-- A name that is not a formal parameter. -/
private def strayMeasureName : CoreIdent := ⟨"zzz", ()⟩

/-- A bodyless recursive integer function. -/
private def measuredIntFunction : Function :=
  { name := ⟨"measureInt", ()⟩
    typeArgs := []
    isRecursive := true
    inputs := [(measureX, .int)]
    output := .int
    body := none }

/-- A recursive Boolean function measured by its formal `x`. -/
private def measuredBoolFunction : Function :=
  { name := ⟨"measureBool", ()⟩
    typeArgs := []
    isRecursive := true
    inputs := [(measureX, .bool)]
    output := .bool
    body := none
    measure := some (.fvar Core.coreLoc measureX none) }

/-- An environment binding the non-formal `zzz`. -/
private def ambientMeasureEnv : Expression.TyEnv :=
  Function.formalsEnv Env [] [(strayMeasureName, .int)]

/--
info: REJECTED: [zzz] No free variables are allowed here!
Free Variables: [zzz]
-/
#guard_msgs in
#eval functionVerdict (Env := Env)
  { measuredIntFunction with measure := some (.fvar Core.coreLoc strayMeasureName none) }

/--
info: REJECTED: recursive function 'measureInt': decreases expression uses variables [zzz] that are not parameters
-/
#guard_msgs in
#eval functionVerdict (Env := ambientMeasureEnv)
  { measuredIntFunction with measure := some (.fvar Core.coreLoc strayMeasureName none) }

/-- info: ACCEPTED -/
#guard_msgs in
#eval functionVerdict (Env := Env)
  { measuredIntFunction with measure := some (.fvar Core.coreLoc measureX none) }

/--
info: REJECTED: recursive function 'measureBool': decreases expression must have type int or be a parameter of a datatype type, got 'bool'
-/
#guard_msgs in
#eval functionVerdict measuredBoolFunction (Env := Env)

/-- info: ACCEPTED -/
#guard_msgs in
#eval functionVerdict (Env := Env)
  { measuredIntFunction with measure := some (.intConst Core.coreLoc 0) }

/--
info: REJECTED: recursive function 'measureInt': decreases expression must have type int or be a parameter of a datatype type, got 'bool'
-/
#guard_msgs in
#eval functionVerdict (Env := Env)
  { measuredIntFunction with measure := some (.boolConst Core.coreLoc true) }

-- `decreases (x : bool)` on the formal `x : int` is rejected.
/-- info: REJECTED: Impossible to unify bool with int. -/
#guard_msgs in
#eval functionVerdict (Env := Env)
  { measuredIntFunction with measure := some (.fvar Core.coreLoc measureX (some .bool)) }

-- The bare `int` formal `x` is stored at `int`.
/-- info: x : some int -/
#guard_msgs in
#eval match Function.typeCheck C Env
    { measuredIntFunction with measure := some (.fvar Core.coreLoc measureX none) } with
  | .ok (func', _) =>
    match func'.measure with
    | some (.fvar _ x ty) => f!"{x} : {ty}"
    | _ => f!"not a variable"
  | .error e => e

-- A recursive list function measured by its datatype formal `xs` is accepted.
open Strata in
private def datatypeMeasurePgm :=
#strata
program Core;
datatype IntList { Nil(), Cons(hd: int, tl: IntList) };
rec function len (@[cases] xs : IntList) : int
  decreases xs
{
  if IntList..isNil(xs) then 0 else int.add(1, len(IntList..tl(xs)))
};
#end

/--
info: ACCEPTED
-/
#guard_msgs in
#eval coreVerdict (translate datatypeMeasurePgm)

/-! ## A decreases expression belongs only to a recursive function -/

section MeasureRequiresRecursion

/-- A nonrecursive function with no measure. -/
private def baseFunc : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [],
    inputs := [(⟨"x", ()⟩, LMonoTy.int)], output := LMonoTy.int,
    body := some (.fvar Core.coreLoc ⟨"x", ()⟩ none) }

/-- The bare parameter measure `x`. -/
private def bareMeasure : Expression.Expr := .fvar Core.coreLoc ⟨"x", ()⟩ none

/-- The computed measure `if x == x then 0 else 1`. -/
private def computedMeasure : Expression.Expr :=
  .ite Core.coreLoc (.eq Core.coreLoc (.fvar Core.coreLoc ⟨"x", ()⟩ none)
                     (.fvar Core.coreLoc ⟨"x", ()⟩ none))
    (.intConst Core.coreLoc 0) (.intConst Core.coreLoc 1)

/-! ### A measure without the recursion mark -/

/--
info: REJECTED: Function 'f': a decreases expression is only allowed on a recursive function
-/
#guard_msgs in
#eval functionVerdict { baseFunc with measure := some bareMeasure }

/--
info: REJECTED: Function 'f': a decreases expression is only allowed on a recursive function
-/
#guard_msgs in
#eval functionVerdict { baseFunc with measure := some computedMeasure }

/-! ### Accepted recursion and measure combinations -/

/-! A recursive definition may carry either a parameter measure or an integer-valued measure. -/

/-- info: ACCEPTED -/
#guard_msgs in
#eval functionVerdict
  { baseFunc with isRecursive := true, measure := some bareMeasure }

/-- info: ACCEPTED -/
#guard_msgs in
#eval functionVerdict
  { baseFunc with isRecursive := true, measure := some computedMeasure }

/-! A definition with neither a measure nor the recursion mark. -/

/-- info: ACCEPTED -/
#guard_msgs in
#eval functionVerdict baseFunc

/-- A recursive block whose single member is marked recursive and carries a computed measure. -/
private def recBlockMeasurePgm : Program :=
  { decls := [.recFuncBlock
      [{ baseFunc with isRecursive := true, measure := some computedMeasure }] .empty] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict recBlockMeasurePgm

/-! ### A recursive block member without the recursion mark

A member with a measure but no recursion mark fails the block-membership rule first. -/

/-- A recursive block whose member carries a computed measure but is not marked recursive. -/
private def recBlockNoRecMeasurePgm : Program :=
  { decls := [.recFuncBlock [{ baseFunc with measure := some computedMeasure }] .empty] }

/-- info: REJECTED: recursive function block member 'f' must be marked recursive -/
#guard_msgs in
#eval firstLineOf <| programVerdict recBlockNoRecMeasurePgm

/-! ### A top-level function declaration

A top-level function with a measure is rejected; without one it is accepted. -/

/-- info: REJECTED: Function 'f': a decreases expression is only allowed on a recursive function -/
#guard_msgs in
#eval firstLineOf <| programVerdict
  { decls := [.func { baseFunc with measure := some computedMeasure } .empty] }

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| programVerdict { decls := [.func baseFunc .empty] }

/-! ### A factory function

A factory function may be marked recursive; with the mark it is accepted. -/

/-- info: REJECTED: Function 'f': a decreases expression is only allowed on a recursive function -/
#guard_msgs in
#eval runCheck { baseFunc with measure := some computedMeasure }

/-- info: ACCEPTED -/
#guard_msgs in
#eval runCheck { baseFunc with isRecursive := true, measure := some computedMeasure }

end MeasureRequiresRecursion

end Core.FunctionTypeTests
