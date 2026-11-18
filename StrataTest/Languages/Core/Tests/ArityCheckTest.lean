/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.DL.Lambda.LTyWF
import StrataTest.Languages.Core.Tests.TestUtil

/-! ## Arity-check tests for known type constructors

The Core typechecker rejects a known type constructor applied at the wrong arity. `Sequence` is
arity 1, so `Sequence a a` is rejected in a datatype constructor, a function or procedure
signature, and a local `var` type; `Sequence a` is accepted. Type synonyms and binder annotations
are checked too.

Tests drive the AST/typechecker path directly (the DDM concrete-syntax path catches arity
mismatches at translation). The datatype cases pin the exact error and the others its first line,
since the full message embeds the hash-ordered known-types dump. The typechecker-spec
counterpart is `ArityCheckSpecTest.lean`.
-/

namespace Core.ArityCheckTest

open _root_.Lambda Imperative
open LTy.Syntax LExpr.SyntaxMono

/-- Ambient context with Core's built-in functions and known types, so that
    `Sequence` is a known arity-1 type constructor (as in `Core.typeCheck`). -/
private def coreContext : LContext CoreLParams :=
  { LContext.default with
      functions := Core.Factory,
      knownTypes := Core.KnownTypes }

open Core.TestUtil (coreVerdict firstLineOf firstLineVerdict)

---------------------------------------------------------------------
-- Datatype constructor argument
---------------------------------------------------------------------

/-- `datatype Foo<a> { Bar(x : Sequence a a) }` — `Sequence` applied to 2 args. -/
private def fooBadArity : LDatatype Unit :=
  { name := "Foo", typeArgs := ["a"],
    constrs := [{ name := "Bar",
                  args := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
                  testerName := "isBar" }],
    constrs_ne := rfl }

/-- info: Error in datatype Foo, constructor Bar: Type constructor 'Sequence' expects 1 type argument(s) but was given 2 -/
#guard_msgs in
#eval match coreContext.addMutualBlock [fooBadArity] with
  | .ok _ => f!"typechecks"
  | .error e => Std.format e

/-- Nested arity error: outer `Sequence a` is correct, inner `Map a` is not. -/
private def fooNestedBadArity : LDatatype Unit :=
  { name := "FooNested", typeArgs := ["a"],
    constrs := [{ name := "BarNested",
                  args := [(⟨"x", ()⟩, .tcons "Sequence" [.tcons "Map" [.ftvar "a"]])],
                  testerName := "isBarNested" }],
    constrs_ne := rfl }

/-- info: Error in datatype FooNested, constructor BarNested: Type constructor 'Map' expects 2 type argument(s) but was given 1 -/
#guard_msgs in
#eval match coreContext.addMutualBlock [fooNestedBadArity] with
  | .ok _ => f!"typechecks"
  | .error e => Std.format e

/-- Control: correct-arity `Sequence a`. -/
private def fooOkArity : LDatatype Unit :=
  { name := "FooOk", typeArgs := ["a"],
    constrs := [{ name := "BarOk",
                  args := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a"])],
                  testerName := "isBarOk" }],
    constrs_ne := rfl }

/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineVerdict (coreContext.addMutualBlock [fooOkArity])

---------------------------------------------------------------------
-- Function signature: `function f<a>(x : Sequence a a) : int;`
---------------------------------------------------------------------

private def badArityFunc : Core.Function :=
  { name := ⟨"f", ()⟩,
    typeArgs := ["a"],
    inputs := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
    output := .int }

private def coreTyEnv : Core.Expression.TyEnv := default

/-- info: REJECTED: Function 'f': signature type (Sequence a a) is not a registered type -/
#guard_msgs in
#eval firstLineVerdict (Function.typeCheck coreContext coreTyEnv badArityFunc)

---------------------------------------------------------------------
-- Procedure signature: `procedure p<a>(x : Sequence a a) { }`
---------------------------------------------------------------------

private def badArityProc : Core.Procedure :=
  { header := { name := ⟨"p", ()⟩,
                typeArgs := ["a"],
                inputs := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
                outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [] }

private def badArityProcPgm : Core.Program :=
  { decls := [.proc badArityProc .empty] }

/-- info: REJECTED: Procedure 'p': signature type (Sequence a a) is not a registered type -/
#guard_msgs in
#eval firstLineOf <| coreVerdict badArityProcPgm

---------------------------------------------------------------------
-- Command: `var y : Sequence a a := *` inside a procedure body
---------------------------------------------------------------------

private def badArityVarProc : Core.Procedure :=
  { header := { name := ⟨"q", ()⟩,
                typeArgs := ["a"],
                inputs := [],
                outputs := [] },
    spec := { preconditions := [], postconditions := [] },
    body := .structured [
      Statement.init "y" (.forAll [] (.tcons "Sequence" [.ftvar "a", .ftvar "a"])) .nondet .empty
    ] }

private def badArityVarPgm : Core.Program :=
  { decls := [.proc badArityVarProc .empty] }

/--
info: REJECTED: Procedure 'q': Type (Sequence a a) is not an instance of a previously registered type: Type constructor 'Sequence' expects 1 type argument(s) but was given 2
-/
#guard_msgs in
#eval firstLineOf <| coreVerdict badArityVarPgm

-- The direct resolved checker rejects a known constructor at the wrong arity.
/--
info: REJECTED: Type (Sequence a a) is not an instance of a previously registered type: Type constructor 'Sequence' expects 1 type argument(s) but was given 2
-/
#guard_msgs in
#eval firstLineVerdict (LMonoTy.typeCheckResolved (.tcons "Sequence" [.ftvar "a", .ftvar "a"])
  coreContext TyVarAdmissibility.all)

-- The direct resolved checker accepts the same constructor at its registered arity.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineVerdict (LMonoTy.typeCheckResolved (.tcons "Sequence" [.ftvar "a"])
  coreContext TyVarAdmissibility.all)

---------------------------------------------------------------------
-- Type synonyms
---------------------------------------------------------------------

/-- A program made of the given type synonyms, declared in order. -/
private def synPgm (tss : List TypeSynonym) : Core.Program :=
  { decls := tss.map (fun ts => .type (.syn ts) .empty) }

/-- `type A a := Map a int`. -/
private def synMapA : TypeSynonym :=
  { name := "A", typeArgs := ["a"], type := .tcons "Map" [.ftvar "a", .int] }

-- `type A := Foo` is rejected: `Foo` is not a registered type.
/-- info: REJECTED: Type Foo is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (synPgm [{ name := "A", typeArgs := [], type := .tcons "Foo" [] }])

-- An alias name with a reserved internal prefix is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (synPgm [{ name := "$__tyA", typeArgs := [], type := .int }])

-- `type A := int` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (synPgm [{ name := "A", typeArgs := [], type := .int }])

-- `type A a := Map a int; type B := A bool` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (synPgm [synMapA, { name := "B", typeArgs := [], type := .tcons "A" [.bool] }])

---------------------------------------------------------------------
-- Binder annotations
---------------------------------------------------------------------

/-- A program declaring `pre` and then a procedure `p` with the given type parameters and inputs,
    whose body asserts `e`. -/
private def assertPgm (pre : List Core.Decl) (typeArgs : List String)
    (inputs : List (CoreIdent × LMonoTy)) (e : Core.Expression.Expr) : Core.Program :=
  { decls := pre ++ [.proc
      { header := { name := ⟨"p", ()⟩, typeArgs := typeArgs, inputs := inputs, outputs := [] },
        spec := { preconditions := [], postconditions := [] },
        body := .structured [Statement.assert "a" e .empty] } .empty] }

/-- `forall x : ty :: true`. -/
private def forallTrue (ty : LMonoTy) : Core.Expression.Expr :=
  LExpr.all Core.coreLoc "x" (some ty) (LExpr.boolConst Core.coreLoc true)

/-- `(λx:ty. true) == (λy:ty. true)`. -/
private def lambdasEq (ty : LMonoTy) : Core.Expression.Expr :=
  .eq Core.coreLoc (.abs Core.coreLoc "x" (some ty) (LExpr.boolConst Core.coreLoc true))
    (.abs Core.coreLoc "y" (some ty) (LExpr.boolConst Core.coreLoc true))

-- `forall x : Foo :: true` is rejected: `Foo` is not a registered type.
/-- info: REJECTED: Procedure 'p': Type Foo is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue (.tcons "Foo" [])))

-- `(λx:Foo. true) == (λy:Foo. true)` is rejected: `Foo` is not a registered type.
/-- info: REJECTED: Procedure 'p': Type Foo is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (lambdasEq (.tcons "Foo" [])))

-- `forall x : int :: true` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue .int))

-- `forall x : b :: true` is rejected: no declaration in scope binds `b`.
/-- info: REJECTED: Procedure 'p': type variable `b` is not in scope -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue (.ftvar "b")))

-- `forall x : $__ty999 :: true` is rejected: `$__ty999` is not in scope.
/--
info: REJECTED: Procedure 'p': type variable `$__ty999` is not in scope
-/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue (.ftvar "$__ty999")))

-- `type A := int; forall x : A :: true` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (assertPgm [.type (.syn { name := "A", typeArgs := [], type := .int }) .empty] [] []
    (forallTrue (.tcons "A" [])))

-- `(λx:int. true) == (λy:int. true)` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (lambdasEq .int))

-- `procedure p<a>(y : a) { assert forall x : a :: true }` is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (assertPgm [] ["a"] [(⟨"y", ()⟩, .ftvar "a")] (forallTrue (.ftvar "a")))

---------------------------------------------------------------------
-- Arity diagnostics
---------------------------------------------------------------------

/-- A program declaring `pre` and then a procedure whose body is `var y : ty := *`. -/
private def varPgm (pre : List Core.Decl) (ty : LMonoTy) : Core.Program :=
  { decls := pre ++ [.proc
      { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [], outputs := [] },
        spec := { preconditions := [], postconditions := [] },
        body := .structured [Statement.init "y" (.forAll [] ty) .nondet .empty] } .empty] }

-- A local variable type applying `Map` to one argument is rejected.
/-- info: REJECTED: Procedure 'p': Type (Map int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 1 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (varPgm [] (.tcons "Map" [.int]))

-- A local variable type applying `Map` to three arguments is rejected.
/-- info: REJECTED: Procedure 'p': Type (Map int int int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 3 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (varPgm [] (.tcons "Map" [.int, .int, .int]))

-- A local variable type applying the unary synonym `A` to no argument is rejected.
/-- info: REJECTED: Procedure 'p': Type A is not an instance of a previously registered type: Type alias 'A' expects 1 type argument(s) but was given 0 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (varPgm [.type (.syn synMapA) .empty] (.tcons "A" []))

-- A local variable type applying the unary synonym `A` to two arguments is rejected.
/-- info: REJECTED: Procedure 'p': Type (A int bool) is not an instance of a previously registered type: Type alias 'A' expects 1 type argument(s) but was given 2 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (varPgm [.type (.syn synMapA) .empty] (.tcons "A" [.int, .bool]))

-- An arity error nested inside a local variable type is reported.
/-- info: REJECTED: Procedure 'p': Type (Map int A) is not an instance of a previously registered type: Type alias 'A' expects 1 type argument(s) but was given 0 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (varPgm [.type (.syn synMapA) .empty] (.tcons "Map" [.int, .tcons "A" []]))

-- A binder annotation applying `Map` to one argument is rejected.
/-- info: REJECTED: Procedure 'p': Type (Map int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 1 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue (.tcons "Map" [.int])))

-- A binder annotation applying `Map` to three arguments is rejected.
/-- info: REJECTED: Procedure 'p': Type (Map int int int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 3 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (assertPgm [] [] [] (forallTrue (.tcons "Map" [.int, .int, .int])))

-- A synonym body applying `Map` to one argument is rejected.
/-- info: REJECTED: Type (Map int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 1 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (synPgm [{ name := "B", typeArgs := [], type := .tcons "Map" [.int] }])

-- A synonym body applying `Map` to three arguments is rejected.
/-- info: REJECTED: Type (Map int int int) is not an instance of a previously registered type: Type constructor 'Map' expects 2 type argument(s) but was given 3 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (synPgm [{ name := "B", typeArgs := [], type := .tcons "Map" [.int, .int, .int] }])

-- A synonym body applying the unary synonym `A` to no argument is rejected.
/-- info: REJECTED: Type A is not an instance of a previously registered type: Type alias 'A' expects 1 type argument(s) but was given 0 -/
#guard_msgs in
#eval firstLineOf <| coreVerdict
  (synPgm [synMapA, { name := "B", typeArgs := [], type := .tcons "A" [] }])

-- An unregistered type gets the generic message, with no arity note.
/-- info: REJECTED: Procedure 'p': Type Foo is not an instance of a previously registered type! -/
#guard_msgs in
#eval firstLineOf <| coreVerdict (varPgm [] (.tcons "Foo" []))

end Core.ArityCheckTest
