/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-! ## Arity-check tests for known type constructors

The Core typechecker rejects a known type constructor applied at the wrong arity.
`Sequence` is arity 1, so `Sequence a a` is rejected in a datatype constructor,
a function or procedure signature, and a local `var` type; `Sequence a` is
accepted.

Tests drive the AST/typechecker path directly (the DDM concrete-syntax path
catches arity mismatches at translation). The datatype case pins the exact arity
error; the function/procedure/command cases check `Except.isOk`, since their
rejection message embeds the hash-ordered known-types dump. The declarative-spec
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

/-- info: Error in datatype Foo, constructor Bar: Type constructor 'Sequence' expects 1 argument(s) but is applied to 2 -/
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

/-- info: Error in datatype FooNested, constructor BarNested: Type constructor 'Map' expects 2 argument(s) but is applied to 1 -/
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

#guard (coreContext.addMutualBlock [fooOkArity]).isOk

---------------------------------------------------------------------
-- Function signature: `function f<a>(x : Sequence a a) : int;`
---------------------------------------------------------------------

private def badArityFunc : Core.Function :=
  { name := ⟨"f", ()⟩,
    typeArgs := ["a"],
    inputs := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
    output := .int }

private def coreTyEnv : Core.Expression.TyEnv := default

#guard !(Function.typeCheck coreContext coreTyEnv badArityFunc).isOk

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

#guard !(Core.typeCheck .default badArityProcPgm).isOk

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

#guard !(Core.typeCheck .default badArityVarPgm).isOk

end Core.ArityCheckTest
