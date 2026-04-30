/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.ProgramType

/-!
# Test: fresh type variables as placeholder types

When Laurel type translation encounters an unknown type, `throwTypeDiagnostic`
returns a fresh type variable (`ftvar`) rather than a concrete type like `Error`.
A fresh type variable can be unified with any type by the Core type checker,
whereas a concrete placeholder like `Error` would cause "Impossible to unify"
failures.

These tests verify:
1. A Core program using `ftvar` placeholder types passes type checking
   (the ftvar unifies with the expected concrete type).
2. A Core program using `tcons "Error"` as a placeholder FAILS type checking
   (Error does not unify with int), documenting the bug that the ftvar fix solves.
-/

open Strata

/-- Build a minimal Core program directly (not via DDM syntax) to precisely
    control the placeholder type used for `x`. DDM parsing would infer types,
    defeating the purpose of testing type-checker behavior on specific types.
    `procedure main() { var x : <placeholderTy> := 0; var y : int := x; }`
    The placeholder type of `x` must unify with `int` when `x` is assigned to `y`. -/
private def mkTestProgram (placeholderTy : Lambda.LMonoTy) : Core.Program :=
  let md : Imperative.MetaData Core.Expression := #[]
  let zero : Lambda.LExpr Core.CoreLParams.mono := .const () (.intConst 0)
  let xIdent : Core.CoreIdent := ⟨"x", ()⟩
  let yIdent : Core.CoreIdent := ⟨"y", ()⟩
  let xRef : Lambda.LExpr Core.CoreLParams.mono := .fvar () xIdent (some placeholderTy)
  let body : List Core.Statement := [
    Core.Statement.init xIdent (Lambda.LTy.forAll [] placeholderTy) (.det zero) md,
    Core.Statement.init yIdent (Lambda.LTy.forAll [] .int) (.det xRef) md
  ]
  let proc : Core.Procedure := {
    header := { name := ⟨"main", ()⟩, typeArgs := [], inputs := [], outputs := [] }
    spec := { preconditions := [], postconditions := [] }
    body := body
  }
  { decls := [.proc proc #[]] }

private def typeCheckProgram (pgm : Core.Program) : Except String Unit :=
  let Ctx := { Lambda.LContext.default with
    functions := Core.Factory, knownTypes := Core.KnownTypes }
  let Env := Lambda.TEnv.default
  match Core.Program.typeCheck Ctx Env pgm with
  | .ok _ => .ok ()
  | .error e => .error s!"{e.format none}"

/-- Test: ftvar placeholder unifies with int — type checking succeeds. -/
def test_ftvar_unifies : IO Unit := do
  let pgm := mkTestProgram (.ftvar "$__ty_unused_1")
  match typeCheckProgram pgm with
  | .ok () => IO.println "  ✓ ftvar placeholder unifies with int"
  | .error e => throw (IO.userError s!"  ✗ ftvar should unify with int: {e}")

/-- Test: tcons "Error" does NOT unify with int — type checking fails.
    This documents the bug that the ftvar fix solves. The Error type
    is intentionally not registered; any concrete type constructor
    (registered or not) fails to unify with int. -/
def test_error_does_not_unify : IO Unit := do
  let pgm := mkTestProgram (.tcons "Error" [])
  match typeCheckProgram pgm with
  | .ok () => throw (IO.userError "  ✗ Error should not unify with int")
  | .error _ => IO.println "  ✓ Error placeholder correctly fails to unify"

def main : IO Unit := do
  IO.println "ThrowTypeDiagnosticTest:"
  test_ftvar_unifies
  test_error_does_not_unify
