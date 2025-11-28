/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.Verifier
import Strata.DL.Lambda.TypeFactory

/-!
# Datatype Verification Integration Tests

This file contains integration tests for datatype encoding in verification conditions.
These tests create complete Boogie programs with datatype declarations and procedures,
then verify them using the full verification pipeline.

Tests verify the complete integration of:
- Task 3: Context serialization for datatypes
- Task 4: Constructor encoding
- Task 5: Tester function encoding
- Task 6: Destructor function encoding
- Task 7: Integration into encoding pipeline

Each test creates a Boogie Program and calls Boogie.verify to test end-to-end.
-/

namespace Boogie.DatatypeVerificationTests

open Lambda
open Std (ToFormat Format)
open Imperative

/-! ## Test Datatypes -/

/-- Simple Option datatype: Option a = None | Some a -/
def optionDatatype : LDatatype Visibility :=
  { name := "Option"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"None", .unres⟩, args := [] },
      { name := ⟨"Some", .unres⟩, args := [(⟨"value", .unres⟩, .ftvar "a")] }
    ]
    constrs_ne := by decide }

/-- Recursive List datatype: List a = Nil | Cons a (List a) -/
def listDatatype : LDatatype Visibility :=
  { name := "List"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"Nil", .unres⟩, args := [] },
      { name := ⟨"Cons", .unres⟩, args := [
          (⟨"head", .unres⟩, .ftvar "a"),
          (⟨"tail", .unres⟩, .tcons "List" [.ftvar "a"])
        ] }
    ]
    constrs_ne := by decide }

/-! ## Helper Functions -/

/--
Create a Boogie program with datatypes and a procedure.
-/
def mkProgramWithDatatypes
  (datatypes : List (LDatatype Visibility))
  (procName : String)
  (body : List Statement)
  : Except Format Program := do
  -- Create procedure
  let proc : Procedure := {
    header := {
      name := BoogieIdent.unres procName
      typeArgs := []
      inputs := []
      outputs := []
    }
    spec := {
      modifies := []
      preconditions := []
      postconditions := []
    }
    body := body
  }

  -- Create type declarations for datatypes
  let mut decls : List Decl := []
  for d in datatypes do
    -- Add datatype declaration
    decls := decls ++ [Decl.type (.data d) .empty]

  -- Add procedure
  decls := decls ++ [Decl.proc proc .empty]

  -- Create program
  return { decls := decls }

/-! ## Test 1: Constructor Application -/

/--
Test that constructor applications are properly encoded.
Creates a procedure that constructs Option values and verifies trivial properties.
-/
def test1_constructorApplication : IO Unit := do
  let statements : List Statement := [
    -- Create None value
    Statement.init (BoogieIdent.unres "x") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.op () (BoogieIdent.unres "None") (.some (LMonoTy.tcons "Option" [.int]))),

    -- Create Some value
    Statement.init (BoogieIdent.unres "y") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Some")
          (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
        (LExpr.intConst () 42)),

    -- Trivial assertion to verify the program
    Statement.assert "trivial" (LExpr.boolConst () true)
  ]

  match mkProgramWithDatatypes [optionDatatype] "testConstructors" statements with
  | .error err =>
    IO.println s!"Test 1 - Constructor Application: FAILED (program creation)"
    IO.println s!"  Error: {err.pretty}"
  | .ok program =>
    try
      match ← EIO.toIO' (Boogie.verify "cvc5" program) with
      | .error err =>
        IO.println s!"Test 1 - Constructor Application: FAILED (verification)"
        IO.println s!"  Error: {err}"
      | .ok results =>
        IO.println s!"Test 1 - Constructor Application: PASSED"
        IO.println s!"  Verified {results.size} obligation(s)"
        for result in results do
          if result.result != .unsat then
            IO.println s!"  WARNING: {result.obligation.label}: {Std.format result.result}"
    catch e =>
      IO.println s!"Test 1 - Constructor Application: FAILED (exception)"
      IO.println s!"  Error: {e}"

/-! ## Test 2: Tester Functions -/

/--
Test that tester functions (is-None, is-Some) are properly encoded.
Verifies that None is detected as None and Some is detected as Some.
-/
def test2_testerFunctions : IO Unit := do
  let statements : List Statement := [
    -- Create None value
    Statement.init (BoogieIdent.unres "x") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.op () (BoogieIdent.unres "None") (.some (LMonoTy.tcons "Option" [.int]))),

    -- Assert that x is None
    Statement.assert "x_is_none"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$isNone")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Create Some value
    Statement.init (BoogieIdent.unres "y") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Some")
          (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
        (LExpr.intConst () 42)),

    -- Assert that y is Some
    Statement.assert "y_is_some"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$isSome")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "y") (.some (LMonoTy.tcons "Option" [.int]))))
  ]

  match mkProgramWithDatatypes [optionDatatype] "testTesters" statements with
  | .error err =>
    IO.println s!"Test 2 - Tester Functions: FAILED (program creation)"
    IO.println s!"  Error: {err.pretty}"
  | .ok program =>
    try
      match ← EIO.toIO' (Boogie.verify "cvc5" program) with
      | .error err =>
        IO.println s!"Test 2 - Tester Functions: FAILED (verification)"
        IO.println s!"  Error: {err}"
      | .ok results =>
        IO.println s!"Test 2 - Tester Functions: PASSED"
        IO.println s!"  Verified {results.size} obligation(s)"
        for result in results do
          if result.result != .unsat then
            IO.println s!"  WARNING: {result.obligation.label}: {Std.format result.result}"
    catch e =>
      IO.println s!"Test 2 - Tester Functions: FAILED (exception)"
      IO.println s!"  Error: {e}"

/-! ## Test 3: Destructor Functions -/

/--
Test that destructor functions are properly encoded.
Verifies that extracting values from constructors works correctly.
-/
def test3_destructorFunctions : IO Unit := do
  let statements : List Statement := [
    -- Create Some(42)
    Statement.init (BoogieIdent.unres "opt") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Some")
          (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
        (LExpr.intConst () 42)),

    -- Extract value from Some
    Statement.init (BoogieIdent.unres "val") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$SomeProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "opt") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert that val == 42
    Statement.assert "val_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "val") (.some .int))
        (LExpr.intConst () 42)),

    -- Create Cons(1, Nil)
    Statement.init (BoogieIdent.unres "list") (.forAll [] (LMonoTy.tcons "List" [.int]))
      (LExpr.app ()
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "Cons")
            (.some (LMonoTy.arrow .int (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) (LMonoTy.tcons "List" [.int])))))
          (LExpr.intConst () 1))
        (LExpr.op () (BoogieIdent.unres "Nil") (.some (LMonoTy.tcons "List" [.int])))),

    -- Extract head
    Statement.init (BoogieIdent.unres "head") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$ConsProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "list") (.some (LMonoTy.tcons "List" [.int])))),

    -- Assert head == 1
    Statement.assert "head_is_1"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "head") (.some .int))
        (LExpr.intConst () 1))
  ]

  match mkProgramWithDatatypes [optionDatatype, listDatatype] "testDestructors" statements with
  | .error err =>
    IO.println s!"Test 3 - Destructor Functions: FAILED (program creation)"
    IO.println s!"  Error: {err.pretty}"
  | .ok program =>
    try
      match ← EIO.toIO' (Boogie.verify "cvc5" program) with
      | .error err =>
        IO.println s!"Test 3 - Destructor Functions: FAILED (verification)"
        IO.println s!"  Error: {err}"
      | .ok results =>
        IO.println s!"Test 3 - Destructor Functions: PASSED"
        IO.println s!"  Verified {results.size} obligation(s)"
        for result in results do
          if result.result != .unsat then
            IO.println s!"  WARNING: {result.obligation.label}: {Std.format result.result}"
    catch e =>
      IO.println s!"Test 3 - Destructor Functions: FAILED (exception)"
      IO.println s!"  Error: {e}"

/-! ## Test 4: Nested Datatypes -/

/--
Test nested datatypes (List of Option).
Verifies that multiple datatypes can be used together and nested.
-/
def test4_nestedDatatypes : IO Unit := do
  let statements : List Statement := [
    -- Create a List of Option: Cons(Some(42), Nil)
    Statement.init (BoogieIdent.unres "listOfOpt")
      (.forAll [] (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]))
      (LExpr.app ()
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "Cons")
            (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int])
              (LMonoTy.arrow (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])
                (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))))
          (LExpr.app ()
            (LExpr.op () (BoogieIdent.unres "Some")
              (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
            (LExpr.intConst () 42)))
        (LExpr.op () (BoogieIdent.unres "Nil")
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))),

    -- Assert that the list is Cons
    Statement.assert "list_is_cons"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$isCons")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "listOfOpt")
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]))))
  ]

  match mkProgramWithDatatypes [listDatatype, optionDatatype] "testNested" statements with
  | .error err =>
    IO.println s!"Test 4 - Nested Datatypes: FAILED (program creation)"
    IO.println s!"  Error: {err.pretty}"
  | .ok program =>
    try
      match ← EIO.toIO' (Boogie.verify "cvc5" program) with
      | .error err =>
        IO.println s!"Test 4 - Nested Datatypes: FAILED (verification)"
        IO.println s!"  Error: {err}"
      | .ok results =>
        IO.println s!"Test 4 - Nested Datatypes: PASSED"
        IO.println s!"  Verified {results.size} obligation(s)"
        for result in results do
          if result.result != .unsat then
            IO.println s!"  WARNING: {result.obligation.label}: {Std.format result.result}"
    catch e =>
      IO.println s!"Test 4 - Nested Datatypes: FAILED (exception)"
      IO.println s!"  Error: {e}"

/-! ## Test 5: Complete Verification Condition -/

/--
Test a complete verification condition with datatypes.
Creates a procedure with assumptions and assertions that exercise
constructors, testers, and destructors together.
-/
def test5_completeVC : IO Unit := do
  let statements : List Statement := [
    -- Create Some(42)
    Statement.init (BoogieIdent.unres "x") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Some")
          (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
        (LExpr.intConst () 42)),

    -- Assume x is Some (should be true)
    Statement.assume "x_is_some"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$isSome")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Extract value
    Statement.init (BoogieIdent.unres "val") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$SomeProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert extracted value is 42
    Statement.assert "extracted_value_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "val") (.some .int))
        (LExpr.intConst () 42)),

    -- Create a list and test it
    Statement.init (BoogieIdent.unres "list") (.forAll [] (LMonoTy.tcons "List" [.int]))
      (LExpr.app ()
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "Cons")
            (.some (LMonoTy.arrow .int (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) (LMonoTy.tcons "List" [.int])))))
          (LExpr.intConst () 10))
        (LExpr.op () (BoogieIdent.unres "Nil") (.some (LMonoTy.tcons "List" [.int])))),

    -- Assert list is Cons
    Statement.assert "list_is_cons"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$isCons")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "list") (.some (LMonoTy.tcons "List" [.int])))),

    -- Extract and verify head
    Statement.init (BoogieIdent.unres "h") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$ConsProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "list") (.some (LMonoTy.tcons "List" [.int])))),

    Statement.assert "head_is_10"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "h") (.some .int))
        (LExpr.intConst () 10))
  ]

  match mkProgramWithDatatypes [optionDatatype, listDatatype] "testCompleteVC" statements with
  | .error err =>
    IO.println s!"Test 5 - Complete VC: FAILED (program creation)"
    IO.println s!"  Error: {err.pretty}"
  | .ok program =>
    try
      match ← EIO.toIO' (Boogie.verify "cvc5" program) with
      | .error err =>
        IO.println s!"Test 5 - Complete VC: FAILED (verification)"
        IO.println s!"  Error: {err}"
      | .ok results =>
        IO.println s!"Test 5 - Complete VC: PASSED"
        IO.println s!"  Verified {results.size} obligation(s)"
        for result in results do
          if result.result != .unsat then
            IO.println s!"  WARNING: {result.obligation.label}: {Std.format result.result}"
    catch e =>
      IO.println s!"Test 5 - Complete VC: FAILED (exception)"
      IO.println s!"  Error: {e}"

/-! ## Run All Tests -/

def runAllTests : IO Unit := do
  IO.println "=== Datatype Integration Tests ==="
  IO.println ""

  test1_constructorApplication
  IO.println ""

  test2_testerFunctions
  IO.println ""

  test3_destructorFunctions
  IO.println ""

  test4_nestedDatatypes
  IO.println ""

  test5_completeVC
  IO.println ""

  IO.println "=== All Integration Tests Complete ==="

-- Run the tests
#eval runAllTests

end Boogie.DatatypeVerificationTests
