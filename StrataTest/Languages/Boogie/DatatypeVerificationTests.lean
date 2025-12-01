/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Boogie.Verifier
import Strata.DL.Lambda.TypeFactory

/-!
# Datatype Verification Integration Tests

Verify Boogie programs with datatypes, encoding with declare-datatype
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

  let decls := datatypes.map (fun d => Decl.type (.data d) .empty)
  return { decls := decls ++ [Decl.proc proc .empty] }

/-! ## Helper for Running Tests -/

/--
Run verification and return a summary string.
-/
def runVerificationTest (testName : String) (program : Program) : IO String := do
  try
    match ← EIO.toIO' (Boogie.verify "cvc5" program) with
    | .error err =>
      return s!"{testName}: FAILED\n  Error: {err}"
    | .ok results =>
      let mut output := s!"{testName}: PASSED\n"
      output := output ++ s!"  Verified {results.size} obligation(s)\n"
      for result in results do
        if result.result != .unsat then
          output := output ++ s!"  WARNING: {result.obligation.label}: {Std.format result.result}\n"
      return output
  catch e =>
    return s!"{testName}: FAILED (exception)\n  Error: {e}"

/-! ## Test 1: Constructor Application -/

/--
Test that constructor applications are properly encoded.

datatype Option a = None | Some a

procedure testConstructors () {
  x := None;
  y := Some 42;
  assert true;
}
-/
def test1_constructorApplication : IO String := do
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
    return s!"Test 1 - Constructor Application: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 1 - Constructor Application" program

/-! ## Test 2: Tester Functions -/

/--
Test that tester functions (is-None, is-Some) are properly encoded.

datatype Option a = None | Some a

procedure testTesters () {
  x := None;
  assert (Option$isNone x);
  y := Some 42;
  assert (Option$isSome y);
}

-/
def test2_testerFunctions : IO String := do
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
    return s!"Test 2 - Tester Functions: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 2 - Tester Functions" program

/-! ## Test 3: Destructor Functions -/

/--
Test that destructor functions are properly encoded.

datatype Option a = None | Some a
datatype List a = Nil | Cons a (List a)

procedure testDestructors () {
  opt := Some 42;
  val := Option$SomeProj0 opt;
  assert (val == 42);

  list := [1]
  head := List$ConsProj0 list;
  assert(head == 1);
}

-/
def test3_destructorFunctions : IO String := do
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
    return s!"Test 3 - Destructor Functions: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 3 - Destructor Functions" program

/-! ## Test 4: Nested Datatypes -/

/--
Test nested datatypes (List of Option).

datatype Option a = None | Some a
datatype List a = Nil | Cons a (List a)

procedure testNested () {
  listOfOpt := [Some 42];
  assert (List$isCons listOfOpt);
  headOpt := List$ConsProj0 listOfOpt;
  value := Option$ConsProj0 headOpt;
  assert (value == 42);
}

-/
def test4_nestedDatatypes : IO String := do
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
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))),

    -- Extract the head of the list (which is an Option)
    Statement.init (BoogieIdent.unres "headOpt") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$ConsProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]) (LMonoTy.tcons "Option" [.int]))))
        (LExpr.fvar () (BoogieIdent.unres "listOfOpt")
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))),

    -- Extract the value from the Option
    Statement.init (BoogieIdent.unres "value") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$SomeProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "headOpt")
          (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert that the extracted value is 42
    Statement.assert "value_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "value") (.some .int))
        (LExpr.intConst () 42))
  ]

  match mkProgramWithDatatypes [listDatatype, optionDatatype] "testNested" statements with
  | .error err =>
    return s!"Test 4 - Nested Datatypes: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 4 - Nested Datatypes" program

/-! ## Test 5: Tester with Havoc (requires SMT) -/

/--
Test tester functions with havoc'd values that require SMT solving and cannot
be solved only with partial evaluation.

datatype Option a = None | Some a

procedure testTesterHavoc () {
  x := None;
  x := havoc();
  assume (Option$isSome x);
  assert (not (Option$isNone x));
}

-/
def test5_testerWithHavoc : IO String := do
  let statements : List Statement := [
    -- Havoc an Option value (non-deterministic)
    Statement.init (BoogieIdent.unres "x") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.op () (BoogieIdent.unres "None") (.some (LMonoTy.tcons "Option" [.int]))),
    Statement.havoc (BoogieIdent.unres "x"),

    -- Assume x is Some
    Statement.assume "x_is_some"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$isSome")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert x is not None (should follow from assumption)
    Statement.assert "x_not_none"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Bool.Not")
          (.some (LMonoTy.arrow .bool .bool)))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "Option$isNone")
            (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
          (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))))
  ]

  match mkProgramWithDatatypes [optionDatatype] "testTesterHavoc" statements with
  | .error err =>
    return s!"Test 5 - Tester with Havoc: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 5 - Tester with Havoc" program

/-! ## Test 6: Destructor with Havoc (requires SMT) -/

/--
Test destructor functions with havoc'd values.

datatype Option a = None | Some a

procedure testDestructorHavoc () {
  opt := Some 0;
  opt := havoc();
  assume (opt == Some 42);
  val := Option$SomeProj0 opt;
  assert (val == 42);
}

-/
def test6_destructorWithHavoc : IO String := do
  let statements : List Statement := [
    -- Havoc an Option value
    Statement.init (BoogieIdent.unres "opt") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Some")
          (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
        (LExpr.intConst () 0)),
    Statement.havoc (BoogieIdent.unres "opt"),

    -- Assume opt is Some(42)
    Statement.assume "opt_is_some_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "opt") (.some (LMonoTy.tcons "Option" [.int])))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "Some")
            (.some (LMonoTy.arrow .int (LMonoTy.tcons "Option" [.int]))))
          (LExpr.intConst () 42))),

    -- Extract value
    Statement.init (BoogieIdent.unres "val") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Option$SomeProj0")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "opt") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert val == 42
    Statement.assert "val_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "val") (.some .int))
        (LExpr.intConst () 42))
  ]

  match mkProgramWithDatatypes [optionDatatype] "testDestructorHavoc" statements with
  | .error err =>
    return s!"Test 6 - Destructor with Havoc: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 6 - Destructor with Havoc" program

/-! ## Test 7: List Constructor with Havoc (requires SMT) -/

/--
Test list operations with havoc'd values.

datatype List a = Nil | Cons a (List a)

procedure testListHavoc () {
  xs := Nil;
  xs := havoc();
  assume (List$isCons xs);
  assert (not (List$isNil xs));
}

-/
def test7_listWithHavoc : IO String := do
  let statements : List Statement := [
    -- Havoc a list
    Statement.init (BoogieIdent.unres "xs") (.forAll [] (LMonoTy.tcons "List" [.int]))
      (LExpr.op () (BoogieIdent.unres "Nil") (.some (LMonoTy.tcons "List" [.int]))),
    Statement.havoc (BoogieIdent.unres "xs"),

    -- Assume xs is Cons
    Statement.assume "xs_is_cons"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "List$isCons")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "xs") (.some (LMonoTy.tcons "List" [.int])))),

    -- Assert xs is not Nil
    Statement.assert "xs_not_nil"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Bool.Not")
          (.some (LMonoTy.arrow .bool .bool)))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "List$isNil")
            (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .bool)))
          (LExpr.fvar () (BoogieIdent.unres "xs") (.some (LMonoTy.tcons "List" [.int])))))
  ]

  match mkProgramWithDatatypes [listDatatype] "testListHavoc" statements with
  | .error err =>
    return s!"Test 7 - List with Havoc: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 7 - List with Havoc" program

/-! ## Run All Tests with #guard_msgs -/

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: trivial
Assumptions:


Proof Obligation:
#true

---
info: "Test 1 - Constructor Application: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test1_constructorApplication

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: x_is_none
Assumptions:


Proof Obligation:
#true

Label: y_is_some
Assumptions:


Proof Obligation:
#true

---
info: "Test 2 - Tester Functions: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test2_testerFunctions

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: val_is_42
Assumptions:


Proof Obligation:
#true

Label: head_is_1
Assumptions:


Proof Obligation:
#true

---
info: "Test 3 - Destructor Functions: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test3_destructorFunctions

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: list_is_cons
Assumptions:


Proof Obligation:
#true

Label: value_is_42
Assumptions:


Proof Obligation:
#true

---
info: "Test 4 - Nested Datatypes: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test4_nestedDatatypes

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: x_not_none
Assumptions:
(x_is_some, (~Option$isSome $__x0))

Proof Obligation:
(~Bool.Not (~Option$isNone $__x0))

Wrote problem to vcs/x_not_none.smt2.
---
info: "Test 5 - Tester with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test5_testerWithHavoc

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: val_is_42
Assumptions:
(opt_is_some_42, ($__opt0 == (~Some #42)))

Proof Obligation:
((~Option$SomeProj0 $__opt0) == #42)

Wrote problem to vcs/val_is_42.smt2.
---
info: "Test 6 - Destructor with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test6_destructorWithHavoc

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: xs_not_nil
Assumptions:
(xs_is_cons, (~List$isCons $__xs0))

Proof Obligation:
(~Bool.Not (~List$isNil $__xs0))

Wrote problem to vcs/xs_not_nil.smt2.
---
info: "Test 7 - List with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test7_listWithHavoc

end Boogie.DatatypeVerificationTests
