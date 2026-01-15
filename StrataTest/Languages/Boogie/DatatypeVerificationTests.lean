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

/-- Simple Option datatype: Option a = None | Some(OptionVal: a)
    Testers: isNone, isSome
    Destructors: OptionVal -/
def optionDatatype : LDatatype Visibility :=
  { name := "Option"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"None", .unres⟩, args := [], testerName := "isNone" },
      { name := ⟨"Some", .unres⟩, args := [(⟨"OptionVal", .unres⟩, .ftvar "a")], testerName := "isSome" }
    ]
    constrs_ne := by decide }

/-- Recursive List datatype: List a = Nil | Cons(hd: a, tl: List a)
    Testers: isNil, isCons
    Destructors: hd, tl -/
def listDatatype : LDatatype Visibility :=
  { name := "List"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"Nil", .unres⟩, args := [], testerName := "isNil" },
      { name := ⟨"Cons", .unres⟩, args := [
          (⟨"hd", .unres⟩, .ftvar "a"),
          (⟨"tl", .unres⟩, .tcons "List" [.ftvar "a"])
        ], testerName := "isCons" }
    ]
    constrs_ne := by decide }

/-- Hidden datatype that is never directly used in the program -/
def hiddenDatatype : LDatatype Visibility :=
  { name := "Hidden"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"HiddenValue", .unres⟩, args := [
          (⟨"hiddenField", .unres⟩, .ftvar "a")
        ], testerName := "isHiddenValue" }
    ]
    constrs_ne := by decide }

/-- Container datatype that references Hidden but we never use Hidden directly -/
def containerDatatype : LDatatype Visibility :=
  { name := "Container"
    typeArgs := ["a"]
    constrs := [
      { name := ⟨"Empty", .unres⟩, args := [], testerName := "isEmpty" },
      { name := ⟨"WithHidden", .unres⟩, args := [
          (⟨"hiddenPart", .unres⟩, .tcons "Hidden" [.ftvar "a"]),
          (⟨"visiblePart", .unres⟩, .ftvar "a")
        ], testerName := "isWithHidden" }
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
    match ← EIO.toIO' (Boogie.verify "cvc5" program Options.quiet) with
    | .error err =>
      return s!"{testName}: FAILED\n  Error: {err}"
    | .ok results =>
      let mut output := s!"{testName}: PASSED\n"
      output := output ++ s!"  Verified {results.size} obligation(s)\n"
      for result in results do
        if result.result != .pass then
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
  assert (isNone x);
  y := Some 42;
  assert (isSome y);
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
        (LExpr.op () (BoogieIdent.unres "isNone")
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
        (LExpr.op () (BoogieIdent.unres "isSome")
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
  val := value opt;
  assert (val == 42);

  list := [1]
  head := hd list;
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
    Statement.init (BoogieIdent.unres "value") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "OptionVal")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "opt") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert that val == 42
    Statement.assert "val_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "value") (.some .int))
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
        (LExpr.op () (BoogieIdent.unres "hd")
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
  assert (isCons listOfOpt);
  headOpt := hd listOfOpt;
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
        (LExpr.op () (BoogieIdent.unres "isCons")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "listOfOpt")
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))),

    -- Extract the head of the list (which is an Option)
    Statement.init (BoogieIdent.unres "headOpt") (.forAll [] (LMonoTy.tcons "Option" [.int]))
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "hd")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]]) (LMonoTy.tcons "Option" [.int]))))
        (LExpr.fvar () (BoogieIdent.unres "listOfOpt")
          (.some (LMonoTy.tcons "List" [LMonoTy.tcons "Option" [.int]])))),

    -- Extract the value from the Option
    Statement.init (BoogieIdent.unres "value") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "OptionVal")
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
  assume (isSome x);
  assert (not (isNone x));
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
        (LExpr.op () (BoogieIdent.unres "isSome")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "x") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert x is not None (should follow from assumption)
    Statement.assert "x_not_none"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Bool.Not")
          (.some (LMonoTy.arrow .bool .bool)))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "isNone")
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
  value := val opt;
  assert (value == 42);
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
    Statement.init (BoogieIdent.unres "value") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "OptionVal")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Option" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "opt") (.some (LMonoTy.tcons "Option" [.int])))),

    -- Assert val == 42
    Statement.assert "val_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "value") (.some .int))
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
  assume (isCons xs);
  assert (not (isNil xs));
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
        (LExpr.op () (BoogieIdent.unres "isCons")
          (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "xs") (.some (LMonoTy.tcons "List" [.int])))),

    -- Assert xs is not Nil
    Statement.assert "xs_not_nil"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Bool.Not")
          (.some (LMonoTy.arrow .bool .bool)))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "isNil")
            (.some (LMonoTy.arrow (LMonoTy.tcons "List" [.int]) .bool)))
          (LExpr.fvar () (BoogieIdent.unres "xs") (.some (LMonoTy.tcons "List" [.int])))))
  ]

  match mkProgramWithDatatypes [listDatatype] "testListHavoc" statements with
  | .error err =>
    return s!"Test 7 - List with Havoc: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 7 - List with Havoc" program

/-! ## Test 8: Hidden Type Recursive Addition -/

/--
Test that SMT.Context.addType correctly handles the recursive case where
a datatype constructor has another datatype as an argument, but this
argument datatype is NEVER directly referenced in the program.

datatype Hidden a = HiddenValue a
datatype Container a = Empty | WithHidden (Hidden a) a

procedure testHiddenTypeRecursion () {
  // We ONLY use Container, never Hidden directly
  container := Empty;
  havoc container;
  assume (not (isEmpty container));
  visiblePart := visiblePart container;
  assume (visiblePart == 42);
  assert (isWithHidden container);
}
-/
def test8_hiddenTypeRecursion : IO String := do
  let statements : List Statement := [
    -- Initialize with Empty Container - note we NEVER use Hidden directly
    Statement.init (BoogieIdent.unres "container")
      (.forAll [] (LMonoTy.tcons "Container" [.int]))
      (LExpr.op () (BoogieIdent.unres "Empty") (.some (LMonoTy.tcons "Container" [.int]))),

    -- Havoc the container to make it non-deterministic
    Statement.havoc (BoogieIdent.unres "container"),

    -- Assume container is not Empty (so it must be WithHidden)
    Statement.assume "container_not_empty"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "Bool.Not")
          (.some (LMonoTy.arrow .bool .bool)))
        (LExpr.app ()
          (LExpr.op () (BoogieIdent.unres "isEmpty")
            (.some (LMonoTy.arrow (LMonoTy.tcons "Container" [.int]) .bool)))
          (LExpr.fvar () (BoogieIdent.unres "container") (.some (LMonoTy.tcons "Container" [.int]))))),

    -- Extract the visible part
    Statement.init (BoogieIdent.unres "visiblePart") (.forAll [] LMonoTy.int)
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "visiblePart")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Container" [.int]) .int)))
        (LExpr.fvar () (BoogieIdent.unres "container") (.some (LMonoTy.tcons "Container" [.int])))),

    -- Assume the visible part has a specific value
    Statement.assume "visible_part_is_42"
      (LExpr.eq ()
        (LExpr.fvar () (BoogieIdent.unres "visiblePart") (.some .int))
        (LExpr.intConst () 42)),

    -- Assert that container is WithHidden
    Statement.assert "container_is_with_hidden"
      (LExpr.app ()
        (LExpr.op () (BoogieIdent.unres "isWithHidden")
          (.some (LMonoTy.arrow (LMonoTy.tcons "Container" [.int]) .bool)))
        (LExpr.fvar () (BoogieIdent.unres "container") (.some (LMonoTy.tcons "Container" [.int]))))
  ]

  match mkProgramWithDatatypes [hiddenDatatype, containerDatatype] "testHiddenTypeRecursion" statements with
  | .error err =>
    return s!"Test 8 - Hidden Type Recursion: FAILED (program creation)\n  Error: {err.pretty}"
  | .ok program =>
    runVerificationTest "Test 8 - Hidden Type Recursion" program



/--
info: "Test 1 - Constructor Application: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test1_constructorApplication

/--
info: "Test 2 - Tester Functions: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test2_testerFunctions

/--
info: "Test 3 - Destructor Functions: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test3_destructorFunctions

/--
info: "Test 4 - Nested Datatypes: PASSED\n  Verified 2 obligation(s)\n"
-/
#guard_msgs in
#eval test4_nestedDatatypes

/--
info: "Test 5 - Tester with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test5_testerWithHavoc

/--
info: "Test 6 - Destructor with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test6_destructorWithHavoc

/--
info: "Test 7 - List with Havoc: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test7_listWithHavoc

/--
info: "Test 8 - Hidden Type Recursion: PASSED\n  Verified 1 obligation(s)\n"
-/
#guard_msgs in
#eval test8_hiddenTypeRecursion


end Boogie.DatatypeVerificationTests
