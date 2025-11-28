/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.TypeFactory
import Strata.DL.SMT.Term
import Strata.DL.SMT.Encoder
import Strata.Languages.Boogie.Env
import Strata.Languages.Boogie.Factory
import Strata.Languages.Boogie.Identifiers
import Strata.Languages.Boogie.Options
import Strata.Languages.Boogie.SMTEncoder
import Strata.Languages.Boogie.Verifier

/-!
This file contains unit tests for SMT datatype encoding.
Tests verify that datatypes are correctly encoded to SMT-LIB format.

Tests cover:
- Simple datatypes (Option)
- Recursive datatypes (List)
- Multiple constructors
- Zero-argument constructors
- Multi-field constructors
- Parametric datatype instantiation
-/

namespace Boogie

section DatatypeTests

open Lambda
open Std

/-! ## Test Datatypes -/

/-- Simple Option datatype: Option α = None | Some α -/
def optionDatatype : LDatatype Visibility :=
  { name := "TestOption"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"None", .unres⟩, args := [] },
      { name := ⟨"Some", .unres⟩, args := [(⟨"value", .unres⟩, .ftvar "α")] }
    ]
    constrs_ne := by decide }

/-- Recursive List datatype: List α = Nil | Cons α (List α) -/
def listDatatype : LDatatype Visibility :=
  { name := "TestList"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Nil", .unres⟩, args := [] },
      { name := ⟨"Cons", .unres⟩, args := [
          (⟨"head", .unres⟩, .ftvar "α"),
          (⟨"tail", .unres⟩, .tcons "TestList" [.ftvar "α"])
        ] }
    ]
    constrs_ne := by decide }

/-- Binary tree datatype: Tree α = Leaf | Node α (Tree α) (Tree α) -/
def treeDatatype : LDatatype Visibility :=
  { name := "TestTree"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Leaf", .unres⟩, args := [] },
      { name := ⟨"Node", .unres⟩, args := [
          (⟨"value", .unres⟩, .ftvar "α"),
          (⟨"left", .unres⟩, .tcons "TestTree" [.ftvar "α"]),
          (⟨"right", .unres⟩, .tcons "TestTree" [.ftvar "α"])
        ] }
    ]
    constrs_ne := by decide }

/-! ## Helper Functions -/

/--
Create an environment with a TypeFactory containing the given datatypes.
-/
def mkEnvWithDatatypes (datatypes : List (LDatatype Visibility)) : Except Format Env := do
  let mut env := Env.init
  for d in datatypes do
    env := { env with datatypes := env.datatypes.push d }
    let factory ← d.genFactory (T := BoogieLParams)
    env ← env.addFactory factory
  return env

/--
Convert an expression to full SMT string including datatype declarations.
This emits the complete SMT-LIB output with declare-datatype commands.
-/
def toSMTStringWithDatatypes (e : LExpr BoogieLParams.mono) (datatypes : List (LDatatype Visibility)) : IO String := do
  match mkEnvWithDatatypes datatypes with
  | .error msg => return s!"Error creating environment: {msg}"
  | .ok env =>
    match toSMTTerm env [] e SMT.Context.default with
    | .error err => return err.pretty
    | .ok (smt, ctx) =>
      -- Emit the full SMT output including datatype declarations
      let b ← IO.mkRef { : IO.FS.Stream.Buffer }
      let solver ← Strata.SMT.Solver.bufferWriter b
      match (← ((do
        -- First emit datatypes
        ctx.emitDatatypes
        -- Then encode the term
        let _ ← (Strata.SMT.Encoder.encodeTerm false smt).run Strata.SMT.EncoderState.init
        pure ()
      ).run solver).toBaseIO) with
      | .error e => return s!"Error: {e}"
      | .ok _ =>
        let contents ← b.get
        if h: String.validateUTF8 contents.data then
          return String.fromUTF8 contents.data h
        else
          return "Invalid UTF-8 in output"

/-! ## Test Cases with Guard Messages -/

-- Test 1: Simple datatype (Option) - zero-argument constructor
-- This tests that a type using Option gets the datatype registered and declared
/--
info: "(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n; x\n(declare-const f0 (TestOption Int))\n(define-fun t0 () (TestOption Int) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "x") (.some (.tcons "TestOption" [.int])))
  [optionDatatype]

-- Test 2: Recursive datatype (List) - using List type
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; xs\n(declare-const f0 (TestList Int))\n(define-fun t0 () (TestList Int) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "xs") (.some (.tcons "TestList" [.int])))
  [listDatatype]

-- Test 3: Multiple constructors - Tree with Leaf and Node
/--
info: "(declare-datatype TestTree (par (α) (\n  (Leaf)\n  (Node (TestTree$NodeProj0 α) (TestTree$NodeProj1 (TestTree α)) (TestTree$NodeProj2 (TestTree α))))))\n; tree\n(declare-const f0 (TestTree Bool))\n(define-fun t0 () (TestTree Bool) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "tree") (.some (.tcons "TestTree" [.bool])))
  [treeDatatype]

-- Test 4: Parametric datatype instantiation - List Int
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; intList\n(declare-const f0 (TestList Int))\n(define-fun t0 () (TestList Int) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "intList") (.some (.tcons "TestList" [.int])))
  [listDatatype]

-- Test 5: Parametric datatype instantiation - List Bool (should reuse same datatype)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; boolList\n(declare-const f0 (TestList Bool))\n(define-fun t0 () (TestList Bool) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "boolList") (.some (.tcons "TestList" [.bool])))
  [listDatatype]

-- Test 6: Multi-field constructor - Tree with 3 fields
/--
info: "(declare-datatype TestTree (par (α) (\n  (Leaf)\n  (Node (TestTree$NodeProj0 α) (TestTree$NodeProj1 (TestTree α)) (TestTree$NodeProj2 (TestTree α))))))\n; intTree\n(declare-const f0 (TestTree Int))\n(define-fun t0 () (TestTree Int) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "intTree") (.some (.tcons "TestTree" [.int])))
  [treeDatatype]

-- Test 7: Nested parametric types - List of Option (should declare both datatypes)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n; listOfOption\n(declare-const f0 (TestList (TestOption Int)))\n(define-fun t0 () (TestList (TestOption Int)) f0)\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.fvar () (BoogieIdent.unres "listOfOption") (.some (.tcons "TestList" [.tcons "TestOption" [.int]])))
  [listDatatype, optionDatatype]

/-! ## Constructor Application Tests (will work after task 4 is complete) -/

-- Test 8: None constructor (zero-argument)
-- Expected output should show: (None) or similar SMT constructor application
/--
info: "(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n(define-fun t0 () (TestOption Int) (as None (TestOption Int)))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.op () (BoogieIdent.unres "None") (.some (.tcons "TestOption" [.int])))
  [optionDatatype]

-- Test 9: Some constructor (single-argument)
-- Expected output should show: (Some 42)
/--
info: "(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n(define-fun t0 () (TestOption Int) (Some 42))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "Some") (.some (.arrow .int (.tcons "TestOption" [.int])))) (.intConst () 42))
  [optionDatatype]

-- Test 10: Cons constructor (multi-argument)
-- Expected output should show: (Cons 1 Nil)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n(define-fun t0 () (TestList Int) (as Nil (TestList Int)))\n(define-fun t1 () (TestList Int) (Cons 1 t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app ()
    (.app () (.op () (BoogieIdent.unres "Cons") (.some (.arrow .int (.arrow (.tcons "TestList" [.int]) (.tcons "TestList" [.int])))))
      (.intConst () 1))
    (.op () (BoogieIdent.unres "Nil") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Tester Function Tests (will work after task 5 is complete) -/

-- Test 11: isNone tester
-- Expected output should show: (is-None x)
/--
info: "(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n; x\n(declare-const f0 (TestOption Int))\n(define-fun t0 () (TestOption Int) f0)\n(define-fun t1 () Bool (is-None t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "TestOption$isNone") (.some (.arrow (.tcons "TestOption" [.int]) .bool)))
    (.fvar () (BoogieIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 12: isCons tester
-- Expected output should show: (is-Cons xs)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; xs\n(declare-const f0 (TestList Int))\n(define-fun t0 () (TestList Int) f0)\n(define-fun t1 () Bool (is-Cons t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "TestList$isCons") (.some (.arrow (.tcons "TestList" [.int]) .bool)))
    (.fvar () (BoogieIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Destructor Function Tests (will work after task 6 is complete) -/

-- Test 13: Some value destructor
-- Expected output should show: (TestOption$SomeProj0 x)
/--
info: "(declare-datatype TestOption (par (α) (\n  (None)\n  (Some (TestOption$SomeProj0 α)))))\n; x\n(declare-const f0 (TestOption Int))\n(define-fun t0 () (TestOption Int) f0)\n(define-fun t1 () Int (TestOption$SomeProj0 t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "TestOption$SomeProj0") (.some (.arrow (.tcons "TestOption" [.int]) .int)))
    (.fvar () (BoogieIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 14: Cons head destructor
-- Expected output should show: (TestList$ConsProj0 xs)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; xs\n(declare-const f0 (TestList Int))\n(define-fun t0 () (TestList Int) f0)\n(define-fun t1 () Int (TestList$ConsProj0 t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "TestList$ConsProj0") (.some (.arrow (.tcons "TestList" [.int]) .int)))
    (.fvar () (BoogieIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

-- Test 15: Cons tail destructor
-- Expected output should show: (TestList$ConsProj1 xs)
/--
info: "(declare-datatype TestList (par (α) (\n  (Nil)\n  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))\n; xs\n(declare-const f0 (TestList Int))\n(define-fun t0 () (TestList Int) f0)\n(define-fun t1 () (TestList Int) (TestList$ConsProj1 t0))\n"
-/
#guard_msgs in
#eval toSMTStringWithDatatypes
  (.app () (.op () (BoogieIdent.unres "TestList$ConsProj1") (.some (.arrow (.tcons "TestList" [.int]) (.tcons "TestList" [.int]))))
    (.fvar () (BoogieIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

end DatatypeTests

end Boogie
