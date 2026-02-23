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
import Strata.Languages.Core.Env
import Strata.Languages.Core.Factory
import Strata.Languages.Core.Identifiers
import Strata.Languages.Core.Options
import Strata.Languages.Core.SMTEncoder
import Strata.Languages.Core.Verifier

/-!
This file contains unit tests for SMT datatype encoding.
-/

namespace Core

section DatatypeTests

open Lambda
open Std

/-! ## Test Datatypes -/

/-- Option α = None | Some α -/
def optionDatatype : LDatatype Visibility :=
  { name := "TestOption"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"None", .unres⟩, args := [], testerName := "TestOption..isNone" },
      { name := ⟨"Some", .unres⟩, args := [(⟨"val", .unres⟩, .ftvar "α")], testerName := "TestOption..isSome"  }
    ]
    constrs_ne := by decide }

/-- List α = Nil | Cons α (List α) -/
def listDatatype : LDatatype Visibility :=
  { name := "TestList"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Nil", .unres⟩, args := [], testerName := "TestList..isNil" },
      { name := ⟨"Cons", .unres⟩, args := [
          (⟨"head", .unres⟩, .ftvar "α"),
          (⟨"tail", .unres⟩, .tcons "TestList" [.ftvar "α"])
        ], testerName := "TestList..isCons" }
    ]
    constrs_ne := by decide }

/-- Tree α = Leaf | Node α (Tree α) (Tree α) -/
def treeDatatype : LDatatype Visibility :=
  { name := "TestTree"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Leaf", .unres⟩, args := [], testerName := "TestTree..isLeaf" },
      { name := ⟨"Node", .unres⟩, args := [
          (⟨"value", .unres⟩, .ftvar "α"),
          (⟨"left", .unres⟩, .tcons "TestTree" [.ftvar "α"]),
          (⟨"right", .unres⟩, .tcons "TestTree" [.ftvar "α"])
        ], testerName := "TestTree..isNode" }
    ]
    constrs_ne := by decide }
/--
Convert an expression to full SMT string including datatype declarations.
`blocks` is a list of mutual blocks (each block is a list of mutually recursive datatypes).
-/
def toSMTStringWithDatatypeBlocks (e : LExpr CoreLParams.mono) (blocks : List (List (LDatatype Visibility))) : IO String := do
  match Env.init.addDatatypes blocks with
  | .error msg => return s!"Error creating environment: {msg}"
  | .ok env =>
    -- Set the TypeFactory for correct datatype emission ordering
    let ctx := SMT.Context.default.withTypeFactory env.datatypes
    match toSMTTerm env [] e ctx with
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
        if h: contents.data.IsValidUTF8 then
          return String.fromUTF8 contents.data h
        else
          return "Invalid UTF-8 in output"

/--
Convert an expression to full SMT string including datatype declarations.
Each datatype is treated as its own (non-mutual) block.
-/
def toSMTStringWithDatatypes (e : LExpr CoreLParams.mono) (datatypes : List (LDatatype Visibility)) : IO String :=
  toSMTStringWithDatatypeBlocks e (datatypes.map (fun d => [d]))

/-! ## Test Cases with Guard Messages -/

-- Test 1: Simple datatype (Option) - zero-argument constructor
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
; x
(declare-const f0 (TestOption Int))
(define-fun t0 () (TestOption Int) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "x") (.some (.tcons "TestOption" [.int])))
  [optionDatatype]

-- Test 2: Recursive datatype (List) - using List type
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int])))
  [listDatatype]

-- Test 3: Multiple constructors - Tree with Leaf and Node
/--
info: (declare-datatype TestTree (par (α) (
  (Leaf)
  (Node (TestTree..value α) (TestTree..left (TestTree α)) (TestTree..right (TestTree α))))))
; tree
(declare-const f0 (TestTree Bool))
(define-fun t0 () (TestTree Bool) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "tree") (.some (.tcons "TestTree" [.bool])))
  [treeDatatype]

-- Test 4: Parametric datatype instantiation - List Int
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; intList
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "intList") (.some (.tcons "TestList" [.int])))
  [listDatatype]

-- Test 5: Parametric datatype instantiation - List Bool (should reuse same datatype)
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; boolList
(declare-const f0 (TestList Bool))
(define-fun t0 () (TestList Bool) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "boolList") (.some (.tcons "TestList" [.bool])))
  [listDatatype]

-- Test 6: Multi-field constructor - Tree with 3 fields
/--
info: (declare-datatype TestTree (par (α) (
  (Leaf)
  (Node (TestTree..value α) (TestTree..left (TestTree α)) (TestTree..right (TestTree α))))))
; intTree
(declare-const f0 (TestTree Int))
(define-fun t0 () (TestTree Int) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "intTree") (.some (.tcons "TestTree" [.int])))
  [treeDatatype]

-- Test 7: Nested parametric types - List of Option (should declare both datatypes)
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
(declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; listOfOption
(declare-const f0 (TestList (TestOption Int)))
(define-fun t0 () (TestList (TestOption Int)) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "listOfOption") (.some (.tcons "TestList" [.tcons "TestOption" [.int]])))
  [optionDatatype, listDatatype]

/-! ## Constructor Application Tests -/

-- Test 8: None constructor (zero-argument)
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
(define-fun t0 () (TestOption Int) (as None (TestOption Int)))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.op () (CoreIdent.unres "None") (.some (.tcons "TestOption" [.int])))
  [optionDatatype]

-- Test 9: Some constructor (single-argument)
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
(define-fun t0 () (TestOption Int) ((as Some (TestOption Int)) 42))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "Some") (.some (.arrow .int (.tcons "TestOption" [.int])))) (.intConst () 42))
  [optionDatatype]

-- Test 10: Cons constructor (multi-argument)
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
(define-fun t0 () (TestList Int) (as Nil (TestList Int)))
(define-fun t1 () (TestList Int) ((as Cons (TestList Int)) 1 t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app ()
    (.app () (.op () (CoreIdent.unres "Cons") (.some (.arrow .int (.arrow (.tcons "TestList" [.int]) (.tcons "TestList" [.int])))))
      (.intConst () 1))
    (.op () (CoreIdent.unres "Nil") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Tester Function Tests  -/

-- Test 11: isNone tester
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
; x
(declare-const f0 (TestOption Int))
(define-fun t0 () (TestOption Int) f0)
(define-fun t1 () Bool (is-None t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestOption..isNone") (.some (.arrow (.tcons "TestOption" [.int]) .bool)))
    (.fvar () (CoreIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 12: isCons tester
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () Bool (is-Cons t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList..isCons") (.some (.arrow (.tcons "TestList" [.int]) .bool)))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Destructor Function Tests -/

-- Test 13: Some value destructor
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
; x
(declare-const f0 (TestOption Int))
(define-fun t0 () (TestOption Int) f0)
(define-fun t1 () Int (TestOption..val t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestOption..val") (.some (.arrow (.tcons "TestOption" [.int]) .int)))
    (.fvar () (CoreIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 14: Cons head destructor
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () Int (TestList..head t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList..head") (.some (.arrow (.tcons "TestList" [.int]) .int)))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

-- Test 15: Cons tail destructor
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList..head α) (TestList..tail (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () (TestList Int) (TestList..tail t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList..tail") (.some (.arrow (.tcons "TestList" [.int]) (.tcons "TestList" [.int]))))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Dependency Order Tests -/

-- Test 16: Diamond dependency pattern
-- Dependencies: Diamond -> Left, Right
--              Left -> Root
--              Right -> Root

/-- Root = RootValue int -/
def rootDatatype : LDatatype Visibility :=
  { name := "Root"
    typeArgs := []
    constrs := [
      { name := ⟨"RootValue", .unres⟩, args := [(⟨"value", .unres⟩, .int)], testerName := "Root..isRootValue" }
    ]
    constrs_ne := by decide }

/-- Left = LeftValue Root -/
def leftDatatype : LDatatype Visibility :=
  { name := "Left"
    typeArgs := []
    constrs := [
      { name := ⟨"LeftValue", .unres⟩, args := [(⟨"root", .unres⟩, .tcons "Root" [])], testerName := "Left..isLeftValue" }
    ]
    constrs_ne := by decide }

/-- Right = RightValue Root -/
def rightDatatype : LDatatype Visibility :=
  { name := "Right"
    typeArgs := []
    constrs := [
      { name := ⟨"RightValue", .unres⟩, args := [(⟨"root", .unres⟩, .tcons "Root" [])], testerName := "Right..isRightValue" }
    ]
    constrs_ne := by decide }

/-- Diamond = DiamondValue Left Right -/
def diamondDatatype : LDatatype Visibility :=
  { name := "Diamond"
    typeArgs := []
    constrs := [
      { name := ⟨"DiamondValue", .unres⟩, args := [
          (⟨"left", .unres⟩, .tcons "Left" []),
          (⟨"right", .unres⟩, .tcons "Right" [])
        ], testerName := "Diamond..isDiamondValue" }
    ]
    constrs_ne := by decide }

/--
info: (declare-datatype Root (
  (RootValue (Root..value Int))))
(declare-datatype Right (
  (RightValue (Right..root Root))))
(declare-datatype Left (
  (LeftValue (Left..root Root))))
(declare-datatype Diamond (
  (DiamondValue (Diamond..left Left) (Diamond..right Right))))
; diamondVar
(declare-const f0 Diamond)
(define-fun t0 () Diamond f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "diamondVar") (.some (.tcons "Diamond" [])))
  [rootDatatype, rightDatatype, leftDatatype, diamondDatatype]

-- Test 17: Mutually recursive datatypes (RoseTree/Forest)
-- Should emit declare-datatypes with both types together

/-- RoseTree α = Node α (Forest α) -/
def roseTreeDatatype : LDatatype Visibility :=
  { name := "RoseTree"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Node", .unres⟩, args := [
          (⟨"node", .unres⟩, .ftvar "α"),
          (⟨"children", .unres⟩, .tcons "Forest" [.ftvar "α"])
        ], testerName := "RoseTree$isNode" }
    ]
    constrs_ne := by decide }

/-- Forest α = FNil | FCons (RoseTree α) (Forest α) -/
def forestDatatype : LDatatype Visibility :=
  { name := "Forest"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"FNil", .unres⟩, args := [], testerName := "Forest$isFNil" },
      { name := ⟨"FCons", .unres⟩, args := [
          (⟨"hd", .unres⟩, .tcons "RoseTree" [.ftvar "α"]),
          (⟨"tl", .unres⟩, .tcons "Forest" [.ftvar "α"])
        ], testerName := "Forest$isFCons" }
    ]
    constrs_ne := by decide }

/--
info: (declare-datatypes ((RoseTree 1) (Forest 1))
  ((par (α) ((Node (RoseTree..node α) (RoseTree..children (Forest α)))))
  (par (α) ((FNil) (FCons (Forest..hd (RoseTree α)) (Forest..tl (Forest α)))))))
; tree
(declare-const f0 (RoseTree Int))
(define-fun t0 () (RoseTree Int) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypeBlocks
  (.fvar () (CoreIdent.unres "tree") (.some (.tcons "RoseTree" [.int])))
  [[roseTreeDatatype, forestDatatype]]

-- Test 19: Mix of mutual and non-mutual datatypes
-- TestOption (non-mutual), then RoseTree/Forest (mutual)
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption..val α)))))
(declare-datatypes ((RoseTree 1) (Forest 1))
  ((par (α) ((Node (RoseTree..node α) (RoseTree..children (Forest α)))))
  (par (α) ((FNil) (FCons (Forest..hd (RoseTree α)) (Forest..tl (Forest α)))))))
; optionTree
(declare-const f0 (TestOption (RoseTree Int)))
(define-fun t0 () (TestOption (RoseTree Int)) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypeBlocks
  (.fvar () (CoreIdent.unres "optionTree") (.some (.tcons "TestOption" [.tcons "RoseTree" [.int]])))
  [[optionDatatype], [roseTreeDatatype, forestDatatype]]

end DatatypeTests

end Core
