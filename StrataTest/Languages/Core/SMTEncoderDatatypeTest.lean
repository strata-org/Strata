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
      { name := ⟨"None", .unres⟩, args := [], testerName := "TestOption$isNone" },
      { name := ⟨"Some", .unres⟩, args := [(⟨"TestOption$SomeProj0", .unres⟩, .ftvar "α")], testerName := "TestOption$isSome"  }
    ]
    constrs_ne := by decide }

/-- List α = Nil | Cons α (List α) -/
def listDatatype : LDatatype Visibility :=
  { name := "TestList"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Nil", .unres⟩, args := [], testerName := "TestList$isNil" },
      { name := ⟨"Cons", .unres⟩, args := [
          (⟨"TestList$ConsProj0", .unres⟩, .ftvar "α"),
          (⟨"TestList$ConsProj1", .unres⟩, .tcons "TestList" [.ftvar "α"])
        ], testerName := "TestList$isCons" }
    ]
    constrs_ne := by decide }

/-- Tree α = Leaf | Node α (Tree α) (Tree α) -/
def treeDatatype : LDatatype Visibility :=
  { name := "TestTree"
    typeArgs := ["α"]
    constrs := [
      { name := ⟨"Leaf", .unres⟩, args := [], testerName := "TestTree$isLeaf" },
      { name := ⟨"Node", .unres⟩, args := [
          (⟨"TestTree$NodeProj0", .unres⟩, .ftvar "α"),
          (⟨"TestTree$NodeProj1", .unres⟩, .tcons "TestTree" [.ftvar "α"]),
          (⟨"TestTree$NodeProj2", .unres⟩, .tcons "TestTree" [.ftvar "α"])
        ], testerName := "TestTree$isNode" }
    ]
    constrs_ne := by decide }
/--
Convert an expression to full SMT string including datatype declarations.
-/
def toSMTStringWithDatatypes (e : LExpr CoreLParams.mono) (datatypes : List (LDatatype Visibility)) : IO String := do
  match Env.init.addDatatypes datatypes with
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
        if h: contents.data.IsValidUTF8 then
          return String.fromUTF8 contents.data h
        else
          return "Invalid UTF-8 in output"

/-! ## Test Cases with Guard Messages -/

-- Test 1: Simple datatype (Option) - zero-argument constructor
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption$SomeProj0 α)))))
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
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
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
  (Node (TestTree$NodeProj0 α) (TestTree$NodeProj1 (TestTree α)) (TestTree$NodeProj2 (TestTree α))))))
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
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
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
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
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
  (Node (TestTree$NodeProj0 α) (TestTree$NodeProj1 (TestTree α)) (TestTree$NodeProj2 (TestTree α))))))
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
  (Some (TestOption$SomeProj0 α)))))
(declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
; listOfOption
(declare-const f0 (TestList (TestOption Int)))
(define-fun t0 () (TestList (TestOption Int)) f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "listOfOption") (.some (.tcons "TestList" [.tcons "TestOption" [.int]])))
  [listDatatype, optionDatatype]

/-! ## Constructor Application Tests -/

-- Test 8: None constructor (zero-argument)
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption$SomeProj0 α)))))
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
  (Some (TestOption$SomeProj0 α)))))
(define-fun t0 () (TestOption Int) (Some 42))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "Some") (.some (.arrow .int (.tcons "TestOption" [.int])))) (.intConst () 42))
  [optionDatatype]

-- Test 10: Cons constructor (multi-argument)
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
(define-fun t0 () (TestList Int) (as Nil (TestList Int)))
(define-fun t1 () (TestList Int) (Cons 1 t0))
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
  (Some (TestOption$SomeProj0 α)))))
; x
(declare-const f0 (TestOption Int))
(define-fun t0 () (TestOption Int) f0)
(define-fun t1 () Bool (is-None t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestOption$isNone") (.some (.arrow (.tcons "TestOption" [.int]) .bool)))
    (.fvar () (CoreIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 12: isCons tester
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () Bool (is-Cons t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList$isCons") (.some (.arrow (.tcons "TestList" [.int]) .bool)))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Destructor Function Tests -/

-- Test 13: Some value destructor
/--
info: (declare-datatype TestOption (par (α) (
  (None)
  (Some (TestOption$SomeProj0 α)))))
; x
(declare-const f0 (TestOption Int))
(define-fun t0 () (TestOption Int) f0)
(define-fun t1 () Int (TestOption$SomeProj0 t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestOption$SomeProj0") (.some (.arrow (.tcons "TestOption" [.int]) .int)))
    (.fvar () (CoreIdent.unres "x") (.some (.tcons "TestOption" [.int]))))
  [optionDatatype]

-- Test 14: Cons head destructor
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () Int (TestList$ConsProj0 t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList$ConsProj0") (.some (.arrow (.tcons "TestList" [.int]) .int)))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

-- Test 15: Cons tail destructor
/--
info: (declare-datatype TestList (par (α) (
  (Nil)
  (Cons (TestList$ConsProj0 α) (TestList$ConsProj1 (TestList α))))))
; xs
(declare-const f0 (TestList Int))
(define-fun t0 () (TestList Int) f0)
(define-fun t1 () (TestList Int) (TestList$ConsProj1 t0))
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.app () (.op () (CoreIdent.unres "TestList$ConsProj1") (.some (.arrow (.tcons "TestList" [.int]) (.tcons "TestList" [.int]))))
    (.fvar () (CoreIdent.unres "xs") (.some (.tcons "TestList" [.int]))))
  [listDatatype]

/-! ## Complex Dependency Topological Sorting Tests -/

-- Test 16: Very complex dependency graph requiring sophisticated topological sorting
-- Dependencies: Alpha -> Beta, Gamma
--              Beta -> Delta, Epsilon
--              Gamma -> Epsilon, Zeta
--              Delta -> Zeta
--              Epsilon -> Zeta
-- Actual topological order: Zeta, Epsilon, Gamma, Delta, Beta, Alpha

/-- Alpha = AlphaValue Beta Gamma -/
def alphaDatatype : LDatatype Visibility :=
  { name := "Alpha"
    typeArgs := []
    constrs := [
      { name := ⟨"AlphaValue", .unres⟩, args := [
          (⟨"Alpha$AlphaValueProj0", .unres⟩, .tcons "Beta" []),
          (⟨"Alpha$AlphaValueProj1", .unres⟩, .tcons "Gamma" [])
        ], testerName := "Alpha$isAlphaValue" }
    ]
    constrs_ne := by decide }

/-- Beta = BetaValue Delta Epsilon -/
def betaDatatype : LDatatype Visibility :=
  { name := "Beta"
    typeArgs := []
    constrs := [
      { name := ⟨"BetaValue", .unres⟩, args := [
          (⟨"Beta$BetaValueProj0", .unres⟩, .tcons "Delta" []),
          (⟨"Beta$BetaValueProj1", .unres⟩, .tcons "Epsilon" [])
        ], testerName := "Beta$isBetaValue" }
    ]
    constrs_ne := by decide }

/-- Gamma = GammaValue Epsilon Zeta -/
def gammaDatatype : LDatatype Visibility :=
  { name := "Gamma"
    typeArgs := []
    constrs := [
      { name := ⟨"GammaValue", .unres⟩, args := [
          (⟨"Gamma$GammaValueProj0", .unres⟩, .tcons "Epsilon" []),
          (⟨"Gamma$GammaValueProj1", .unres⟩, .tcons "Zeta" [])
        ], testerName := "Gamma$isGammaValue" }
    ]
    constrs_ne := by decide }

/-- Delta = DeltaValue Zeta -/
def deltaDatatype : LDatatype Visibility :=
  { name := "Delta"
    typeArgs := []
    constrs := [
      { name := ⟨"DeltaValue", .unres⟩, args := [(⟨"Delta$DeltaValueProj0", .unres⟩, .tcons "Zeta" [])], testerName := "Delta$isDeltaValue" }
    ]
    constrs_ne := by decide }

/-- Epsilon = EpsilonValue Zeta -/
def epsilonDatatype : LDatatype Visibility :=
  { name := "Epsilon"
    typeArgs := []
    constrs := [
      { name := ⟨"EpsilonValue", .unres⟩, args := [(⟨"Epsilon$EpsilonValueProj0", .unres⟩, .tcons "Zeta" [])], testerName := "Epsilon$isEpsilonValue" }
    ]
    constrs_ne := by decide }

/-- Zeta = ZetaValue int -/
def zetaDatatype : LDatatype Visibility :=
  { name := "Zeta"
    typeArgs := []
    constrs := [
      { name := ⟨"ZetaValue", .unres⟩, args := [(⟨"Zeta$ZetaValueProj0", .unres⟩, .int)], testerName := "Zeta$isZetaValue" }
    ]
    constrs_ne := by decide }

/--
info: (declare-datatype Zeta (
  (ZetaValue (Zeta$ZetaValueProj0 Int))))
(declare-datatype Epsilon (
  (EpsilonValue (Epsilon$EpsilonValueProj0 Zeta))))
(declare-datatype Gamma (
  (GammaValue (Gamma$GammaValueProj0 Epsilon) (Gamma$GammaValueProj1 Zeta))))
(declare-datatype Delta (
  (DeltaValue (Delta$DeltaValueProj0 Zeta))))
(declare-datatype Beta (
  (BetaValue (Beta$BetaValueProj0 Delta) (Beta$BetaValueProj1 Epsilon))))
(declare-datatype Alpha (
  (AlphaValue (Alpha$AlphaValueProj0 Beta) (Alpha$AlphaValueProj1 Gamma))))
; alphaVar
(declare-const f0 Alpha)
(define-fun t0 () Alpha f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "alphaVar") (.some (.tcons "Alpha" [])))
  [alphaDatatype, betaDatatype, gammaDatatype, deltaDatatype, epsilonDatatype, zetaDatatype]

-- Test 17: Diamond dependency pattern
-- Dependencies: Diamond -> Left, Right
--              Left -> Root
--              Right -> Root
-- Actual topological order: Root, Right, Left, Diamond (or Root, Left, Right, Diamond)

/-- Root = RootValue int -/
def rootDatatype : LDatatype Visibility :=
  { name := "Root"
    typeArgs := []
    constrs := [
      { name := ⟨"RootValue", .unres⟩, args := [(⟨"Root$RootValueProj0", .unres⟩, .int)], testerName := "Root$isRootValue" }
    ]
    constrs_ne := by decide }

/-- Left = LeftValue Root -/
def leftDatatype : LDatatype Visibility :=
  { name := "Left"
    typeArgs := []
    constrs := [
      { name := ⟨"LeftValue", .unres⟩, args := [(⟨"Left$LeftValueProj0", .unres⟩, .tcons "Root" [])], testerName := "Left$isLeftValue" }
    ]
    constrs_ne := by decide }

/-- Right = RightValue Root -/
def rightDatatype : LDatatype Visibility :=
  { name := "Right"
    typeArgs := []
    constrs := [
      { name := ⟨"RightValue", .unres⟩, args := [(⟨"Right$RightValueProj0", .unres⟩, .tcons "Root" [])], testerName := "Right$isRightValue" }
    ]
    constrs_ne := by decide }

/-- Diamond = DiamondValue Left Right -/
def diamondDatatype : LDatatype Visibility :=
  { name := "Diamond"
    typeArgs := []
    constrs := [
      { name := ⟨"DiamondValue", .unres⟩, args := [
          (⟨"Diamond$DiamondValueProj0", .unres⟩, .tcons "Left" []),
          (⟨"Diamond$DiamondValueProj1", .unres⟩, .tcons "Right" [])
        ], testerName := "Diamond$isDiamondValue" }
    ]
    constrs_ne := by decide }

/--
info: (declare-datatype Root (
  (RootValue (Root$RootValueProj0 Int))))
(declare-datatype Right (
  (RightValue (Right$RightValueProj0 Root))))
(declare-datatype Left (
  (LeftValue (Left$LeftValueProj0 Root))))
(declare-datatype Diamond (
  (DiamondValue (Diamond$DiamondValueProj0 Left) (Diamond$DiamondValueProj1 Right))))
; diamondVar
(declare-const f0 Diamond)
(define-fun t0 () Diamond f0)
-/
#guard_msgs in
#eval format <$> toSMTStringWithDatatypes
  (.fvar () (CoreIdent.unres "diamondVar") (.some (.tcons "Diamond" [])))
  [diamondDatatype, leftDatatype, rightDatatype, rootDatatype]

end DatatypeTests

end Core
