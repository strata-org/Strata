/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.DtRankAxioms
import Strata.DL.Lambda.TypeFactory

/-!
## Tests for dtRank axiom generation

Unit tests for `mkDtRankFunc`, `mkDtRankPerConstrAxioms`, and
`mkDtRankDeclsForBlock` from `DtRankAxioms.lean`.
-/

namespace Lambda

open Std (ToFormat Format format)
open LExpr

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TP.Identifier where
  coe s := Identifier.mk s ()

---------------------------------------------------------------------
-- Test datatypes
---------------------------------------------------------------------

private def intListDt : LDatatype Unit :=
  { name := "IntList", typeArgs := [],
    constrs := [
      { name := "Nil", args := [], testerName := "isNil" },
      { name := "Cons",
        args := [("hd", .int), ("tl", .tcons "IntList" [])],
        testerName := "isCons" }
    ], constrs_ne := rfl }

private def myNatDt : LDatatype Unit :=
  { name := "MyNat", typeArgs := [],
    constrs := [
      { name := "Zero", args := [], testerName := "isZero" },
      { name := "Succ",
        args := [("pred", .tcons "MyNat" [])],
        testerName := "isSucc" }
    ], constrs_ne := rfl }

private def roseTreeDt : LDatatype Unit :=
  { name := "RoseTree", typeArgs := [],
    constrs := [
      { name := "Leaf",
        args := [("val", .int)],
        testerName := "isLeaf" },
      { name := "Node",
        args := [("children", .tcons "RoseList" [])],
        testerName := "isNode" }
    ], constrs_ne := rfl }

private def roseListDt : LDatatype Unit :=
  { name := "RoseList", typeArgs := [],
    constrs := [
      { name := "RNil", args := [], testerName := "isRNil" },
      { name := "RCons",
        args := [("hd", .tcons "RoseTree" []), ("tl", .tcons "RoseList" [])],
        testerName := "isRCons" }
    ], constrs_ne := rfl }

private def noRecDt : LDatatype Unit :=
  { name := "Pair", typeArgs := [],
    constrs := [
      { name := "MkPair",
        args := [("fst", .int), ("snd", .int)],
        testerName := "isMkPair" }
    ], constrs_ne := rfl }

---------------------------------------------------------------------
-- Test 1: mkDtRankFunc — correct name, input, output
---------------------------------------------------------------------

/-- info: { name := "IntList..dtRank", metadata := () } -/
#guard_msgs in
#eval (mkDtRankFunc (T := TP) intListDt).name

/-- info: [({ name := "x", metadata := () }, Lambda.LMonoTy.tcons "IntList" [])] -/
#guard_msgs in
#eval (mkDtRankFunc (T := TP) intListDt).inputs

/-- info: Lambda.LMonoTy.tcons "int" [] -/
#guard_msgs in
#eval (mkDtRankFunc (T := TP) intListDt).output

---------------------------------------------------------------------
-- Test 2: mkDtRankFunc for MyNat
---------------------------------------------------------------------

/-- info: { name := "MyNat..dtRank", metadata := () } -/
#guard_msgs in
#eval (mkDtRankFunc (T := TP) myNatDt).name

---------------------------------------------------------------------
-- Test 3: Per-constructor axioms for IntList
-- Nil has no recursive fields → no axioms
-- Cons has one recursive field (tl) → one axiom
---------------------------------------------------------------------

private def intListBlock : MutualDatatype Unit := [intListDt]

/-- info: 1 -/
#guard_msgs in
#eval (mkDtRankPerConstrAxioms (T := TP) intListDt intListBlock ()).length

/--
info: (∀ (bvar:int) (∀ (bvar:IntList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~IntList..dtRank : (arrow IntList int)) %0)
   ((~IntList..dtRank : (arrow IntList int)) ((~Cons : (arrow int (arrow IntList IntList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkDtRankPerConstrAxioms (T := TP) intListDt intListBlock ())[0]!

---------------------------------------------------------------------
-- Test 3b: Non-negativity axiom for IntList
-- ∀ x : IntList. IntList..dtRank(x) >= 0
---------------------------------------------------------------------

/-- info: (∀ (bvar:IntList) ((~Int.Ge : (arrow int (arrow int bool))) ((~IntList..dtRank : (arrow IntList int)) %0) #0)) -/
#guard_msgs in
#eval format (mkDtRankNonNegAxiom (T := TP) intListDt ())

---------------------------------------------------------------------
-- Test 3c: mkDtRankAxioms includes non-neg + per-constructor
-- IntList: 1 non-neg + 1 per-constructor = 2
---------------------------------------------------------------------

/-- info: 2 -/
#guard_msgs in
#eval (mkDtRankAxioms (T := TP) intListDt intListBlock ()).length

---------------------------------------------------------------------
-- Test 4: Per-constructor axioms for MyNat
-- Zero has no recursive fields → no axioms
-- Succ has one recursive field (pred) → one axiom
---------------------------------------------------------------------

private def myNatBlock : MutualDatatype Unit := [myNatDt]

/-- info: 1 -/
#guard_msgs in
#eval (mkDtRankPerConstrAxioms (T := TP) myNatDt myNatBlock ()).length

-- MyNat..dtRank(pred) < MyNat..dtRank(Succ(pred))
/--
info: (∀ (bvar:MyNat) ((~Int.Lt : (arrow int (arrow int bool)))
  ((~MyNat..dtRank : (arrow MyNat int)) %0)
  ((~MyNat..dtRank : (arrow MyNat int)) ((~Succ : (arrow MyNat MyNat)) %0))))
-/
#guard_msgs in
#eval format (mkDtRankPerConstrAxioms (T := TP) myNatDt myNatBlock ())[0]!

---------------------------------------------------------------------
-- Test 5: No axioms for a datatype with no recursive fields
---------------------------------------------------------------------

private def noRecBlock : MutualDatatype Unit := [noRecDt]

/-- info: 0 -/
#guard_msgs in
#eval (mkDtRankPerConstrAxioms (T := TP) noRecDt noRecBlock ()).length

---------------------------------------------------------------------
-- Test 6: Mutual datatypes — RoseTree (via mkDtRankAxioms)
-- Non-neg axiom + 1 per-constructor (Node's children field) = 2
---------------------------------------------------------------------

private def roseBlock : MutualDatatype Unit := [roseTreeDt, roseListDt]

/-- info: 2 -/
#guard_msgs in
#eval (mkDtRankAxioms (T := TP) roseTreeDt roseBlock ()).length

-- Axiom 0: non-negativity
/-- info: (∀ (bvar:RoseTree) ((~Int.Ge : (arrow int (arrow int bool))) ((~RoseTree..dtRank : (arrow RoseTree int)) %0) #0)) -/
#guard_msgs in
#eval format (mkDtRankAxioms (T := TP) roseTreeDt roseBlock ())[0]!

-- Axiom 1: RoseList..dtRank(children) < RoseTree..dtRank(Node(children))
/--
info: (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
  ((~RoseList..dtRank : (arrow RoseList int)) %0)
  ((~RoseTree..dtRank : (arrow RoseTree int)) ((~Node : (arrow RoseList RoseTree)) %0))))
-/
#guard_msgs in
#eval format (mkDtRankAxioms (T := TP) roseTreeDt roseBlock ())[1]!

---------------------------------------------------------------------
-- Test 7: Mutual datatypes — RoseList (via mkDtRankAxioms)
-- Non-neg axiom + 2 per-constructor (RCons hd and tl) = 3
---------------------------------------------------------------------

/-- info: 3 -/
#guard_msgs in
#eval (mkDtRankAxioms (T := TP) roseListDt roseBlock ()).length

-- Axiom 0: non-negativity
/-- info: (∀ (bvar:RoseList) ((~Int.Ge : (arrow int (arrow int bool))) ((~RoseList..dtRank : (arrow RoseList int)) %0) #0)) -/
#guard_msgs in
#eval format (mkDtRankAxioms (T := TP) roseListDt roseBlock ())[0]!

-- Axiom 1: RoseTree..dtRank(hd) < RoseList..dtRank(RCons(hd, tl))
/--
info: (∀ (bvar:RoseTree) (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~RoseTree..dtRank : (arrow RoseTree int)) %1)
   ((~RoseList..dtRank : (arrow RoseList int)) ((~RCons : (arrow RoseTree (arrow RoseList RoseList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkDtRankAxioms (T := TP) roseListDt roseBlock ())[1]!

-- Axiom 2: RoseList..dtRank(tl) < RoseList..dtRank(RCons(hd, tl))
/--
info: (∀ (bvar:RoseTree) (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~RoseList..dtRank : (arrow RoseList int)) %0)
   ((~RoseList..dtRank : (arrow RoseList int)) ((~RCons : (arrow RoseTree (arrow RoseList RoseList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkDtRankAxioms (T := TP) roseListDt roseBlock ())[2]!

---------------------------------------------------------------------
-- Test 8: mkDtRankDeclsForBlock — generates funcs + axioms for all types
---------------------------------------------------------------------

/-- info: 2 -/
#guard_msgs in
#eval (mkDtRankDeclsForBlock (T := TP) roseBlock ()).1.length

/-- info: 5 -/
#guard_msgs in
#eval (mkDtRankDeclsForBlock (T := TP) roseBlock ()).2.length

/-- info: [{ name := "RoseTree..dtRank", metadata := () }, { name := "RoseList..dtRank", metadata := () }] -/
#guard_msgs in
#eval (mkDtRankDeclsForBlock (T := TP) roseBlock ()).1.map (·.name)

end Lambda
