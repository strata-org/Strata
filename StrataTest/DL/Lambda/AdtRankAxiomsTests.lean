/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.AdtRankAxioms
import Strata.DL.Lambda.TypeFactory

/-!
## Tests for adtRank axiom generation

Unit tests for `mkAdtRankFunc`, `mkAdtRankPerConstrAxioms`, and
`mkAdtRankDeclsForBlock` from `AdtRankAxioms.lean`.
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
-- Test 1: mkAdtRankFunc — correct name, input, output
---------------------------------------------------------------------

/-- info: { name := "IntList..adtRank", metadata := () } -/
#guard_msgs in
#eval (mkAdtRankFunc (T := TP) intListDt).name

/-- info: [({ name := "x", metadata := () }, Lambda.LMonoTy.tcons "IntList" [])] -/
#guard_msgs in
#eval (mkAdtRankFunc (T := TP) intListDt).inputs

/-- info: Lambda.LMonoTy.tcons "int" [] -/
#guard_msgs in
#eval (mkAdtRankFunc (T := TP) intListDt).output

---------------------------------------------------------------------
-- Test 2: Per-constructor axioms for IntList
-- Nil has no recursive fields → no axioms
-- Cons has one recursive field (tl) → one axiom
---------------------------------------------------------------------

private def intListBlock : MutualDatatype Unit := [intListDt]

/-- info: 1 -/
#guard_msgs in
#eval (mkAdtRankPerConstrAxioms (T := TP) intListDt intListBlock ()).length

/--
info: (∀ (bvar:int) (∀ (bvar:IntList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~IntList..adtRank : (arrow IntList int)) %0)
   ((~IntList..adtRank : (arrow IntList int)) ((~Cons : (arrow int (arrow IntList IntList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkAdtRankPerConstrAxioms (T := TP) intListDt intListBlock ())[0]!

---------------------------------------------------------------------
-- Test 3b: Non-negativity axiom for IntList
-- ∀ x : IntList. IntList..adtRank(x) >= 0
---------------------------------------------------------------------

/-- info: (∀ (bvar:IntList) ((~Int.Ge : (arrow int (arrow int bool))) ((~IntList..adtRank : (arrow IntList int)) %0) #0)) -/
#guard_msgs in
#eval format (mkAdtRankNonNegAxiom (T := TP) intListDt ())

---------------------------------------------------------------------
-- Test 3: Per-constructor axioms for MyNat
-- Zero has no recursive fields → no axioms
-- Succ has one recursive field (pred) → one axiom
---------------------------------------------------------------------

private def myNatBlock : MutualDatatype Unit := [myNatDt]

/-- info: 1 -/
#guard_msgs in
#eval (mkAdtRankPerConstrAxioms (T := TP) myNatDt myNatBlock ()).length

-- MyNat..adtRank(pred) < MyNat..adtRank(Succ(pred))
/--
info: (∀ (bvar:MyNat) ((~Int.Lt : (arrow int (arrow int bool)))
  ((~MyNat..adtRank : (arrow MyNat int)) %0)
  ((~MyNat..adtRank : (arrow MyNat int)) ((~Succ : (arrow MyNat MyNat)) %0))))
-/
#guard_msgs in
#eval format (mkAdtRankPerConstrAxioms (T := TP) myNatDt myNatBlock ())[0]!

---------------------------------------------------------------------
-- Test 5: No axioms for a datatype with no recursive fields
---------------------------------------------------------------------

private def noRecBlock : MutualDatatype Unit := [noRecDt]

/-- info: 0 -/
#guard_msgs in
#eval (mkAdtRankPerConstrAxioms (T := TP) noRecDt noRecBlock ()).length

---------------------------------------------------------------------
-- Test 6: Mutual datatypes — RoseTree (via mkAdtRankAxioms)
-- Non-neg axiom + 1 per-constructor (Node's children field) = 2
---------------------------------------------------------------------

private def roseBlock : MutualDatatype Unit := [roseTreeDt, roseListDt]

/-- info: 2 -/
#guard_msgs in
#eval (mkAdtRankAxioms (T := TP) roseTreeDt roseBlock ()).length

-- Axiom 0: non-negativity
/-- info: (∀ (bvar:RoseTree) ((~Int.Ge : (arrow int (arrow int bool))) ((~RoseTree..adtRank : (arrow RoseTree int)) %0) #0)) -/
#guard_msgs in
#eval format (mkAdtRankAxioms (T := TP) roseTreeDt roseBlock ())[0]!

-- Axiom 1: RoseList..adtRank(children) < RoseTree..adtRank(Node(children))
/--
info: (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
  ((~RoseList..adtRank : (arrow RoseList int)) %0)
  ((~RoseTree..adtRank : (arrow RoseTree int)) ((~Node : (arrow RoseList RoseTree)) %0))))
-/
#guard_msgs in
#eval format (mkAdtRankAxioms (T := TP) roseTreeDt roseBlock ())[1]!

---------------------------------------------------------------------
-- Test 7: Mutual datatypes — RoseList (via mkAdtRankAxioms)
-- Non-neg axiom + 2 per-constructor (RCons hd and tl) = 3
---------------------------------------------------------------------

/-- info: 3 -/
#guard_msgs in
#eval (mkAdtRankAxioms (T := TP) roseListDt roseBlock ()).length

-- Axiom 0: non-negativity
/-- info: (∀ (bvar:RoseList) ((~Int.Ge : (arrow int (arrow int bool))) ((~RoseList..adtRank : (arrow RoseList int)) %0) #0)) -/
#guard_msgs in
#eval format (mkAdtRankAxioms (T := TP) roseListDt roseBlock ())[0]!

-- Axiom 1: RoseTree..adtRank(hd) < RoseList..adtRank(RCons(hd, tl))
/--
info: (∀ (bvar:RoseTree) (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~RoseTree..adtRank : (arrow RoseTree int)) %1)
   ((~RoseList..adtRank : (arrow RoseList int)) ((~RCons : (arrow RoseTree (arrow RoseList RoseList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkAdtRankAxioms (T := TP) roseListDt roseBlock ())[1]!

-- Axiom 2: RoseList..adtRank(tl) < RoseList..adtRank(RCons(hd, tl))
/--
info: (∀ (bvar:RoseTree) (∀ (bvar:RoseList) ((~Int.Lt : (arrow int (arrow int bool)))
   ((~RoseList..adtRank : (arrow RoseList int)) %0)
   ((~RoseList..adtRank : (arrow RoseList int)) ((~RCons : (arrow RoseTree (arrow RoseList RoseList))) %1 %0)))))
-/
#guard_msgs in
#eval format (mkAdtRankAxioms (T := TP) roseListDt roseBlock ())[2]!

---------------------------------------------------------------------
-- Test 8: mkAdtRankDeclsForBlock — generates funcs + axioms for all types
---------------------------------------------------------------------

/-- info: 2 -/
#guard_msgs in
#eval (mkAdtRankDeclsForBlock (T := TP) roseBlock ()).1.length

/-- info: 5 -/
#guard_msgs in
#eval (mkAdtRankDeclsForBlock (T := TP) roseBlock ()).2.length

/-- info: [{ name := "RoseTree..adtRank", metadata := () }, { name := "RoseList..adtRank", metadata := () }] -/
#guard_msgs in
#eval (mkAdtRankDeclsForBlock (T := TP) roseBlock ()).1.map (·.name)

end Lambda
