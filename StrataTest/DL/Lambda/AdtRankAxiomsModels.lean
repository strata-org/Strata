/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-!
## Models for adtRank Axioms

We define concrete interpretations (size functions) for IntList and
RoseTree/RoseList and prove they satisfy the properties implied by
the generated adtRank axioms:
1. Non-negativity: `adtRank(x) >= 0`
2. Strict decrease: for each recursive field of a constructor,
   `adtRank(field) < adtRank(C(fields...))`

This establishes that the axiom sets are consistent (have a model).
-/

namespace AdtRankAxiomsModels

---------------------------------------------------------------------
-- IntList
---------------------------------------------------------------------

inductive IntList where
  | nil : IntList
  | cons : Int → IntList → IntList

def IntList.adtRank : IntList → Int
  | .nil => 0
  | .cons _ tl => IntList.adtRank tl + 1

theorem IntList.adtRank_non_neg (x : IntList) : IntList.adtRank x >= 0 := by
  induction x with
  | nil => simp [adtRank]
  | cons _ tl ih => simp [adtRank]; omega

theorem IntList.adtRank_cons_decreases (hd : Int) (tl : IntList) :
    IntList.adtRank tl < IntList.adtRank (.cons hd tl) := by
  simp [adtRank]; omega

---------------------------------------------------------------------
-- RoseTree / RoseList (mutual datatypes)
---------------------------------------------------------------------

mutual
inductive RoseTree where
  | leaf : Int → RoseTree
  | node : RoseList → RoseTree

inductive RoseList where
  | rnil : RoseList
  | rcons : RoseTree → RoseList → RoseList
end

mutual
def RoseTree.adtRank : RoseTree → Int
  | .leaf _ => 0
  | .node children => RoseList.adtRank children + 1

def RoseList.adtRank : RoseList → Int
  | .rnil => 0
  | .rcons hd tl => max (RoseTree.adtRank hd) (RoseList.adtRank tl) + 1
end

-- Non-negativity
mutual
theorem RoseTree.adtRank_non_neg (x : RoseTree) : RoseTree.adtRank x >= 0 := by
  match x with
  | .leaf _ => simp [RoseTree.adtRank]
  | .node children =>
    simp [RoseTree.adtRank]
    have h := RoseList.adtRank_non_neg children
    omega

theorem RoseList.adtRank_non_neg (x : RoseList) : RoseList.adtRank x >= 0 := by
  match x with
  | .rnil => simp [RoseList.adtRank]
  | .rcons hd tl =>
    simp [RoseList.adtRank]
    have h1 := RoseTree.adtRank_non_neg hd
    have h2 := RoseList.adtRank_non_neg tl
    omega
end

-- Strict decrease: Node's children field
theorem RoseTree.adtRank_node_decreases (children : RoseList) :
    RoseList.adtRank children < RoseTree.adtRank (.node children) := by
  simp [RoseTree.adtRank]; omega

-- Strict decrease: RCons's hd field
theorem RoseList.adtRank_rcons_hd_decreases (hd : RoseTree) (tl : RoseList) :
    RoseTree.adtRank hd < RoseList.adtRank (.rcons hd tl) := by
  simp [RoseList.adtRank]
  have h := RoseList.adtRank_non_neg tl
  omega

-- Strict decrease: RCons's tl field
theorem RoseList.adtRank_rcons_tl_decreases (hd : RoseTree) (tl : RoseList) :
    RoseList.adtRank tl < RoseList.adtRank (.rcons hd tl) := by
  simp [RoseList.adtRank]
  have h := RoseTree.adtRank_non_neg hd
  omega

end AdtRankAxiomsModels
