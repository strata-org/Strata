/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Preconditions

/-! # Tests: overflow safe operators

Verify that safe operators exist and generate WF obligations (overflow preconditions).
-/

open Strata Core Lambda

-- Verify safe op expressions exist for multiple sizes (silent compilation check)
example := Core.bv8SafeAddOp
example := Core.bv16SafeAddOp
example := Core.bv32SafeAddOp
example := Core.bv32SafeSubOp
example := Core.bv32SafeMulOp
example := Core.bv32SafeNegOp
example := Core.bv64SafeAddOp

-- Verify overflow predicate expressions exist
example := Core.bv32SAddOverflowOp
example := Core.bv32SSubOverflowOp
example := Core.bv32SMulOverflowOp
example := Core.bv32SNegOverflowOp

-- Verify WF obligations are generated for safe add (1 precondition)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp () Core.bv32SafeAddOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 32))])).length == 1

-- Verify WF obligations are generated for safe neg (1 precondition)
#guard (collectWFObligations Core.Factory
  (.app () Core.bv8SafeNegOp
    (.fvar () ⟨"x", ()⟩ (some (.bitvec 8))))).length == 1

-- Verify no WF obligations for unsafe add (no precondition)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp () Core.bv32AddOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 32))])).length == 0

-- Verify SafeSDiv has 2 preconditions (div-by-zero + overflow)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp () Core.bv32SafeSDivOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 32))])).length == 2

-- Verify SDivOverflow predicate and SafeSDiv/SafeSMod exist
example := Core.bv32SDivOverflowOp
example := Core.bv32SafeSDivOp
example := Core.bv32SafeSModOp

-- Verify SafeUAdd has 1 precondition (unsigned overflow)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp () Core.bv8SafeUAddOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 8)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 8))])).length == 1

-- Verify unsigned overflow predicates and safe ops exist
example := Core.bv32UAddOverflowOp
example := Core.bv32USubOverflowOp
example := Core.bv32UMulOverflowOp
example := Core.bv32UNegOverflowOp
example := Core.bv32SafeUAddOp
example := Core.bv32SafeUSubOp
example := Core.bv32SafeUMulOp
example := Core.bv32SafeUNegOp
