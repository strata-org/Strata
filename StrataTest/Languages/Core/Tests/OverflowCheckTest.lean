/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Preconditions

/-! # Tests: signed bitvector overflow safe operators

Verify that SafeAdd/SafeSub/SafeMul/SafeNeg exist and generate
WF obligations (overflow preconditions).
-/

open Strata Core Lambda

-- Verify safe op expressions exist for multiple sizes
#check Core.bv8SafeAddOp
#check Core.bv16SafeAddOp
#check Core.bv32SafeAddOp
#check Core.bv32SafeSubOp
#check Core.bv32SafeMulOp
#check Core.bv32SafeNegOp
#check Core.bv64SafeAddOp

-- Verify overflow predicate expressions exist
#check Core.bv32SAddOverflowOp
#check Core.bv32SSubOverflowOp
#check Core.bv32SMulOverflowOp
#check Core.bv32SNegOverflowOp

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
