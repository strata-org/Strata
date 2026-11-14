/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all Strata.Languages.Core.Factory
meta import all Strata.DL.Lambda.Preconditions
meta import all Strata.Transform.PrecondElim

meta section

/-! # Tests: overflow safe operators

Verify that safe operators exist and generate WF obligations (overflow preconditions).
-/

open Strata Core Lambda
private abbrev testLoc : ExprSourceLoc := ExprSourceLoc.synthesized "test"

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
  (LExpr.mkApp testLoc Core.bv32SafeAddOp [
    .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 32))])).length == 1

-- Verify WF obligations are generated for safe neg (1 precondition)
#guard (collectWFObligations Core.Factory
  (.app testLoc Core.bv8SafeNegOp
    (.fvar testLoc ⟨"x", ()⟩ (some (.bitvec 8))))).length == 1

-- Verify no WF obligations for unsafe add (no precondition)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp testLoc Core.bv32AddOp [
    .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 32))])).length == 0

-- Verify SafeSDiv has 2 preconditions (div-by-zero + overflow)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp testLoc Core.bv32SafeSDivOp [
    .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 32))])).length == 2

-- Verify SDivOverflow predicate and SafeSDiv/SafeSMod exist
example := Core.bv32SDivOverflowOp
example := Core.bv32SafeSDivOp
example := Core.bv32SafeSModOp

-- Verify SafeUAdd has 1 precondition (unsigned overflow)
#guard (collectWFObligations Core.Factory
  (LExpr.mkApp testLoc Core.bv8SafeUAddOp [
    .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 8)),
    .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 8))])).length == 1

-- Verify unsigned overflow predicates and safe ops exist
example := Core.bv32UAddOverflowOp
example := Core.bv32USubOverflowOp
example := Core.bv32UMulOverflowOp
example := Core.bv32UNegOverflowOp
example := Core.bv32SafeUAddOp
example := Core.bv32SafeUSubOp
example := Core.bv32SafeUMulOp
example := Core.bv32SafeUNegOp

-- Verify SafeSDiv precondition classification: precond 0 = divisionByZero, precond 1 = arithmeticOverflow
open Strata Core Lambda Core.PrecondElim Imperative in
private def sdivStmts :=
  collectPrecondAsserts Core.Factory
    (LExpr.mkApp testLoc Core.bv32SafeSDivOp [
      .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 32)),
      .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 32))]) "test" #[]

#guard sdivStmts.length == 2
-- First is divisionByZero, second is arithmeticOverflow.
open Strata Core Lambda Imperative in
#guard (match sdivStmts[0]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.divisionByZero
open Strata Core Lambda Imperative in
#guard (match sdivStmts[1]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.arithmeticOverflow

-- Verify nested SafeSDiv: both inner and outer calls get correct classification
open Strata Core Lambda Core.PrecondElim Imperative in
private def nestedStmts :=
  collectPrecondAsserts Core.Factory
    (LExpr.mkApp testLoc Core.bv32SafeSDivOp [
      LExpr.mkApp testLoc Core.bv32SafeSDivOp [
        .fvar testLoc ⟨"x", ()⟩ (some (.bitvec 32)),
        .fvar testLoc ⟨"y", ()⟩ (some (.bitvec 32))],
      .fvar testLoc ⟨"z", ()⟩ (some (.bitvec 32))]) "test" #[]

#guard nestedStmts.length == 4
-- Inner call: precond 0 = divisionByZero, precond 1 = arithmeticOverflow;
-- outer call: precond 2 = divisionByZero, precond 3 = arithmeticOverflow.
open Strata Core Lambda Imperative in
#guard (match nestedStmts[0]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.divisionByZero
open Strata Core Lambda Imperative in
#guard (match nestedStmts[1]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.arithmeticOverflow
open Strata Core Lambda Imperative in
#guard (match nestedStmts[2]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.divisionByZero
open Strata Core Lambda Imperative in
#guard (match nestedStmts[3]! with | Statement.assert _ _ md => md.getPropertyType | _ => none)
  == some MetaData.arithmeticOverflow

end
