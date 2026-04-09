/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Preconditions
import Strata.Transform.PrecondElim

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

-- Verify SafeSDiv precondition classification: precond 0 = divisionByZero, precond 1 = arithmeticOverflow
open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let expr := LExpr.mkApp () Core.bv32SafeSDivOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 32))]
  let stmts := collectPrecondAsserts Core.Factory expr "test" #[]
  assert! stmts.length == 2
  -- First should be divisionByZero
  let md0 : MetaData Core.Expression := match stmts[0]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md0.getPropertyType == some MetaData.divisionByZero
  -- Second should be arithmeticOverflow
  let md1 : MetaData Core.Expression := match stmts[1]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md1.getPropertyType == some MetaData.arithmeticOverflow

-- Verify nested SafeSDiv: both inner and outer calls get correct classification
open Strata Core Lambda Core.PrecondElim Imperative in
#eval do
  let innerDiv := LExpr.mkApp () Core.bv32SafeSDivOp [
    .fvar () ⟨"x", ()⟩ (some (.bitvec 32)),
    .fvar () ⟨"y", ()⟩ (some (.bitvec 32))]
  let outerDiv := LExpr.mkApp () Core.bv32SafeSDivOp [
    innerDiv,
    .fvar () ⟨"z", ()⟩ (some (.bitvec 32))]
  let stmts := collectPrecondAsserts Core.Factory outerDiv "test" #[]
  assert! stmts.length == 4
  -- Inner call: precond 0 = divisionByZero, precond 1 = arithmeticOverflow
  let md0 : MetaData Core.Expression := match stmts[0]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md0.getPropertyType == some MetaData.divisionByZero
  let md1 : MetaData Core.Expression := match stmts[1]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md1.getPropertyType == some MetaData.arithmeticOverflow
  -- Outer call: precond 0 = divisionByZero, precond 1 = arithmeticOverflow
  let md2 : MetaData Core.Expression := match stmts[2]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md2.getPropertyType == some MetaData.divisionByZero
  let md3 : MetaData Core.Expression := match stmts[3]! with | Statement.assert _ _ md => md | _ => #[]
  assert! md3.getPropertyType == some MetaData.arithmeticOverflow
