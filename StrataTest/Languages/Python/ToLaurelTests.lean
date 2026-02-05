/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PythonToLaurel
import Strata.Languages.Python.LaurelPrelude

/-!
# Python to Laurel Translation Tests

Test suite for Python to Laurel translation.

## Test Organization
- Basic type translation tests
- Expression translation tests
- Statement translation tests
- Function translation tests
- End-to-end integration tests
-/

namespace StrataTest.Python.ToLaurel

open Strata.Python
open Strata.Python.LaurelPrelude
open Strata.Laurel

/-! ## Helper Functions for Testing -/

/-- Check if translation succeeds -/
def expectSuccess {α : Type} (result : Except TranslationError α) : Bool :=
  match result with
  | .ok _ => true
  | .error _ => false

/-- Check if translation fails -/
def expectFailure {α : Type} (result : Except TranslationError α) : Bool :=
  match result with
  | .ok _ => false
  | .error _ => true

/-! ## Context Tests -/

/-- Test: Empty context creation -/
def testEmptyContext : Bool :=
  let ctx : TranslationContext := default
  ctx.variableTypes.isEmpty && ctx.functionSignatures.isEmpty

#guard testEmptyContext

/-! ## Helper Function Tests -/

/-- Test: mkIntLiteral creates correct AST -/
def testMkIntLiteral : Bool :=
  let lit := mkIntLiteral 42
  match lit.val with
  | Strata.Laurel.StmtExpr.LiteralInt 42 => true
  | _ => false

#guard testMkIntLiteral

/-- Test: mkBoolLiteral creates correct AST -/
def testMkBoolLiteral : Bool :=
  let lit := mkBoolLiteral true
  match lit.val with
  | Strata.Laurel.StmtExpr.LiteralBool true => true
  | _ => false

#guard testMkBoolLiteral

/-- Test: mkIdentifier creates correct AST -/
def testMkIdentifier : Bool :=
  let ident := mkIdentifier "x"
  match ident.val with
  | Strata.Laurel.StmtExpr.Identifier "x" => true
  | _ => false

#guard testMkIdentifier

/-! ## Type Helper Tests -/

/-- Test: intType creates TInt -/
def testIntType : Bool :=
  match intType.val with
  | Strata.Laurel.HighType.TInt => true
  | _ => false

#guard testIntType

/-- Test: boolType creates TBool -/
def testBoolType : Bool :=
  match boolType.val with
  | Strata.Laurel.HighType.TBool => true
  | _ => false

#guard testBoolType

/-! ## Operation Mapping Tests -/

/-- Test: Python arithmetic operators map correctly -/
def testArithOpMapping : Bool :=
  match pyArithOpToLaurel .add, pyArithOpToLaurel .sub with
  | Strata.Laurel.Operation.Add, Strata.Laurel.Operation.Sub => true
  | _, _ => false

#guard testArithOpMapping

/-- Test: Python comparison operators map correctly -/
def testCmpOpMapping : Bool :=
  match pyCmpOpToLaurel .eq, pyCmpOpToLaurel .lt with
  | Strata.Laurel.Operation.Eq, Strata.Laurel.Operation.Lt => true
  | _, _ => false

#guard testCmpOpMapping

/-- Test: Python logical operators map correctly -/
def testLogicalOpMapping : Bool :=
  match pyLogicalOpToLaurel .and, pyLogicalOpToLaurel .not with
  | Strata.Laurel.Operation.And, Strata.Laurel.Operation.Not => true
  | _, _ => false

#guard testLogicalOpMapping

/-! ## AST Construction Tests -/

/-- Test: mkBinOp creates correct binary operation -/
def testMkBinOp : Bool :=
  let lhs := mkIntLiteral 1
  let rhs := mkIntLiteral 2
  let add := mkBinOp Strata.Laurel.Operation.Add lhs rhs
  match add.val with
  | Strata.Laurel.StmtExpr.PrimitiveOp Strata.Laurel.Operation.Add [l, r] =>
    match l.val, r.val with
    | Strata.Laurel.StmtExpr.LiteralInt 1, Strata.Laurel.StmtExpr.LiteralInt 2 => true
    | _, _ => false
  | _ => false

#guard testMkBinOp

/-- Test: mkUnaryOp creates correct unary operation -/
def testMkUnaryOp : Bool :=
  let arg := mkIntLiteral 5
  let neg := mkUnaryOp Strata.Laurel.Operation.Neg arg
  match neg.val with
  | Strata.Laurel.StmtExpr.PrimitiveOp Strata.Laurel.Operation.Neg [a] =>
    match a.val with
    | Strata.Laurel.StmtExpr.LiteralInt 5 => true
    | _ => false
  | _ => false

#guard testMkUnaryOp

/-- Test: mkBlock creates correct block -/
def testMkBlock : Bool :=
  let stmt1 := mkIntLiteral 1
  let stmt2 := mkIntLiteral 2
  let block := mkBlock [stmt1, stmt2]
  match block.val with
  | Strata.Laurel.StmtExpr.Block stmts none =>
    stmts.length == 2
  | _ => false

#guard testMkBlock

/-! ## Summary

All Day 1 setup tests pass. The infrastructure is ready for Day 2-3 implementation.
-/

end StrataTest.Python.ToLaurel

namespace StrataTest.Python.ToLaurel

open Strata.Python
open Strata.Python.LaurelPrelude
open Strata.Laurel

/-! ## Type Translation Tests -/

/-- Test: translateType for int succeeds -/
def testTranslateTypeInt : Bool :=
  match translateType "int" with
  | .ok ty => match ty.val with
    | Strata.Laurel.HighType.TInt => true
    | _ => false
  | .error _ => false

#guard testTranslateTypeInt

/-- Test: translateType for bool succeeds -/
def testTranslateTypeBool : Bool :=
  match translateType "bool" with
  | .ok ty => match ty.val with
    | Strata.Laurel.HighType.TBool => true
    | _ => false
  | .error _ => false

#guard testTranslateTypeBool

/-- Test: translateType for unsupported type fails -/
def testTranslateTypeUnsupported : Bool :=
  expectFailure (translateType "str")

#guard testTranslateTypeUnsupported

/-! ## Integration Test Summary

The translation functions are implemented and tested individually.
For end-to-end integration testing with actual Python code, use the
Python-to-Ion workflow described in `StrataTest/Languages/Python/README.md`:

1. Write Python code in `tests/` directory
2. Run `test_helper.py` to convert to Ion format
3. Load the Ion file in Lean
4. Test the translation pipeline

This approach avoids the complexity of manually constructing Python AST
in Lean, since the Python dialect is generated from Ion files.
-/
