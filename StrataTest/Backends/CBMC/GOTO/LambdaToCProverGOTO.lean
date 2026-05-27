/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.LambdaToCProverGOTO

namespace Lambda

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

open LTy.Syntax LExpr.Syntax in
/--
info: ok: { id := CProverGOTO.Expr.Identifier.nullary (CProverGOTO.Expr.Identifier.Nullary.constant "1"),
  type := { id := CProverGOTO.Ty.Identifier.primitive (CProverGOTO.Ty.Identifier.Primitive.integer),
            subtypes := [],
            sourceLoc := { file := "", line := 0, column := 0, function := "", workingDir := "", comment := "" } },
  operands := [],
  sourceLoc := { file := "", line := 0, column := 0, function := "", workingDir := "", comment := "" },
  namedFields := [] }
-/
#guard_msgs in
#eval do let ans ← @LExprT.toGotoExpr TestParams.mono _ (.const ⟨(), mty[int]⟩ (LConst.intConst 1))
          return repr ans

-- Test Int.DivT maps to div
#eval do
  let .ok r := fnToGotoID "Int.DivT" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div

-- Test Int.ModT maps to mod
#eval do
  let .ok r := fnToGotoID "Int.ModT" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Mod

-- Test BV operators (representative sample across widths)
#eval do
  -- Bv8
  let .ok r := fnToGotoID "Bv8.Add" | IO.throwServerError "Bv8.Add"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Plus
  let .ok r := fnToGotoID "Bv8.Not" | IO.throwServerError "Bv8.Not"
  assert! r == CProverGOTO.Expr.Identifier.unary .Bitnot
  -- Bv16
  let .ok r := fnToGotoID "Bv16.Sub" | IO.throwServerError "Bv16.Sub"
  assert! r == CProverGOTO.Expr.Identifier.binary .Minus
  let .ok r := fnToGotoID "Bv16.And" | IO.throwServerError "Bv16.And"
  assert! r == CProverGOTO.Expr.Identifier.binary .Bitand
  -- Bv32 (all ops)
  let .ok r := fnToGotoID "Bv32.Add" | IO.throwServerError "Bv32.Add"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Plus
  let .ok r := fnToGotoID "Bv32.Neg" | IO.throwServerError "Bv32.Neg"
  assert! r == CProverGOTO.Expr.Identifier.unary .UnaryMinus
  let .ok r := fnToGotoID "Bv32.UDiv" | IO.throwServerError "Bv32.UDiv"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div
  let .ok r := fnToGotoID "Bv32.Or" | IO.throwServerError "Bv32.Or"
  assert! r == CProverGOTO.Expr.Identifier.binary .Bitor
  let .ok r := fnToGotoID "Bv32.Xor" | IO.throwServerError "Bv32.Xor"
  assert! r == CProverGOTO.Expr.Identifier.binary .Bitxor
  let .ok r := fnToGotoID "Bv32.Shl" | IO.throwServerError "Bv32.Shl"
  assert! r == CProverGOTO.Expr.Identifier.binary .Shl
  let .ok r := fnToGotoID "Bv32.UShr" | IO.throwServerError "Bv32.UShr"
  assert! r == CProverGOTO.Expr.Identifier.binary .Lshr
  let .ok r := fnToGotoID "Bv32.SShr" | IO.throwServerError "Bv32.SShr"
  assert! r == CProverGOTO.Expr.Identifier.binary .Ashr
  let .ok r := fnToGotoID "Bv32.ULt" | IO.throwServerError "Bv32.ULt"
  assert! r == CProverGOTO.Expr.Identifier.binary .Lt
  let .ok r := fnToGotoID "Bv32.SLe" | IO.throwServerError "Bv32.SLe"
  assert! r == CProverGOTO.Expr.Identifier.binary .Le
  let .ok r := fnToGotoID "Bv32.SGt" | IO.throwServerError "Bv32.SGt"
  assert! r == CProverGOTO.Expr.Identifier.binary .Gt
  -- Bv64
  let .ok r := fnToGotoID "Bv64.Mul" | IO.throwServerError "Bv64.Mul"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Mult
  let .ok r := fnToGotoID "Bv64.SDiv" | IO.throwServerError "Bv64.SDiv"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div
  let .ok r := fnToGotoID "Bv64.UGe" | IO.throwServerError "Bv64.UGe"
  assert! r == CProverGOTO.Expr.Identifier.binary .Ge

-- Test Real operators
#eval do
  let .ok r := fnToGotoID "Real.Add" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Plus
  let .ok r := fnToGotoID "Real.Sub" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Minus
  let .ok r := fnToGotoID "Real.Mul" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Mult
  let .ok r := fnToGotoID "Real.Div" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div
  let .ok r := fnToGotoID "Real.Neg" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.unary .UnaryMinus
  let .ok r := fnToGotoID "Real.Lt" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Lt
  let .ok r := fnToGotoID "Real.Ge" | IO.throwServerError "failed"
  assert! r == CProverGOTO.Expr.Identifier.binary .Ge

-- Test Int.DivT/ModT (truncating, mapped to GOTO div/mod) and BV Concat
-- Int.Div/SafeDiv and Int.Mod/SafeMod are Euclidean and map to sentinel functionApplications.
#eval do
  let .ok r := fnToGotoID "Int.DivT" | IO.throwServerError "Int.DivT"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div
  let .ok r := fnToGotoID "Int.ModT" | IO.throwServerError "Int.ModT"
  assert! r == CProverGOTO.Expr.Identifier.binary .Mod
  let .ok r := fnToGotoID "Int.SafeDiv" | IO.throwServerError "Int.SafeDiv"
  assert! r == CProverGOTO.Expr.Identifier.functionApplication "Int.EuclideanDiv"
  let .ok r := fnToGotoID "Int.SafeMod" | IO.throwServerError "Int.SafeMod"
  assert! r == CProverGOTO.Expr.Identifier.functionApplication "Int.EuclideanMod"
  let .ok r := fnToGotoID "Bv32.Concat" | IO.throwServerError "Bv32.Concat"
  assert! r == CProverGOTO.Expr.Identifier.binary .Concatenation
  let .ok r := fnToGotoID "Bv8.Concat" | IO.throwServerError "Bv8.Concat"
  assert! r == CProverGOTO.Expr.Identifier.binary .Concatenation

-- Test real type mapping
#eval do
  let .ok r := LMonoTy.toGotoType .real | IO.throwServerError "real type"
  assert! r == CProverGOTO.Ty.Real

-- Test old(expr) maps to unary Old expression
open LTy.Syntax in
#eval do
  -- old(x) where x : int
  -- old is polymorphic: ∀a. a → a, so after type application it's: app (app (op "old" ty) type_arg) x
  let oldOp : LExpr TestParams.mono :=
    .op () (Lambda.Identifier.mk "old" ()) (some mty[int → int → int])
  let typeArg : LExpr TestParams.mono := .const () (.intConst 0)
  let xVar : LExpr TestParams.mono := .fvar () (Lambda.Identifier.mk "x" ()) (some mty[int])
  let oldExpr : LExpr TestParams.mono := .app () (.app () oldOp typeArg) xVar
  let .ok r := LExpr.toGotoExprCtx (TBase := TestParams) [] oldExpr | IO.throwServerError "old(x) failed"
  assert! r.id == CProverGOTO.Expr.Identifier.unary .Old
  assert! r.operands.length == 1

-- Test BV Extract maps to Extractbits
#eval do
  -- fnToGotoID recognizes Extract patterns
  let .ok r := fnToGotoID "Bv32.Extract_31_31" | IO.throwServerError "Extract_31_31"
  assert! r == CProverGOTO.Expr.Identifier.binary .Extractbits
  let .ok r := fnToGotoID "Bv32.Extract_7_0" | IO.throwServerError "Extract_7_0"
  assert! r == CProverGOTO.Expr.Identifier.binary .Extractbits
  let .ok r := fnToGotoID "Bv16.Extract_15_15" | IO.throwServerError "Extract_15_15"
  assert! r == CProverGOTO.Expr.Identifier.binary .Extractbits

-- Test parseBvExtractLo
#eval do
  assert! parseBvExtractLo "Bv32.Extract_7_0" == some 0
  assert! parseBvExtractLo "Bv32.Extract_31_31" == some 31
  assert! parseBvExtractLo "Bv16.Extract_15_15" == some 15
  assert! parseBvExtractLo "Bv16.Extract_7_0" == some 0

-- Test overflow predicate and safe op GOTO translation
#eval do
  -- Overflow predicates → CBMC overflow expressions
  let .ok r := fnToGotoID "Bv32.SAddOverflow" | IO.throwServerError "SAddOverflow"
  assert! r == CProverGOTO.Expr.Identifier.binary .PlusOverflow
  let .ok r := fnToGotoID "Bv32.SSubOverflow" | IO.throwServerError "SSubOverflow"
  assert! r == CProverGOTO.Expr.Identifier.binary .MinusOverflow
  let .ok r := fnToGotoID "Bv32.SMulOverflow" | IO.throwServerError "SMulOverflow"
  assert! r == CProverGOTO.Expr.Identifier.binary .MultOverflow
  let .ok r := fnToGotoID "Bv32.SNegOverflow" | IO.throwServerError "SNegOverflow"
  assert! r == CProverGOTO.Expr.Identifier.unary .UnaryMinusOverflow
  -- Unsigned overflow predicates
  let .ok r := fnToGotoID "Bv32.UAddOverflow" | IO.throwServerError "UAddOverflow"
  assert! r == CProverGOTO.Expr.Identifier.binary .PlusOverflow
  -- Safe ops → same as unsafe
  let .ok r := fnToGotoID "Bv32.SafeAdd" | IO.throwServerError "SafeAdd"
  assert! r == CProverGOTO.Expr.Identifier.multiary .Plus
  let .ok r := fnToGotoID "Bv32.SafeSDiv" | IO.throwServerError "SafeSDiv"
  assert! r == CProverGOTO.Expr.Identifier.binary .Div
  assert! parseBvExtractLo "Bv32.Add" == none
  assert! parseBvExtractLo "Int.Add" == none

-- Test BV Extract expression translation (unary in Core → binary in GOTO)
open LTy.Syntax in
#eval do
  let extractOp : LExpr TestParams.mono :=
    .op () (Lambda.Identifier.mk "Bv32.Extract_7_0" ()) (some mty[bv32 → bv8])
  let xVar : LExpr TestParams.mono := .fvar () (Lambda.Identifier.mk "x" ()) (some mty[bv32])
  let extractExpr : LExpr TestParams.mono := .app () extractOp xVar
  let .ok r := LExpr.toGotoExprCtx (TBase := TestParams) [] extractExpr | IO.throwServerError "extract failed"
  assert! r.id == CProverGOTO.Expr.Identifier.binary .Extractbits
  assert! r.operands.length == 2
  -- Second operand should be the index constant (0)
  let idx := r.operands[1]!
  assert! idx.id == CProverGOTO.Expr.Identifier.nullary (.constant "0")

end Lambda
