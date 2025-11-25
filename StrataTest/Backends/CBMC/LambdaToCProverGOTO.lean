/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.Backends.CBMC.GOTO.Expr

namespace Lambda
open Std (ToFormat Format format)
-------------------------------------------------------------------------------

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()

def LMonoTy.toGotoType (ty : LMonoTy) : Except Format CProverGOTO.Ty :=
  match ty with
  | .bitvec n => .ok (CProverGOTO.Ty.UnsignedBV n)
  | .int => .ok .Integer
  | .bool => .ok .Boolean
  | .string => .ok .String
  | _ => .error f!"[toGotoType] Not yet implemented: {ty}"

def LExprT.getGotoType {T : LExprParamsT} (e : LExprT T) :
    Except Format CProverGOTO.Ty := do
  let ty := LExpr.toLMonoTy e
  ty.toGotoType

def fnToGotoID (fn : String) : Except Format CProverGOTO.Expr.Identifier :=
  match fn with
  | "Bv32.Add" => .ok (.multiary .Plus)
  | "Bv32.Lt" | "Bv32.ULt" => .ok (.binary .Lt)
  | _ => .error f!"[fnToGotoID] Not yet implemented: fn: {fn}"

/--
Mapping `LExprT` (Lambda expressions obtained after the type inference
transform) to GOTO expressions.
-/
def LExprT.toGotoExpr {TBase: LExprParamsT} [ToString TBase.base.IDMeta] (e : LExprT TBase) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const m c =>
    let gty ← m.type.toGotoType
    return (Expr.constant (toString c) gty)
  -- Variables
  | .fvar m v _ =>
    let gty ← m.type.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Binary Functions
  | .app m (.app _ (.op _ fn _) e1) e2 =>
    let op ← fnToGotoID (toString fn)
    let gty ← m.type.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app m (.op _ fn _) e1 =>
    let op ← fnToGotoID (toString fn)
    let gty ← m.type.toGotoType
    let e1g ← toGotoExpr e1
    return { id := op, type := gty, operands := [e1g] }
  -- Equality
  | .eq _ e1 e2 =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {e}"

/--
Mapping `LExpr` to GOTO expressions (for LMonoTy-typed expressions).
-/
def LExpr.toGotoExpr {TBase: LExprParams} [ToString $ LExpr TBase.mono] (e : LExpr TBase.mono) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const _ c  =>
    let gty ← c.ty.toGotoType
    return (Expr.constant (toString c) gty)
  -- Variables
  | .fvar _ v (some ty) =>
    let gty ← ty.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Binary Functions
  | .app _ (.app _ (.op _ fn (some ty)) e1) e2 =>
    let op ← fnToGotoID (toString fn)
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app _ (.op _ fn (some ty)) e1 =>
    let op ← fnToGotoID (toString fn)
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let e1g ← toGotoExpr e1
    return { id := op, type := gty, operands := [e1g] }
  -- Equality
  | .eq _ e1 e2 =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {toString e}"

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
