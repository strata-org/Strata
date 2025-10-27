/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Lambda
import Strata.Backends.CBMC.GOTO.Expr

namespace Lambda
open Std (ToFormat Format format)
-------------------------------------------------------------------------------

def LMonoTy.toGotoType (ty : LMonoTy) : Except Format CProverGOTO.Ty :=
  match ty with
  | .bitvec n => .ok (CProverGOTO.Ty.UnsignedBV n)
  | .int => .ok .Integer
  | .bool => .ok .Boolean
  | .string => .ok .String
  | _ => .error f!"[toGotoType] Not yet implemented: {ty}"

def LExprT.getGotoType {IDMeta} (e : LExprT IDMeta) :
    Except Format CProverGOTO.Ty := do
  let ty := toLMonoTy e
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
def LExprT.toGotoExpr {IDMeta} [ToString IDMeta] (e : LExprT IDMeta) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const c ty =>
    let gty ← ty.toGotoType
    return (Expr.constant c gty)
  -- Variables
  | .fvar v ty =>
    let gty ← ty.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Binary Functions
  | .app (.app (.op fn _) e1 _) e2 ty =>
    let op ← fnToGotoID (toString fn)
    let gty ← ty.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app (.op fn _) e1 ty =>
    let op ← fnToGotoID (toString fn)
    let gty ← ty.toGotoType
    let e1g ← toGotoExpr e1
    return { id := op, type := gty, operands := [e1g] }
  -- Equality
  | .eq e1 e2 _ =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {e}"

/--
Mapping `LExpr` to GOTO expressions.
-/
def LExpr.toGotoExpr {IDMeta} [ToString IDMeta] (e : LExpr LMonoTy IDMeta) :
    Except Format CProverGOTO.Expr :=
  open CProverGOTO in
  do match e with
  -- Constants
  | .const c (some ty) =>
    let gty ← ty.toGotoType
    return (Expr.constant c gty)
  -- Variables
  | .fvar v (some ty) =>
    let gty ← ty.toGotoType
    return (Expr.symbol (toString v) gty)
  -- Binary Functions
  | .app (.app (.op fn (some ty)) e1) e2 =>
    let op ← fnToGotoID (toString fn)
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Unary Functions
  | .app (.op fn (some ty)) e1 =>
    let op ← fnToGotoID (toString fn)
    let retty := ty.destructArrow.getLast!
    let gty ← retty.toGotoType
    let e1g ← toGotoExpr e1
    return { id := op, type := gty, operands := [e1g] }
  -- Equality
  | .eq e1 e2 =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .binary .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {e}"

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
#eval do let ans ← @LExprT.toGotoExpr String _ (.const "1" mty[int])
          return repr ans
