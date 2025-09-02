/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.CProver.Goto
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.Imperative

open Std (ToFormat Format format)
-------------------------------------------------------------------------------

namespace Lambda

def LMonoTy.toGotoType (ty : LMonoTy) : Except Format GotoIR.Ty :=
  match ty with
  | .bitvec n => .ok (.BitVector (.UnsignedBV n))
  | .int => .ok .Integer
  | .bool => .ok .Boolean
  | .string => .ok .String
  | _ => .error f!"[toGotoType] Not yet implemented: {ty}"

def LExprT.getGotoType {Identifier} (e : LExprT Identifier) :
    Except Format GotoIR.Ty := do
  let ty := toLMonoTy e
  ty.toGotoType

def fnToGotoID (fn : String) : Except Format GotoIR.Expr.Identifier :=
  match fn with
  | "bv32AddOp" => .ok (.bin .Plus)
  | "bv32NegOp" => .ok (.bin .Minus)
  | _ => .error f!"[fnToGotoID] Not yet implemented: fn: {fn}"

def LExprT.toGotoExpr {Identifier} [ToString Identifier] (e : LExprT Identifier) :
    Except Format GotoIR.Expr := do
  match e with
  -- Constants
  | .const c ty =>
    let gty ← ty.toGotoType
    return { id := .constant c, type := gty }
  -- Variables
  | .fvar v ty =>
    let gty ← ty.toGotoType
    return { id := .symbol (toString v), type := gty }
  -- Unary Functions
  | .app (.op fn _) e1 ty =>
    let op ← fnToGotoID (toString fn)
    let gty ← ty.toGotoType
    let e1g ← toGotoExpr e1
    return { id := op, type := gty, operands := [e1g] }
  -- Binary Functions
  | .app (.app (.op fn _) e1 _) e2 ty =>
    let op ← fnToGotoID (toString fn)
    let gty ← ty.toGotoType
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := op, type := gty, operands := [e1g, e2g] }
  -- Equality
  | .eq e1 e2 _ =>
    let e1g ← toGotoExpr e1
    let e2g ← toGotoExpr e2
    return { id := .bin .Equal, type := .Boolean, operands := [e1g, e2g] }
  | _ => .error f!"[toGotoExpr] Not yet implemented: {e}"

open LTy.Syntax LExpr.Syntax in
/--
info: ok: { id := GotoIR.Expr.Identifier.constant "1", type := GotoIR.Ty.Integer, operands := [] }
-/
#guard_msgs in
#eval do let ans ← @LExprT.toGotoExpr String _ (.const "1" mty[int])
          return repr ans

end Lambda
-------------------------------------------------------------------------------

namespace Imperative

class ToGoto (P : PureExpr) (T : Type) where
  -- NOTE: `lookupType` corresponds to the function `lookup` in the
  -- `Imperative.TypeContext` class.
  lookupType : T → P.Ident → Except Format GotoIR.Ty
  identToString : P.Ident → String
  toGotoType : P.Ty → Except Format GotoIR.Ty
  toGotoExpr : P.Expr → Except Format GotoIR.Expr

def Cmd.toGotoInstruction {P} [G: ToGoto P T] (TEnv : T) (c : Cmd P) (loc : Nat) :
    Except Format GotoIR.Instruction := do
  match c with
  | .init v ty _e _md =>
    let gty ← G.toGotoType ty
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let expr := { id := .code .Decl, type := gty, operands := [v_expr] }
    return { instrType := .DECL, code := some expr, locationNum := loc }
  | .set v e _md =>
    let gty ← G.lookupType TEnv v
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let e_expr ← G.toGotoExpr e
    let expr := { id := .code .Assign, type := gty, operands := [v_expr, e_expr] }
    return { instrType := .ASSIGN, code := some expr, locationNum := loc }
  | .havoc v _md =>
    let gty ← G.lookupType TEnv v
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let rhs_expr := { id := .nondet, type := gty }
    let expr := { id := .code .Assign, type := gty, operands := [v_expr, rhs_expr] }
    return { instrType := .ASSIGN, code := some expr, locationNum := loc }
  | .assert name b _md =>
    -- TODO: Put `name` in source location field?
    let expr ← G.toGotoExpr b
    return { instrType := .ASSERT, guard := expr, locationNum := loc }
  | .assume name b _md =>
    -- TODO: Put `name` in source location field?
    let expr ← G.toGotoExpr b
    return { instrType := .ASSUME, guard := expr, locationNum := loc }

end Imperative
-------------------------------------------------------------------------------

/-
TODO:

1. GOTO elaborator
2. End-to-end: A small Imperative/Lambda program -> GOTO
3. GOTO Semantics
4. Lean FFI
-/
