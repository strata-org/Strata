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

class ToGoto (P : PureExpr) where
  -- NOTE: `lookupType` and `updateType` corresponds to the functions `lookup`
  -- and `update` in the `Imperative.TypeContext` class.
  lookupType : P.TyEnv → P.Ident → Except Format GotoIR.Ty
  updateType : P.TyEnv → P.Ident → P.Ty → P.TyEnv
  identToString : P.Ident → String
  toGotoType : P.Ty → Except Format GotoIR.Ty
  toGotoExpr : P.Expr → Except Format GotoIR.Expr

def Cmd.toGotoInstruction {P} [G: ToGoto P] (T : P.TyEnv) (c : Cmd P) (loc : Nat) :
    Except Format (GotoIR.Instruction × P.TyEnv) := do
  match c with
  | .init v ty _e _md =>
    -- (FIXME): Assign e to v?
    let T := G.updateType T v ty
    let gty ← G.toGotoType ty
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let expr := { id := .code .Decl, type := gty, operands := [v_expr] }
    return ({ instrType := .DECL, code := some expr, locationNum := loc }, T)
  | .set v e _md =>
    let gty ← G.lookupType T v
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let e_expr ← G.toGotoExpr e
    let expr := { id := .code .Assign, type := gty, operands := [v_expr, e_expr] }
    return ({ instrType := .ASSIGN, code := some expr, locationNum := loc }, T)
  | .havoc v _md =>
    let gty ← G.lookupType T v
    let v_expr := { id := .symbol (G.identToString v), type := gty }
    let rhs_expr := { id := .nondet, type := gty }
    let expr := { id := .code .Assign, type := gty, operands := [v_expr, rhs_expr] }
    return ({ instrType := .ASSIGN, code := some expr, locationNum := loc }, T)
  | .assert _name b _md =>
    -- TODO: Put `name` in source location field?
    let expr ← G.toGotoExpr b
    return ({ instrType := .ASSERT, guard := expr, locationNum := loc }, T)
  | .assume _name b _md =>
    -- TODO: Put `name` in source location field?
    let expr ← G.toGotoExpr b
    return ({ instrType := .ASSUME, guard := expr, locationNum := loc }, T)

def Cmds.toGotoProgram {P} [G: ToGoto P] (T : P.TyEnv) (cs : Cmds P) (loc : Nat := 0) :
  Except Format (GotoIR.Program × P.TyEnv) := do
  let rec go (instrs : List GotoIR.Instruction) (T' : P.TyEnv) (cs' : List (Cmd P)) (i : Nat) :
      Except Format (List GotoIR.Instruction × P.TyEnv) :=
    match cs' with
    | [] => .ok (instrs.reverse, T')
    | c :: rest => do
      let (instr, T'') ← Cmd.toGotoInstruction T' c (loc + i)
      go (instr :: instrs) T'' rest (i + 1)
  let (instructions, finalT) ← go [] T cs 0
  return ({ instructions := instructions.toArray }, finalT)

end Imperative
-------------------------------------------------------------------------------

section

abbrev LExprTP : Imperative.PureExpr :=
   { Ident := String,
     Expr := Lambda.LExprT String,
     Ty := Lambda.LMonoTy,
     TyEnv := @Lambda.TEnv String,
     EvalEnv := Lambda.LState String
     EqIdent := instDecidableEqString }

/- Commands, parameterized by Lambda expressions. -/
abbrev Cmd := Imperative.Cmd LExprTP

private def lookupType (T : LExprTP.TyEnv) (i : LExprTP.Ident) : Except Format GotoIR.Ty :=
  match T.context.types.find? i with
  | none => .error s!"Cannot find {i} in the type context!"
  | some ty =>
    if ty.isMonoType then
      let ty := ty.toMonoTypeUnsafe
      ty.toGotoType
    else .error f!"Poly-type unexpected in the context for {i}: {ty}"

private def updateType (T : LExprTP.TyEnv) (i : LExprTP.Ident) (ty : LExprTP.Ty) : LExprTP.TyEnv :=
  T.insertInContext i (.forAll [] ty)

instance : Imperative.ToGoto LExprTP where
  lookupType := lookupType
  updateType := updateType
  identToString := (fun i => i)
  toGotoType := Lambda.LMonoTy.toGotoType
  toGotoExpr := Lambda.LExprT.toGotoExpr

open Lambda.LTy.Syntax in
def ExampleProgram1 : Imperative.Cmds LExprTP :=
  [.init "s" mty[bv32] (.const "0" mty[bv32]),
   .set "s" (.const "100" mty[bv32])]

#eval do let (ans, _) ← Imperative.Cmds.toGotoProgram Lambda.TEnv.default ExampleProgram1
          return format ans.instructions

end

-------------------------------------------------------------------------------
