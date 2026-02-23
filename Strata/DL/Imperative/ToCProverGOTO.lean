/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program
import Strata.DL.Imperative.Imperative

open Std (ToFormat Format format)

-------------------------------------------------------------------------------

/-! # Transform constructs in Imperative to CProverGOTO's Programs -/

namespace Imperative

class ToGoto (P : PureExpr) where
  -- NOTE: `lookupType` and `updateType` correspond to the functions `lookup`
  -- and `update` in the `Imperative.TypeContext` class.
  lookupType : P.TyEnv → P.Ident → Except Format CProverGOTO.Ty
  updateType : P.TyEnv → P.Ident → P.Ty → P.TyEnv
  identToString : P.Ident → String
  toGotoType : P.Ty → Except Format CProverGOTO.Ty
  toGotoExpr : P.Expr → Except Format CProverGOTO.Expr

structure GotoTransform (TypeEnv : Type) where
  instructions : Array CProverGOTO.Instruction
  nextLoc : Nat
  T : TypeEnv

-------------------------------------------------------------------------------

/-! ## Imperative's Commands to CProverGOTO's Instructions -/

open CProverGOTO in
/--
Convert an `Imperative` command to one or more `CProverGOTO.Instruction`s.

(TODO): Populate `CProverGOTO.Instruction`'s source location from the metadata
field of the Imperative command. For now, we just populate source location's
"comment" field with assertion/assumption names.
-/
def Cmd.toGotoInstructions {P} [G: ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String) (c : Cmd P) (trans : GotoTransform P.TyEnv) :
    Except Format (GotoTransform P.TyEnv) := do
  match c with
  | .init v ty e _md =>
    -- The `init` command declares a new variable `v` and assigns the expression
    -- `e` to it. It yields two GOTO instructions: a DECL and an ASSIGN.
    let T := G.updateType T v ty
    let gty ← G.toGotoType ty
    let v_expr := Expr.symbol (G.identToString v) gty
    let decl_inst :=
      { type := .DECL, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        code := Code.decl v_expr }
    match e with
    | some expr =>
      let e_expr ← G.toGotoExpr expr
      let assign_inst :=
        { type := .ASSIGN, locationNum := (trans.nextLoc + 1),
          sourceLoc := { SourceLocation.nil with function := functionName },
          code := Code.assign v_expr e_expr }
      return { trans with
                instructions := trans.instructions.append #[decl_inst, assign_inst],
                nextLoc := trans.nextLoc + 2,
                T := T }
    | none =>
      -- Init without expression - just declare
      return { trans with
                instructions := trans.instructions.append #[decl_inst],
                nextLoc := trans.nextLoc + 1,
                T := T }
  | .set v e _md =>
    let gty ← G.lookupType T v
    let v_expr := Expr.symbol (G.identToString v) gty
    let e_expr ← G.toGotoExpr e
    let assign_inst :=
      { type := .ASSIGN, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        code := Code.assign v_expr e_expr }
    return { trans with
             instructions := trans.instructions.push assign_inst,
             nextLoc := trans.nextLoc + 1,
             T := T }
  | .assert name b _md =>
    let expr ← G.toGotoExpr b
    let assert_inst :=
    { type := .ASSERT, locationNum := trans.nextLoc,
      sourceLoc := { SourceLocation.nil with comment := name, function := functionName }
      guard := expr }
    return { trans with
              instructions := trans.instructions.push assert_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .assume name b _md =>
    let expr ← G.toGotoExpr b
    let assume_inst :=
    { type := .ASSUME, locationNum := trans.nextLoc,
      sourceLoc := { SourceLocation.nil with comment := name, function := functionName }
      guard := expr }
    return { trans with
              instructions := trans.instructions.push assume_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .havoc v _md =>
    let gty ← G.lookupType T v
    let v_expr := Expr.symbol (G.identToString v) gty
    let e_expr :=
      { id := .side_effect .Nondet,
        sourceLoc := { SourceLocation.nil with function := functionName },
        type := gty,
        /- (TODO) Do we want havoc'd variables to be null too? -/
        -- namedFields := [("is_nondet_nullable", Expr.constant "1" Ty.Integer)]
      }
    let assign_inst :=
      { type := .ASSIGN, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        code := Code.assign v_expr e_expr }
    return { trans with
              instructions := trans.instructions.push assign_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .cover name _b md =>
    .error s!"{MetaData.formatFileRangeD md} [cover {name}]\
               Unimplemented command."

open CProverGOTO in
def Cmds.toGotoTransform {P} [G: ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String) (cs : Cmds P) (loc : Nat := 0) :
    Except Format (GotoTransform P.TyEnv) := do
  let rec go (trans : GotoTransform P.TyEnv) (cs' : List (Cmd P)) :
      Except Format (GotoTransform P.TyEnv) :=
    match cs' with
    | [] => .ok trans
    | c :: rest => do
      let new_trans ← Cmd.toGotoInstructions trans.T functionName c trans
      go new_trans rest
  go { instructions := #[], nextLoc := loc, T := T } cs

-------------------------------------------------------------------------------
