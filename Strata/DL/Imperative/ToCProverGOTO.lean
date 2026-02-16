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

open CProverGOTO

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
    let e_expr ← G.toGotoExpr e
    let assign_inst :=
      { type := .ASSIGN, locationNum := (trans.nextLoc + 1),
        sourceLoc := { SourceLocation.nil with function := functionName },
        code := Code.assign v_expr e_expr }
    return { trans with
              instructions := trans.instructions.append #[decl_inst, assign_inst],
              nextLoc := trans.nextLoc + 2,
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

/-! ## Imperative's Statements to CProverGOTO's Instructions -/

/-
Mutual recursion between Stmt.toGotoInstructions and Block.toGotoInstructions:
Statements can contain blocks (e.g., in .ite and .loop), and blocks contain statements.
This mutual dependency requires both functions to be defined in a mutual block.
-/
mutual

/--
Convert an `Imperative.Stmt` to one or more `CProverGOTO.Instruction`s.

This function handles all statement types including control flow constructs like
blocks, conditionals, and loops.
-/
def Stmt.toGotoInstructions {P} [G: ToGoto P] [BEq P.Ident]
    (_T : P.TyEnv) (functionName : String) (s : Stmt P (Cmd P)) (trans : GotoTransform P.TyEnv) :
    Except Format (GotoTransform P.TyEnv) := do
  match s with
  | .cmd c =>
    -- Atomic command - delegate to existing Cmd transformation
    Cmd.toGotoInstructions trans.T functionName c trans

  | .block label body _md =>
    -- Block with label - emit a LOCATION instruction with the label, then process body
    let label_inst : Instruction :=
      { type := .LOCATION,
        locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        labels := [label],
        code := Code.skip }
    let trans := { trans with
                    instructions := trans.instructions.push label_inst,
                    nextLoc := trans.nextLoc + 1 }
    Block.toGotoInstructions trans.T functionName body trans

  | .ite cond thenb elseb _md =>
    /-
    Conditional: if cond then thenb else elseb
    Structure:
      GOTO [!cond] else_label    ; jump to else branch if condition is false
      <then branch instructions>
      GOTO end_label             ; skip else branch
      LOCATION else_label        ; else branch starts here
      <else branch instructions>
      LOCATION end_label         ; after conditional
    -/
    let else_label := s!"else_{trans.nextLoc}"
    let end_label := s!"end_if_{trans.nextLoc}"

    -- Emit conditional GOTO to else branch
    let cond_expr ← G.toGotoExpr cond
    let neg_cond := Expr.not cond_expr
    let goto_else_inst : Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        guard := neg_cond, target := .none }
    let trans := { trans with
                    instructions := trans.instructions.push goto_else_inst,
                    nextLoc := trans.nextLoc + 1 }
    let goto_else_loc := trans.nextLoc - 1

    -- Process then branch
    let trans ← Block.toGotoInstructions trans.T functionName thenb trans

    -- Emit unconditional GOTO to end
    let goto_end_inst : Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        guard := Expr.true, target := .none }
    let trans := { trans with
                    instructions := trans.instructions.push goto_end_inst,
                    nextLoc := trans.nextLoc + 1 }
    let goto_end_loc := trans.nextLoc - 1

    -- Emit else branch label
    let else_loc := trans.nextLoc
    let else_label_inst : Instruction :=
      { type := .LOCATION, locationNum := else_loc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        labels := [else_label], code := Code.skip }
    let trans := { trans with
                    instructions := trans.instructions.push else_label_inst,
                    nextLoc := trans.nextLoc + 1 }

    -- Process else branch
    let trans ← Block.toGotoInstructions trans.T functionName elseb trans

    -- Emit end label
    let end_loc := trans.nextLoc
    let end_label_inst : Instruction :=
      { type := .LOCATION, locationNum := end_loc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        labels := [end_label], code := Code.skip }
    let trans := { trans with
                    instructions := trans.instructions.push end_label_inst,
                    nextLoc := trans.nextLoc + 1 }

    -- Patch GOTO targets
    let insts := trans.instructions
    let insts := insts.set! goto_else_loc
      { insts[goto_else_loc]! with target := .some else_loc }
    let insts := insts.set! goto_end_loc
      { insts[goto_end_loc]! with target := .some end_loc }
    return { trans with instructions := insts }

  | .loop guard _measure _invariant body _md =>
    /-
    Loop: while guard do body
    Structure:
      LOCATION loop_start        ; loop entry point
      GOTO [!guard] loop_end     ; exit loop if guard false
      <body instructions>
      GOTO loop_start            ; back edge
      LOCATION loop_end          ; after loop
    -/
    let loop_start_label := s!"loop_start_{trans.nextLoc}"
    let loop_end_label := s!"loop_end_{trans.nextLoc}"

    -- Emit loop start label
    let loop_start_loc := trans.nextLoc
    let loop_start_inst : Instruction :=
      { type := .LOCATION, locationNum := loop_start_loc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        labels := [loop_start_label], code := Code.skip }
    let trans := { trans with
                    instructions := trans.instructions.push loop_start_inst,
                    nextLoc := trans.nextLoc + 1 }

    -- Emit conditional GOTO to exit loop
    let guard_expr ← G.toGotoExpr guard
    let neg_guard := Expr.not guard_expr
    let goto_end_inst : Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        guard := neg_guard, target := .none }
    let trans := { trans with
                    instructions := trans.instructions.push goto_end_inst,
                    nextLoc := trans.nextLoc + 1 }
    let goto_end_loc := trans.nextLoc - 1

    -- Process loop body
    let trans ← Block.toGotoInstructions trans.T functionName body trans

    -- Emit unconditional GOTO back to loop start
    let goto_start_inst : Instruction :=
      { type := .GOTO, locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        guard := Expr.true, target := .some loop_start_loc }
    let trans := { trans with
                    instructions := trans.instructions.push goto_start_inst,
                    nextLoc := trans.nextLoc + 1 }

    -- Emit loop end label
    let loop_end_loc := trans.nextLoc
    let loop_end_inst : Instruction :=
      { type := .LOCATION, locationNum := loop_end_loc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        labels := [loop_end_label], code := Code.skip }
    let trans := { trans with
                    instructions := trans.instructions.push loop_end_inst,
                    nextLoc := trans.nextLoc + 1 }

    -- Patch GOTO to loop end
    let insts := trans.instructions
    let insts := insts.set! goto_end_loc
      { insts[goto_end_loc]! with target := .some loop_end_loc }
    return { trans with instructions := insts }

  | .goto label _md =>
    -- Goto statement - creates an incomplete GOTO (target will be resolved later)
    -- Note: In a full implementation, we would need a second pass to resolve labels
    let goto_inst : Instruction :=
      { type := .INCOMPLETE_GOTO,
        locationNum := trans.nextLoc,
        sourceLoc := { SourceLocation.nil with function := functionName },
        code := Code.goto label }
    return { trans with
              instructions := trans.instructions.push goto_inst,
              nextLoc := trans.nextLoc + 1 }

  | .funcDecl _decl _md =>
    -- Function declarations are not yet supported in GOTO translation
    .error "funcDecl: Unimplemented statement."
termination_by Stmt.sizeOf s
decreasing_by all_goals simp [*] at * <;> omega

/--
Convert a block (list of statements) to GOTO instructions.
-/
def Block.toGotoInstructions {P} [G: ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String) (stmts : Block P (Cmd P)) (trans : GotoTransform P.TyEnv) :
    Except Format (GotoTransform P.TyEnv) := do
  match stmts with
  | [] => return trans
  | s :: rest => do
    let new_trans ← Stmt.toGotoInstructions T functionName s trans
    Block.toGotoInstructions T functionName rest new_trans
termination_by Block.sizeOf stmts
decreasing_by all_goals simp [*] at * <;> omega
end

/--
Transform a block of statements to a GotoTransform structure.
This is the main entry point for statement transformation.
-/
def Stmts.toGotoTransform {P} [G: ToGoto P] [BEq P.Ident] (T : P.TyEnv)
    (functionName : String) (stmts : List (Stmt P (Cmd P))) (loc : Nat := 0) :
    Except Format (GotoTransform P.TyEnv) := do
  Block.toGotoInstructions T functionName stmts { instructions := #[], nextLoc := loc, T := T }

-------------------------------------------------------------------------------
