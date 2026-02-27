/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program
import Strata.DL.Imperative.Imperative
import Strata.Util.FileRange

open Std (ToFormat Format format)

-------------------------------------------------------------------------------

/-! # Transform constructs in Imperative to CProverGOTO's Programs

## Known limitations

The following Imperative constructs are not yet fully translated to GOTO:

### Commands (`Cmd`)
- (none — all commands are now handled)

### Statements (`Stmt`)
- **`funcDecl`**: Returns an error. Local function declarations are not supported.
- **`loop` invariant/measure**: Loop invariants are emitted as
  `#spec_loop_invariant` and decreases clauses as `#spec_decreases`
  named sub-expressions on the backward-edge GOTO instruction's guard,
  recognized by CBMC's DFCC with `--apply-loop-contracts`.

### Core-level (`CmdExt`, handled in `StrataMain.lean`)
- **`call`**: Returns an error; the pipeline requires procedure calls to be
  inlined before GOTO translation. Direct translation to FUNCTION_CALL
  instructions would be more scalable.
-/

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
  fileMap : Option Lean.FileMap := none
  /-- Pending exit GOTOs: (instruction array index, target label). -/
  pendingExits : List (Nat × Option String) := []

/-- Extract a CProverGOTO.SourceLocation from Imperative metadata.
    Uses the FileMap (if available) to convert byte offsets to line/column. -/
def metadataToSourceLoc {P : PureExpr} [BEq P.Ident]
    (md : MetaData P) (functionName : String) (fileMap : Option Lean.FileMap)
    (comment : String := "") : SourceLocation :=
  match Imperative.getFileRange md with
  | some fr =>
    let file := match fr.file with | .file path => path
    let (line, column) := match fileMap with
      | some fm =>
        let pos := fm.toPosition fr.range.start
        (pos.line, pos.column)
      | none =>
        -- Without a FileMap we cannot map byte offsets to lines.
        -- Use byte offset as a rough indicator (better than 0).
        (fr.range.start.byteIdx, 0)
    { file, line, column, function := functionName, workingDir := "", comment }
  | none =>
    { SourceLocation.nil with function := functionName, comment }

-------------------------------------------------------------------------------

/-! ## Imperative's Commands to CProverGOTO's Instructions -/

/--
Convert an `Imperative` command to one or more `CProverGOTO.Instruction`s.

Source location information is extracted from the metadata field of each
Imperative command and used to populate the `CProverGOTO.Instruction`'s
`sourceLoc` field.
-/
def Cmd.toGotoInstructions {P} [G: ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String) (c : Cmd P) (trans : GotoTransform P.TyEnv) :
    Except Format (GotoTransform P.TyEnv) := do
  match c with
  | .init v ty e md =>
    -- The `init` command declares a new variable `v` and optionally assigns
    -- expression `e` to it. It yields a DECL and (if e is some) an ASSIGN.
    let T := G.updateType T v ty
    let gty ← G.toGotoType ty
    let v_expr := Expr.symbol (G.identToString v) gty
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let decl_inst :=
      { type := .DECL, locationNum := trans.nextLoc,
        sourceLoc := srcLoc,
        code := Code.decl v_expr }
    match e with
    | some expr =>
      let e_expr ← G.toGotoExpr expr
      let assign_inst :=
        { type := .ASSIGN, locationNum := (trans.nextLoc + 1),
          sourceLoc := srcLoc,
          code := Code.assign v_expr e_expr }
      return { trans with
                instructions := trans.instructions.append #[decl_inst, assign_inst],
                nextLoc := trans.nextLoc + 2,
                T := T }
    | none =>
      return { trans with
                instructions := trans.instructions.push decl_inst,
                nextLoc := trans.nextLoc + 1,
                T := T }
  | .set v e md =>
    let gty ← G.lookupType T v
    let v_expr := Expr.symbol (G.identToString v) gty
    let e_expr ← G.toGotoExpr e
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let assign_inst :=
      { type := .ASSIGN, locationNum := trans.nextLoc,
        sourceLoc := srcLoc,
        code := Code.assign v_expr e_expr }
    return { trans with
             instructions := trans.instructions.push assign_inst,
             nextLoc := trans.nextLoc + 1,
             T := T }
  | .assert name b md =>
    let expr ← G.toGotoExpr b
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap (comment := name)
    let assert_inst :=
    { type := .ASSERT, locationNum := trans.nextLoc,
      sourceLoc := srcLoc
      guard := expr }
    return { trans with
              instructions := trans.instructions.push assert_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .assume name b md =>
    let expr ← G.toGotoExpr b
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap (comment := name)
    let assume_inst :=
    { type := .ASSUME, locationNum := trans.nextLoc,
      sourceLoc := srcLoc
      guard := expr }
    return { trans with
              instructions := trans.instructions.push assume_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .havoc v md =>
    let gty ← G.lookupType T v
    let v_expr := Expr.symbol (G.identToString v) gty
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let e_expr :=
      { id := .side_effect .Nondet,
        sourceLoc := srcLoc,
        type := gty,
        /- (TODO) Do we want havoc'd variables to be null too? -/
        -- namedFields := [("is_nondet_nullable", Expr.constant "1" Ty.Integer)]
      }
    let assign_inst :=
      { type := .ASSIGN, locationNum := trans.nextLoc,
        sourceLoc := srcLoc,
        code := Code.assign v_expr e_expr }
    return { trans with
              instructions := trans.instructions.push assign_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }
  | .cover name b md =>
    let expr ← G.toGotoExpr b
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap (comment := s!"cover {name}")
    let assert_inst :=
    { type := .ASSERT, locationNum := trans.nextLoc,
      sourceLoc := srcLoc
      guard := expr }
    return { trans with
              instructions := trans.instructions.push assert_inst,
              nextLoc := trans.nextLoc + 1,
              T := T }

def Cmds.toGotoTransform {P} [G: ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String) (cs : Cmds P) (loc : Nat := 0)
    (fileMap : Option Lean.FileMap := none) :
    Except Format (GotoTransform P.TyEnv) := do
  let rec go (trans : GotoTransform P.TyEnv) (cs' : List (Cmd P)) :
      Except Format (GotoTransform P.TyEnv) :=
    match cs' with
    | [] => .ok trans
    | c :: rest => do
      let new_trans ← Cmd.toGotoInstructions trans.T functionName c trans
      go new_trans rest
  go { instructions := #[], nextLoc := loc, T := T, fileMap := fileMap } cs

-------------------------------------------------------------------------------

/-! ## Imperative's Statements to CProverGOTO's Instructions -/

/-! ### Instruction emission helpers

These small helpers factor out the repetitive pattern of creating a GOTO
instruction, pushing it onto the transform, and advancing `nextLoc`.
They are used by the `.ite` and `.loop` cases of `Stmt.toGotoInstructions`.
-/

/-- Emit a GOTO instruction with the given guard and optional target.
    Returns the updated transform and the array index of the emitted instruction. -/
def emitGoto {T : Type} (srcLoc : SourceLocation)
    (target : Option Target) (trans : GotoTransform T)
    (guard : Expr := Expr.true) : GotoTransform T × Nat :=
  let idx := trans.instructions.size
  let inst : Instruction :=
    { type := .GOTO, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      guard := guard, target := target }
  ({ trans with instructions := trans.instructions.push inst,
                nextLoc := trans.nextLoc + 1 }, idx)

/-- Emit a conditional GOTO whose target is not yet known (will be patched). -/
def emitCondGoto {T : Type} (guard : Expr) (srcLoc : SourceLocation)
    (trans : GotoTransform T) : GotoTransform T × Nat :=
  emitGoto srcLoc .none trans (guard := guard)

/-- Emit an unconditional GOTO whose target is not yet known (will be patched). -/
def emitUncondGoto {T : Type} (srcLoc : SourceLocation)
    (trans : GotoTransform T) : GotoTransform T × Nat :=
  emitGoto srcLoc .none trans

/-- Emit a LOCATION instruction with the given label. -/
def emitLabel {T : Type} (label : String) (srcLoc : SourceLocation)
    (trans : GotoTransform T) : GotoTransform T :=
  let inst : Instruction :=
    { type := .LOCATION, locationNum := trans.nextLoc, sourceLoc := srcLoc,
      labels := [label], code := Code.skip }
  { trans with instructions := trans.instructions.push inst,
               nextLoc := trans.nextLoc + 1 }

/-- Patch the targets of previously-emitted GOTO instructions.
    Each pair `(idx, targetLoc)` sets the target of the instruction at array
    index `idx` to location number `targetLoc`. -/
def patchGotoTargets {T : Type} (trans : GotoTransform T)
    (patches : List (Nat × Nat)) : GotoTransform T :=
  let insts := patches.foldl (fun acc (idx, tgt) =>
    acc.set! idx { acc[idx]! with target := .some tgt }) trans.instructions
  { trans with instructions := insts }

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

  | .block label body md =>
    -- Block with label - emit a LOCATION instruction with the label, then process body
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let trans := emitLabel label srcLoc trans
    let trans ← Block.toGotoInstructions trans.T functionName body trans
    -- Patch any pending exits targeting this block's label (or unlabeled exits)
    let end_loc := trans.nextLoc
    let trans := emitLabel s!"end_block_{label}" srcLoc trans
    let (matching, remaining) := trans.pendingExits.partition fun (_, l) =>
      l == some label || l == none
    let patches := matching.map fun (idx, _) => (idx, end_loc)
    return patchGotoTargets { trans with pendingExits := remaining } patches

  | .ite cond thenb elseb md =>
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
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let cond_expr ← G.toGotoExpr cond
    let (trans, goto_else_idx) := emitCondGoto (Expr.not cond_expr) srcLoc trans
    let trans ← Block.toGotoInstructions trans.T functionName thenb trans
    let (trans, goto_end_idx) := emitUncondGoto srcLoc trans
    let else_loc := trans.nextLoc
    let trans := emitLabel s!"else_{else_loc}" srcLoc trans
    let trans ← Block.toGotoInstructions trans.T functionName elseb trans
    let end_loc := trans.nextLoc
    let trans := emitLabel s!"end_if_{else_loc}" srcLoc trans
    return patchGotoTargets trans [(goto_else_idx, else_loc),
                                   (goto_end_idx, end_loc)]

  | .loop guard measure invariants body md =>
    /-
    Loop: while guard do body
    Structure:
      LOCATION loop_start        ; loop entry point
      GOTO [!guard] loop_end     ; exit loop if guard false
      <body instructions>
      GOTO loop_start            ; back edge (with optional loop invariants/decreases)
      LOCATION loop_end          ; after loop
    -/
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let loop_start_loc := trans.nextLoc
    let trans := emitLabel s!"loop_start_{loop_start_loc}" srcLoc trans
    let guard_expr ← G.toGotoExpr guard
    let (trans, goto_end_idx) := emitCondGoto (Expr.not guard_expr) srcLoc trans
    let trans ← Block.toGotoInstructions trans.T functionName body trans
    -- Back edge: attach loop invariants and/or decreases clause
    let hasAnnotation := !invariants.isEmpty || measure.isSome
    if hasAnnotation then
      let mut backGuard := Expr.true
      for inv in invariants do
        let inv_expr ← G.toGotoExpr inv
        backGuard := backGuard.setNamedField "#spec_loop_invariant" inv_expr
      if let some meas := measure then
        let meas_expr ← G.toGotoExpr meas
        backGuard := backGuard.setNamedField "#spec_decreases" meas_expr
      let back_inst : Instruction :=
        { type := .GOTO, locationNum := trans.nextLoc, target := some loop_start_loc,
          guard := backGuard, sourceLoc := srcLoc }
      let trans := { trans with
        instructions := trans.instructions.push back_inst,
        nextLoc := trans.nextLoc + 1 }
      let loop_end_loc := trans.nextLoc
      let trans := emitLabel s!"loop_end_{loop_start_loc}" srcLoc trans
      return patchGotoTargets trans [(goto_end_idx, loop_end_loc)]
    else
      let (trans, _) := emitGoto srcLoc (.some loop_start_loc) trans
      let loop_end_loc := trans.nextLoc
      let trans := emitLabel s!"loop_end_{loop_start_loc}" srcLoc trans
      return patchGotoTargets trans [(goto_end_idx, loop_end_loc)]

  | .exit label md =>
    -- Emit an unconditional GOTO whose target will be patched by the enclosing block.
    let srcLoc := metadataToSourceLoc md functionName trans.fileMap
    let (trans, idx) := emitUncondGoto srcLoc trans
    return { trans with pendingExits := (idx, label) :: trans.pendingExits }

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
    (functionName : String) (stmts : List (Stmt P (Cmd P))) (loc : Nat := 0)
    (fileMap : Option Lean.FileMap := none) :
    Except Format (GotoTransform P.TyEnv) := do
  let trans ← Block.toGotoInstructions T functionName stmts
    { instructions := #[], nextLoc := loc, T := T, fileMap := fileMap }
  if !trans.pendingExits.isEmpty then
    let labels := trans.pendingExits.map fun (_, l) => match l with
      | some s => s!"exit {s}" | none => "exit (unlabeled)"
    .error f!"Unresolved exit statements: {labels}"
  else
    return trans

-------------------------------------------------------------------------------
