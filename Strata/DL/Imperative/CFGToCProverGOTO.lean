/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.BasicBlock
import Strata.DL.Imperative.ToCProverGOTO

/-! # CFG to CProverGOTO Translation

Translates an Imperative dialect CFG (deterministic basic blocks with string
labels) into a flat array of CProverGOTO instructions.

The existing `Stmt.toGotoInstructions` path translates structured statements
directly to GOTO instructions, interleaving control-flow lowering (emitting
conditional jumps, patching forward references) with CBMC-specific concerns
(source locations, instruction encoding). This module separates those two
responsibilities: `StructuredToUnstructured.stmtsToCFG` handles the
control-flow lowering once, producing a backend-agnostic CFG, and this module
handles only the straightforward mapping from CFG blocks to GOTO instructions.

This separation makes it easier to target additional backends (each only needs
to consume the CFG) and to reason about the control-flow lowering independently
of any particular backend.

## Gaps relative to the direct `Stmt.toGotoInstructions` path

The following features are not yet supported via the CFG path, and would need
to be addressed before it can fully replace the direct path:

- **Source locations on control flow**: `StructuredToUnstructured` discards
  `MetaData` from `ite`, `loop`, `block`, and `exit` statements, so transfer
  commands in the CFG carry no source location information.
- **Loop contracts**: The direct path emits `#spec_loop_invariant` and
  `#spec_decreases` as named sub-expressions on the backward-edge GOTO
  instruction (recognized by CBMC's DFCC). In the CFG, invariants are lowered
  to plain `assert` commands and measures are discarded entirely.
  To fix: `StructuredToUnstructured.stmtsToBlocks` (the `.loop` case) would
  need to preserve invariants and measures in the `DetTransferCmd` (or in a
  side channel), and this module would need to emit them as named
  sub-expressions on the backward-edge GOTO, mirroring the logic in the
  `.loop` case of `Stmt.toGotoInstructions` in `ToCProverGOTO.lean`.
- **`Core.CmdExt.call`**: This translation handles `Imperative.Cmd` only.
  Core procedure calls (`CmdExt.call`) would need a command translator
  analogous to `coreStmtsToGoto` in `CoreToGOTOPipeline.lean`.
-/

namespace Imperative

open CProverGOTO
open Std (Format format)

/-- Translate a deterministic CFG to CProverGOTO instructions.

    The translation processes blocks in the order they appear in `cfg.blocks`.
    For each block:
    1. Record the current location number as the block's entry point
    2. Translate each command using `Cmd.toGotoInstructions`
    3. Translate the transfer command:
       - `condGoto c lt lf` → GOTO [!c] lf; GOTO lt (conditional + fallthrough)
       - `finish` → no instruction (handled by END_FUNCTION in the caller)

    After all blocks are emitted, a second pass patches GOTO targets using the
    label-to-location map built during the first pass.
-/
def detCFGToGotoTransform {P} [G : ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (loc : Nat := 0)
    (sourceText : Option String := none)
    : Except Format (GotoTransform P.TyEnv) := do
  -- First pass: emit instructions and build label→locationNum map
  let mut trans : GotoTransform P.TyEnv :=
    { instructions := #[], nextLoc := loc, T := T, sourceText := sourceText }
  -- Pending GOTO patches: (instruction array index, target label)
  let mut pendingPatches : List (Nat × String) := []
  let mut labelMap : List (String × Nat) := []
  for (label, block) in cfg.blocks do
    -- Record this block's entry location
    labelMap := (label, trans.nextLoc) :: labelMap
    -- Emit a LOCATION marker for the block
    -- TODO(source-locations): Once `DetTransferCmd` carries `MetaData`, extract
    -- a real `SourceLocation` here via `metadataToSourceLoc` (see
    -- `Stmt.toGotoInstructions` in ToCProverGOTO.lean for the pattern).
    -- Prerequisite: `StructuredToUnstructured.stmtsToBlocks` must propagate
    -- the `MetaData` from `ite`/`loop`/`block`/`exit` into the transfer
    -- commands it creates (currently discarded as `_md`).
    let srcLoc : SourceLocation := { SourceLocation.nil with function := functionName }
    trans := emitLabel label srcLoc trans
    -- Translate each command via the existing Cmd-to-GOTO mapping.
    -- NOTE: This only handles `Imperative.Cmd`. To support `Core.CmdExt.call`,
    -- either:
    --   (a) generalize this function over the command type and accept a
    --       command translator as a parameter, or
    --   (b) create a Core-specific wrapper (like `coreStmtsToGoto` in
    --       `CoreToGOTOPipeline.lean`) that pattern-matches on `CmdExt` and
    --       emits `FUNCTION_CALL` instructions for `.call`, delegating `.cmd`
    --       to `Cmd.toGotoInstructions`.
    for cmd in block.cmds do
      trans ← Cmd.toGotoInstructions trans.T functionName cmd trans
    -- Translate the transfer command
    match block.transfer with
    | .condGoto cond lt lf _md =>
      let cond_expr ← G.toGotoExpr cond
      -- Emit: GOTO [!cond] lf
      let (trans', falseIdx) := emitCondGoto (Expr.not cond_expr) srcLoc trans
      trans := trans'
      pendingPatches := (falseIdx, lf) :: pendingPatches
      -- Emit: GOTO lt (unconditional)
      let (trans', trueIdx) := emitUncondGoto srcLoc trans
      trans := trans'
      pendingPatches := (trueIdx, lt) :: pendingPatches
    | .finish _md =>
      -- No instruction needed; the caller appends END_FUNCTION
      pure ()
  -- Second pass: patch all GOTO targets
  let patches := pendingPatches.filterMap fun (idx, label) =>
    match labelMap.find? (fun (l, _) => l == label) with
    | some (_, loc) => some (idx, loc)
    | none => none
  return patchGotoTargets trans patches

end Imperative
