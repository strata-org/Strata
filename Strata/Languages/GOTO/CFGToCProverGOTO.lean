/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.Languages.GOTO.ToCProverGOTO

public section

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

- **Source locations on control flow**: each jump carries the location of
  its `DetTransferCmd`'s `MetaData`, but `StructuredToUnstructured.stmtsToBlocks`
  currently passes `MetaData.empty` when constructing transfer commands (the
  metadata from `ite`/`loop`/`block`/`exit` statements is discarded as `_md`).
  Once `stmtsToBlocks` propagates the metadata, this module picks it up.
- **Loop contracts**: The direct path emits `#spec_loop_invariant` and
  `#spec_decreases` as named sub-expressions on the backward-edge GOTO
  instruction (recognized by CBMC's DFCC). In the CFG, invariants are lowered
  to plain `assert` commands and measures are discarded entirely.
  To fix: `StructuredToUnstructured.stmtsToBlocks` (the `.loop` case) would
  need to preserve invariants and measures in the `DetTransferCmd` (or in a
  side channel), and this module would need to emit them as named
  sub-expressions on the backward-edge GOTO, mirroring the logic in the
  `.loop` case of `Stmt.toGotoInstructions` in `ToCProverGOTO.lean`.
- **`Imperative.CmdExt.call`**: `detCFGToGotoTransform` handles
  `Imperative.Cmd` only. `detCFGToGotoTransformWith` takes a command
  translator, so a caller with its own command type (for instance one with
  calls, which `emitFunctionCall` translates) uses that instead.
-/

namespace Imperative

open CProverGOTO
open Std (Format format)

/-- Translate a deterministic CFG whose blocks hold commands of type `C` to
    CProverGOTO instructions, translating each command with `cmdToGoto`.

    The translation processes blocks in the order they appear in `cfg.blocks`.
    The entry block must appear first; the function returns an error otherwise.
    For each block:
    1. Record the current location number as the block's entry point
    2. Translate each command with `cmdToGoto`
    3. Translate the transfer command, located at the transfer's metadata:
       - `condGoto c lt lf` → GOTO [!c] lf; GOTO lt (conditional + fallthrough)
       - `finish` → with `finishJumpsToEnd`, GOTO to the location after the
         last block, where the caller emits the function's exit; otherwise no
         instruction (the caller appends END_FUNCTION)

    After all blocks are emitted, a second pass patches GOTO targets using the
    label-to-location map built during the first pass.
-/
def detCFGToGotoTransformWith {P} {C : Type} [G : ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String)
    (cmdToGoto : C → GotoTransform P.TyEnv → Except Format (GotoTransform P.TyEnv))
    (cfg : CFG String (DetBlock String C P))
    (loc : Nat := 0)
    (sourceText : Option String := none)
    (finishJumpsToEnd : Bool := false)
    : Except Format (GotoTransform P.TyEnv) := do
  -- Verify the entry block is listed first so that GOTO execution starts at
  -- the right location. The caller (e.g., CoreToGOTOPipeline) relies on the
  -- first instruction being the entry point.
  match cfg.blocks with
  | (firstLabel, _) :: _ =>
    if firstLabel != cfg.entry then
      throw f!"[detCFGToGotoTransform] Entry label '{cfg.entry}' does not match \
               first block label '{firstLabel}'. The entry block must be listed first."
  | [] => pure ()
  -- First pass: emit instructions and build label→locationNum map
  let mut trans : GotoTransform P.TyEnv :=
    { instructions := #[], nextLoc := loc, T := T, sourceText := sourceText }
  -- Pending GOTO patches: (instruction array index, target label)
  let mut pendingPatches : Array (Nat × String) := #[]
  -- GOTOs of `finish` transfers, patched to the location after the last block
  let mut finishPatches : Array Nat := #[]
  let mut labelMap : Std.HashMap String Nat := {}
  for (label, block) in cfg.blocks do
    -- Record this block's entry location
    labelMap := labelMap.insert label trans.nextLoc
    -- Emit a LOCATION marker for the block
    let srcLoc : SourceLocation := { SourceLocation.nil with function := functionName }
    trans := emitLabel label srcLoc trans
    for cmd in block.cmds do
      trans ← cmdToGoto cmd trans
    -- Translate the transfer command
    match block.transfer with
    | .condGoto cond lt lf md =>
      let jumpLoc := metadataToSourceLoc md functionName trans.sourceText
      let cond_expr ← G.toGotoExpr cond
      -- Emit: GOTO [!cond] lf
      let (trans', falseIdx) := emitCondGoto (Expr.not cond_expr) jumpLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (falseIdx, lf)
      -- Emit: GOTO lt (unconditional)
      let (trans', trueIdx) := emitUncondGoto jumpLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (trueIdx, lt)
    | .finish md =>
      if finishJumpsToEnd then
        let jumpLoc := metadataToSourceLoc md functionName trans.sourceText
        let (trans', idx) := emitUncondGoto jumpLoc trans
        trans := trans'
        finishPatches := finishPatches.push idx
  -- Second pass: resolve all pending labels, then patch in one call
  let mut resolvedPatches : List (Nat × Nat) := finishPatches.toList.map (·, trans.nextLoc)
  for (idx, label) in pendingPatches do
    match labelMap[label]? with
    | some targetLoc => resolvedPatches := (idx, targetLoc) :: resolvedPatches
    | none =>
      throw f!"[detCFGToGotoTransform] Unresolved label '{label}' referenced \
               by GOTO at instruction index {idx}."
  return patchGotoTargets trans resolvedPatches

/-- Translate a deterministic CFG of `Imperative.Cmd`s to CProverGOTO
    instructions with `Cmd.toGotoInstructions`, as `detCFGToGotoTransformWith`
    does; a `finish` emits no instruction. -/
def detCFGToGotoTransform {P} [G : ToGoto P] [BEq P.Ident]
    (T : P.TyEnv) (functionName : String)
    (cfg : CFG String (DetBlock String (Cmd P) P))
    (loc : Nat := 0)
    (sourceText : Option String := none)
    : Except Format (GotoTransform P.TyEnv) :=
  detCFGToGotoTransformWith T functionName
    (fun cmd trans => Cmd.toGotoInstructions trans.T functionName cmd trans)
    cfg loc sourceText

end Imperative
