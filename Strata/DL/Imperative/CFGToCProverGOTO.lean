/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.ToCProverGOTO

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

- **`Core.CmdExt.call`**: This translation handles `Imperative.Cmd` only.
  Core procedure calls (`CmdExt.call`) are handled by the Core-specific
  wrapper `coreCFGToGotoTransform` in `CoreCFGToGOTOPipeline.lean`.
-/

namespace Imperative

open CProverGOTO
open Std (Format format)

/-- Translate a deterministic CFG to CProverGOTO instructions.

    The translation processes blocks in the order they appear in `cfg.blocks`.
    The entry block must appear first; the function returns an error otherwise.
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
  let mut labelMap : Std.HashMap String Nat := {}
  -- Loop contract metadata: maps loop entry labels to their contract metadata.
  -- Used in the second pass to annotate backward-edge GOTOs.
  let mut loopContracts : Std.HashMap String (MetaData P) := {}
  for (label, block) in cfg.blocks do
    -- Record this block's entry location
    labelMap := labelMap.insert label trans.nextLoc
    let srcLoc : SourceLocation := { SourceLocation.nil with function := functionName }
    trans := emitLabel label srcLoc trans
    -- Translate each command via the existing Cmd-to-GOTO mapping.
    for cmd in block.cmds do
      trans ← Cmd.toGotoInstructions trans.T functionName cmd trans
    -- Translate the transfer command
    match block.transfer with
    | .condGoto cond lt lf md =>
      let transferSrcLoc := metadataToSourceLoc md functionName trans.sourceText
      let cond_expr ← G.toGotoExpr cond
      -- Record loop contracts if present (invariants and/or decreases on this
      -- transfer indicate a loop entry block).
      let hasLoopContract := md.any fun elem =>
        elem.fld == MetaData.specLoopInvariant || elem.fld == MetaData.specDecreases
      if hasLoopContract then
        loopContracts := loopContracts.insert label md
      -- Emit: GOTO [!cond] lf
      let (trans', falseIdx) := emitCondGoto (Expr.not cond_expr) transferSrcLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (falseIdx, lf)
      -- Emit: GOTO lt (unconditional)
      let (trans', trueIdx) := emitUncondGoto transferSrcLoc trans
      trans := trans'
      pendingPatches := pendingPatches.push (trueIdx, lt)
    | .finish _md =>
      -- No instruction needed; the caller appends END_FUNCTION
      pure ()
    | .exitTo _lbl _md =>
      -- An uncaught structured exit. Faithful GOTO lowering of an escaping
      -- exit is deferred; for now emit no instruction (the caller appends
      -- END_FUNCTION), keeping this backend total.
      pure ()
  -- Second pass: resolve all pending labels and annotate backward-edge GOTOs
  -- with loop contracts when the target is a loop entry block.
  let mut resolvedPatches : List (Nat × Nat) := []
  for (idx, label) in pendingPatches do
    match labelMap[label]? with
    | some targetLoc =>
      resolvedPatches := (idx, targetLoc) :: resolvedPatches
      -- If this GOTO targets a loop entry with contracts, annotate its guard.
      if let some md := loopContracts[label]? then
        let instLoc := trans.instructions[idx]!.locationNum
        -- Only annotate backward edges (target location <= source location).
        if targetLoc ≤ instLoc then
          let mut guard := trans.instructions[idx]!.guard
          for elem in md do
            if elem.fld == MetaData.specLoopInvariant then
              if let .expr e := elem.value then
                let gotoExpr ← G.toGotoExpr e
                guard := guard.setNamedField "#spec_loop_invariant" gotoExpr
            if elem.fld == MetaData.specDecreases then
              if let .expr e := elem.value then
                let gotoExpr ← G.toGotoExpr e
                guard := guard.setNamedField "#spec_decreases" gotoExpr
          trans := { trans with
            instructions := trans.instructions.set! idx
              { trans.instructions[idx]! with guard := guard } }
    | none =>
      throw f!"[detCFGToGotoTransform] Unresolved label '{label}' referenced \
               by GOTO at instruction index {idx}."
  return patchGotoTargets trans resolvedPatches

end Imperative
