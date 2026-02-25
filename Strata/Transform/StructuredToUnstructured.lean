/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.PureExpr
import Strata.DL.Imperative.BasicBlock
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LExpr
import Strata.DL.Util.LabelGen

namespace Imperative

abbrev DetBlocks (Label CmdT : Type) (P : PureExpr) := List (Label × DetBlock Label CmdT P)

def detCmdBlock [HasBool P] (c : CmdT) (k : Label) :
  DetBlock Label CmdT P :=
  { cmds := [c], transfer := .goto k }

/-- Coalesce contiguous blocks that have unconditional gotos to each other.
This merges chains of blocks like:
  l1: [cmd1] goto l2
  l2: [cmd2] goto l3
  l3: [cmd3] goto l4
into:
  l1: [cmd1, cmd2, cmd3] goto l4

Only coalesces forward chains - stops at blocks that are:
- Targets of conditional branches
- Targets of multiple gotos (potential loop headers or join points)
-/
def coalesceBlocks [BEq Label] [Hashable Label] [HasBool P]
  (blocks : List (Label × DetBlock Label CmdT P)) :
  List (Label × DetBlock Label CmdT P) :=
  -- Build a map from labels to blocks for quick lookup
  let blockMap := Std.HashMap.ofList blocks

  let incrementLabel (m : Std.HashMap Label Nat) (l : Label) : Std.HashMap Label Nat :=
    m.insert l ((m.getD l 0) + 1)

  -- Count how many blocks jump to each label
  let incomingCount : Std.HashMap Label Nat :=
    blocks.foldl (fun acc (_, block) =>
      match block.transfer with
      | .cgoto _ lt lf _ =>
        let acc' := incrementLabel acc lt
        if lt == lf then acc' else incrementLabel acc' lf
      | _ => acc
    ) {}

  -- Identify blocks that are targets of conditional branches
  let conditionalTargets : Std.HashSet Label :=
    blocks.foldl (fun acc (_, block) =>
      match block.transfer with
      | .cgoto _ lt lf _ =>
        if lt != lf then acc.insert lt |>.insert lf else acc
      | _ => acc
    ) {}

  -- Helper: follow a chain of unconditional gotos and collect commands
  -- Stop at blocks that have multiple incoming edges or are conditional targets
  let rec followChain (fuel : Nat) (visited : Std.HashSet Label) (l : Label) : List CmdT × DetTransferCmd Label P :=
    match fuel with
    | 0 => ([], .goto l)  -- Out of fuel, stop here
    | fuel' + 1 =>
      if visited.contains l then
        -- Cycle detected, stop here
        ([], .goto l)
      else
        -- Stop if this block has multiple incoming edges (potential loop header/join point)
        if (incomingCount.getD l 0) > 1 then
          ([], .goto l)
        -- Stop if this block is a conditional target
        else if conditionalTargets.contains l then
          ([], .goto l)
        else
          match blockMap[l]? with
          | none => ([], .goto l)  -- Label not found, keep the goto
          | some blk =>
            match blk.transfer with
            | .cgoto _ lt lf _ =>
              -- Check if it's an unconditional goto (both branches go to same place)
              if lt == lf then
                -- Unconditional goto - can potentially merge
                let (moreCmds, finalTransfer) := followChain fuel' (visited.insert l) lt
                (blk.cmds ++ moreCmds, finalTransfer)
              else
                -- Conditional branch - stop here
                (blk.cmds, blk.transfer)
            | .finish _ => (blk.cmds, blk.transfer)

  -- Collect all labels that are targets of unconditional gotos (candidates for merging)
  let gotoTargets : Std.HashSet Label :=
    blocks.foldl (fun acc (_, block) =>
      match block.transfer with
      | .cgoto _ lt lf _ =>
        if lt == lf then acc.insert lt else acc
      | _ => acc
    ) {}

  -- Use the number of blocks as fuel (upper bound on chain length)
  let fuel := blocks.length

  -- Process each block
  blocks.filterMap fun (label, block) =>
    -- Skip blocks that:
    -- 1. Are only reachable via a single unconditional goto, AND
    -- 2. Are not conditional targets, AND
    -- 3. Don't have multiple incoming edges
    let isGotoTarget := gotoTargets.contains label
    let hasMultipleIncoming := (incomingCount.getD label 0) > 1
    let isConditionalTarget := conditionalTargets.contains label

    if isGotoTarget && !isConditionalTarget && !hasMultipleIncoming then
      none  -- This block will be merged into its predecessor
    else
      match block.transfer with
      | .cgoto _ lt lf _ =>
        if lt == lf then
          -- Unconditional goto - try to coalesce with following blocks
          let (allCmds, finalTransfer) := followChain fuel (Std.HashSet.ofList [label]) lt
          some (label, { cmds := block.cmds ++ allCmds, transfer := finalTransfer })
        else
          -- Conditional branch - keep as-is
          some (label, block)
      | _ =>
        -- Keep blocks with finish as-is
        some (label, block)

open LabelGen

mutual

/-- Translate a structured statement to an unstructured list of basic blocks
along with an entry label. -/
def stmtToBlocks
  [HasBool P] [HasPassiveCmds P CmdT]
  (k : String) (s : Stmt P CmdT) :
  StringGenM (String × DetBlocks String CmdT P) :=
match s with
| .cmd c => do
  let l ← StringGenState.gen "l"
  /- Note: this introduces a separate block for every command, so we need to
  coalesce later. -/
  pure (l, [(l, detCmdBlock c k)])
| .funcDecl _ _ => pure (k, []) -- TODO: not yet supported
| .block l bss  _md => do
  let (bl, bbs) ← stmtsToBlocks k bss
  -- Note: this introduces another unnecessary block.
  let b := (l, { cmds := [], transfer := .goto bl })
  pure (l, b :: bbs)
| .ite c tss fss _md => do
  let l ← StringGenState.gen "ite"
  let (tl, tbs) ← stmtsToBlocks k tss
  let (fl, fbs) ← stmtsToBlocks k fss
  let b := (l, { cmds := [], transfer := .cgoto c tl fl })
  pure (l, [b] ++ tbs ++ fbs)
| .loop c _m i? bss _md => do
  let lentry ← StringGenState.gen "loop_entry"
  /- The body is translated with continuation `lentry`, so the last statement
  jumps back to the loop entry, forming the back-edge to the entry block created
  below. -/
  let (bl, bbs) ← stmtsToBlocks lentry bss
  let cmds : List CmdT :=
    match i? with
    | .some i => [HasPassiveCmds.assert "inv" i MetaData.empty]
    | .none => []
  let b := (lentry, { cmds := cmds, transfer := .cgoto c bl k })
  pure (lentry, [b] ++ bbs)
| .goto l _md => pure (l, [])

def stmtsToBlocks
  [HasBool P] [HasPassiveCmds P CmdT]
  (k : String) (ss : List (Stmt P CmdT)) :
  StringGenM (String × DetBlocks String CmdT P) :=
match ss with
| [] => pure (k, [])
| s :: ss => do
  let (l, bs) ← stmtsToBlocks k ss
  let (l', bs') ← stmtToBlocks l s
  pure (l', bs' ++ bs)

end

def stmtsToCFGM
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  StringGenM (CFG String (DetBlock String CmdT P)) := do
  let lend ← StringGenState.gen "end"
  let bend := (lend, { cmds := [], transfer := .finish })
  let (l, bs) ← stmtsToBlocks lend ss
  let allBlocks := bs ++ [bend]
  -- Coalesce contiguous blocks with unconditional gotos
  let coalescedBlocks := coalesceBlocks allBlocks
  pure { entry := l, blocks := coalescedBlocks }

def stmtsToCFG
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst
