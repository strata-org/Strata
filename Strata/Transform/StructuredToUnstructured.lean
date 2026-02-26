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

open LabelGen

/-- Helper to flush accumulated commands as a block if non-empty -/
def flushAccum
  [HasBool P]
  (accum : List CmdT) (k : String) :
  StringGenM (String × DetBlocks String CmdT P) := do
  if accum.isEmpty then
    pure (k, [])
  else
    let l ← StringGenState.gen "l"
    let b := (l, { cmds := accum.reverse, transfer := .goto k })
    pure (l, [b])

/-- Translate a list of statements to basic blocks, accumulating commands -/
partial def stmtsToBlocks
  [HasBool P] [HasPassiveCmds P CmdT]
  (k : String) (ss : List (Stmt P CmdT)) (accum : List CmdT) :
  StringGenM (String × DetBlocks String CmdT P) :=
match ss with
| [] =>
  -- Flush any remaining accumulated commands
  flushAccum accum k
| .cmd c :: ss =>
  -- Accumulate the command and continue
  stmtsToBlocks k ss (c :: accum)
| .funcDecl _ _ :: ss => do
  -- Flush accumulator and continue
  let (_, bs1) ← flushAccum accum k
  let (l2, bs2) ← stmtsToBlocks k ss []
  pure (l2, bs1 ++ bs2)
| .block l bss _md :: ss => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k ss []
  -- Process block body
  let (bl, bbs) ← stmtsToBlocks kNext bss []
  -- Flush accumulator
  let (accumEntry, accumBlocks) ← flushAccum accum bl
  -- Create labeled block if needed
  if l == bl then
    pure (accumEntry, accumBlocks ++ bbs ++ bsNext)
  else
    let b := (l, { cmds := [], transfer := .goto bl })
    pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ bsNext)
| .ite c tss fss _md :: ss => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k ss []
  -- Create ite block
  let l ← StringGenState.gen "ite"
  let (tl, tbs) ← stmtsToBlocks kNext tss []
  let (fl, fbs) ← stmtsToBlocks kNext fss []
  let b := (l, { cmds := [], transfer := .cgoto c tl fl })
  -- Flush accumulator
  let (accumEntry, accumBlocks) ← flushAccum accum l
  pure (accumEntry, accumBlocks ++ [b] ++ tbs ++ fbs ++ bsNext)
| .loop c _m is bss _md :: ss => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k ss []
  -- Create loop entry block
  let lentry ← StringGenState.gen "loop_entry"
  let (bl, bbs) ← stmtsToBlocks lentry bss []
  let cmds : List CmdT :=
    is.map (fun i => HasPassiveCmds.assert "inv" i MetaData.empty)
  let b := (lentry, { cmds := cmds, transfer := .cgoto c bl kNext })
  -- Flush accumulator
  let (accumEntry, accumBlocks) ← flushAccum accum lentry
  pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ bsNext)
| .exit l _md :: ss => do
  -- Flush accumulator and continue
  -- TODO: support this correctly
  let (_, bs1) ← flushAccum accum k
  let (l2, bs2) ← stmtsToBlocks k ss []
  pure (l2, bs1 ++ bs2)

def stmtsToCFGM
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  StringGenM (CFG String (DetBlock String CmdT P)) := do
  let lend ← StringGenState.gen "end"
  let bend := (lend, { cmds := [], transfer := .finish })
  let (l, bs) ← stmtsToBlocks lend ss []
  pure { entry := l, blocks := bs ++ [bend] }

def stmtsToCFG
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst
