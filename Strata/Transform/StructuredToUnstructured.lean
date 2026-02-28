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

/-- Flush the list of accumulated commands. If the list is empty, propagate the
provided continuation. If the list is non-empty, create a block containing
one command that jumps to the provided continuation and provide the new block's
label as a new continuation.  -/
def flushCmds
  [HasBool P]
  (pfx : String)
  (accum : List CmdT)
  (tr? : Option (DetTransferCmd String P))
  (k : String) :
  StringGenM (String × DetBlocks String CmdT P) := do
  if accum.isEmpty then
    pure (k, [])
  else
    let l ← StringGenState.gen pfx
    let b := (l, { cmds := accum.reverse, transfer := tr?.getD (.goto k) })
    pure (l, [b])

/-- Translate a list of statements to basic blocks, accumulating commands -/
def stmtsToBlocks
  [HasBool P] [HasPassiveCmds P CmdT]
  (k : String)
  (ss : List (Stmt P CmdT))
  (exitConts : List (String × String))
  (accum : List CmdT) :
  StringGenM (String × DetBlocks String CmdT P) :=
match ss with
| [] =>
  -- Flush accumulated commands
  flushCmds "l$" accum .none k
| .cmd c :: rest =>
  -- Accumulate this command to be emitted at the next block end.
  stmtsToBlocks k rest exitConts (c :: accum)
| .funcDecl _ _ :: rest => do
  -- Not yet supported, so just continue with `rest`.
  stmtsToBlocks k rest exitConts accum
| .block l bss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Process block body, extending the list of exit continuations.
  let (bl, bbs) ← stmtsToBlocks kNext bss ((l, kNext) :: exitConts) []
  -- Flush accumulated commands
  let (accumEntry, accumBlocks) ← flushCmds "blk$" accum .none bl
  -- Create labeled block if needed
  if l == bl then
    -- Empty accumulated block
    pure (accumEntry, accumBlocks ++ bbs ++ bsNext)
  else
    let b := (l, { cmds := [], transfer := .goto bl })
    pure (l, accumBlocks ++ [b] ++ bbs ++ bsNext)
| .ite c tss fss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Create ite block
  let l ← StringGenState.gen "ite"
  let (tl, tbs) ← stmtsToBlocks kNext tss exitConts []
  let (fl, fbs) ← stmtsToBlocks kNext fss exitConts []
  -- Flush accumulated commands
  let (accumEntry, accumBlocks) ← flushCmds "ite$" accum (.some (.cgoto c tl fl)) l
  pure (accumEntry, accumBlocks ++ tbs ++ fbs ++ bsNext)
| .loop c _m is bss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Create loop entry block
  let lentry ← StringGenState.gen "loop_entry$"
  let (bl, bbs) ← stmtsToBlocks lentry bss exitConts []
  let cmds : List CmdT :=
    is.map (fun i => HasPassiveCmds.assert "inv" i MetaData.empty)
  let b := (lentry, { cmds := cmds, transfer := .cgoto c bl kNext })
  -- Flush accumulated commands
  let (accumEntry, accumBlocks) ← flushCmds "before_loop$" accum .none lentry
  pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ bsNext)
| .exit l? _md :: _ => do
  -- Find the continuation of the block labeled `l`, or the most recently-added
  -- block if `l` is `.none`.
  let bk :=
    match (l?, exitConts) with
    | (.none, []) => k -- Just keep going if this is an invalid exit
    | (.none, (_, k) :: _) => k
    | (.some l, _) =>
      match exitConts.lookup l with
      | .some k => k
      | .none => k -- Just keep going if this is an invalid exit
  -- Flush the accumulated commands, going to the continuation calculated above.
  -- Any statements after the `.exit` are skipped.
  let exitName := match l? with | .some l => s!"block${l}$" | .none => "block$"
  flushCmds exitName accum .none bk

def stmtsToCFGM
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  StringGenM (CFG String (DetBlock String CmdT P)) := do
  let lend ← StringGenState.gen "end$"
  let bend := (lend, { cmds := [], transfer := .finish })
  let (l, bs) ← stmtsToBlocks lend ss [] []
  pure { entry := l, blocks := bs ++ [bend] }

def stmtsToCFG
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst
