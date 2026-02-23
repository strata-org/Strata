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

abbrev DetBlocks (Label CmdT : Type) (P : PureExpr) := List (DetBlock Label CmdT P)

def detCmdBlock [HasBool P] (l : Label) (c : CmdT) (k : Label) :
  DetBlock Label CmdT P :=
  { label := l, cmds := [c], transfer := .goto k }

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
  -- TODO: this introduces a separate block for every command
  pure (l, [detCmdBlock l c k])
| .funcDecl _ _ => pure (k, []) -- TODO: not yet supported
| .block l bss  _md => do
  let (bl, bbs) ← stmtsToBlocks k bss
  -- TODO: this introduces another unnecessary block
  let b := { label := l, cmds := [], transfer := .goto bl }
  pure (l, b :: bbs)
| .ite c tss fss _md => do
  let l ← StringGenState.gen "ite"
  let (tl, tbs) ← stmtsToBlocks k tss
  let (fl, fbs) ← stmtsToBlocks k fss
  let b := { label := l, cmds := [], transfer := .cgoto c tl fl }
  pure (l, [b] ++ tbs ++ fbs)
| .loop c _m i? bss _md => do
  let lentry ← StringGenState.gen "loop_entry"
  let (bl, bbs) ← stmtsToBlocks lentry bss
  let cmds : List CmdT :=
    match i? with
    | .some i => [HasPassiveCmds.assert "inv" i MetaData.empty]
    | .none => []
  let b := { label := lentry, cmds := cmds, transfer := .cgoto c bl k }
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
  let bend := { label := lend, cmds := [], transfer := .finish }
  let (l, bs) ← stmtsToBlocks lend ss
  pure { entry := l, blocks := bs ++ [bend] }

def stmtsToCFG
  [HasBool P] [HasPassiveCmds P CmdT]
  (ss : List (Stmt P CmdT)) :
  CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst
