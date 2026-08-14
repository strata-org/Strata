/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Imperative.PureExpr
public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.CFGSemantics
import Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
import Strata.DL.Lambda.LExpr
public import Strata.DL.Util.LabelGen

public section

namespace Imperative

abbrev DetBlocks (Label CmdT : Type) (P : PureExpr) := List (Label × DetBlock Label CmdT P)

def detCmdBlock [HasBool P] (c : CmdT) (k : Label) :
  DetBlock Label CmdT P :=
  { cmds := [c], transfer := .goto k }

open LabelGen

/-! ## Fresh-label prefixes

Every block label this pass generates carries one of the prefixes below, so its
origin is recognizable. Naming them once here (rather than repeating the literals
at each `StringGenState.gen`/`flushCmds` site) keeps the pass and its correctness
proof referring to the same strings by name. The `$__nondet_*` prefixes name the
fresh boolean guard variables this pass introduces for nondeterministic `.ite`
conditions and `.loop` guards; they are distinct from `NondetElim`'s own
`$__ndelim_*` prefixes. -/

/-- Fresh-label prefix for the `.ite` construct's conditional-branch block. -/
def iteLabelPrefix : String := "ite"

/-- Fresh-label prefix for the block flushing the accumulated commands that
precede an `.ite`. -/
def iteFlushPrefix : String := "ite$"

/-- Fresh-label prefix for a loop's entry block. -/
def loopEntryPrefix : String := "loop_entry$"

/-- Fresh-name prefix for the variable snapshotting a loop's measure on entry. -/
def loopMeasurePrefix : String := "loop_measure$"

/-- Fresh-label prefix for the block asserting a loop's measure strictly
decreases. -/
def measureDecreasePrefix : String := "measure_decrease$"

/-- Fresh-label prefix for a synthesized loop-invariant assertion (used only when
the source supplies no label). -/
def invariantPrefix : String := "inv$"

/-- Fresh-label prefix for the CFG's terminal block. -/
def endPrefix : String := "end$"

/-- Fresh-label prefix for the block flushing a statement list's trailing
accumulated commands. -/
def listTailPrefix : String := "l$"

/-- Fresh-label prefix for the block flushing the accumulated commands that
precede a `.block`. -/
def blockFlushPrefix : String := "blk$"

/-- Fresh-label prefix for the block flushing the accumulated commands that
precede a loop. -/
def beforeLoopPrefix : String := "before_loop$"

/-- Fresh-label prefix for the block flushing an `.exit`'s accumulated commands,
parameterized by the source block label `l` being exited. -/
def blockExitPrefix (l : String) : String := s!"block${l}$"

/-- Fresh-name prefix for the boolean guard variable introduced for a
nondeterministic `.ite` condition. -/
def nondetItePrefix : String := "$__nondet_ite$"

/-- Fresh-name prefix for the boolean guard variable introduced for a
nondeterministic `.loop` guard. -/
def nondetLoopPrefix : String := "$__nondet_loop$"

/-- Flush the list of accumulated commands. If both the accumulator is empty
and no explicit transfer is provided, propagate the continuation `k`.
Otherwise emit a block: when `tr?` is `some tr`, use `tr` as the transfer
(this is required for `condGoto` so the conditional is materialized even
with empty accum); when `tr?` is `none`, use `.goto k`. -/
def flushCmds
  [HasBool P]
  (pfx : String)
  (accum : List CmdT)
  (tr? : Option (DetTransferCmd String P))
  (k : String) :
  StringGenM (String × DetBlocks String CmdT P) := do
  match tr? with
  | none =>
    if accum.isEmpty then
      pure (k, [])
    else
      let l ← StringGenState.gen pfx
      let b := (l, { cmds := accum.reverse, transfer := .goto k })
      pure (l, [b])
  | some tr =>
    let l ← StringGenState.gen pfx
    let b := (l, { cmds := accum.reverse, transfer := tr })
    pure (l, [b])

private abbrev synthesizedMd {P : PureExpr} : MetaData P :=
  MetaData.ofProvenance (.synthesized .structuredToUnstructured)

/-- Translate a list of statements to basic blocks, accumulating commands -/
def stmtsToBlocks
  [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
  [HasIdent P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasBoolOps P]
  (k : String)
  (ss : List (Stmt P CmdT))
  (exitConts : List (Option String × String))
  (accum : List CmdT) :
  StringGenM (String × DetBlocks String CmdT P) :=
match ss with
| [] =>
  -- Flush accumulated commands
  flushCmds listTailPrefix accum .none k
| .cmd c :: rest =>
  -- Accumulate this command to be emitted at the next block end.
  stmtsToBlocks k rest exitConts (c :: accum)
| .funcDecl _ _ :: rest => do
  -- Not yet supported, so just continue with `rest`.
  stmtsToBlocks k rest exitConts accum
| .typeDecl _ _ :: rest => do
  -- Not yet supported, so just continue with `rest`.
  stmtsToBlocks k rest exitConts accum
| .block l bss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Process block body, extending the list of exit continuations.
  let (bl, bbs) ← stmtsToBlocks kNext bss ((.some l, kNext) :: exitConts) []
  -- Flush accumulated commands
  let (accumEntry, accumBlocks) ← flushCmds blockFlushPrefix accum .none bl
  -- Create labeled block if needed
  if l == bl then
    -- Empty accumulated block
    pure (accumEntry, accumBlocks ++ bbs ++ bsNext)
  else
    let b := (l, { cmds := [], transfer := .goto bl })
    pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ bsNext)
| .ite c tss fss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Create ite block
  let l ← StringGenState.gen iteLabelPrefix
  let (tl, tbs) ← stmtsToBlocks kNext tss exitConts []
  let (fl, fbs) ← stmtsToBlocks kNext fss exitConts []
  -- For nondet conditions, introduce a fresh boolean variable
  let (condExpr, extraCmds) ← match c with
    | .det e => pure (e, [])
    | .nondet => do
      let freshName ← StringGenState.gen nondetItePrefix
      let ident := HasIdent.ident (P := P) freshName
      let initCmd := HasInit.init ident HasBool.boolTy .nondet synthesizedMd
      pure (HasFvar.mkFvar ident, [initCmd])
  let (accumEntry, accumBlocks) ← flushCmds iteFlushPrefix (accum ++ extraCmds)
    (.some (.condGoto condExpr tl fl .empty)) l
  pure (accumEntry, accumBlocks ++ tbs ++ fbs ++ bsNext)
| .loop c m is bss _md :: rest => do
  -- Process rest first
  let (kNext, bsNext) ← stmtsToBlocks k rest exitConts []
  -- Create loop entry block
  let lentry ← StringGenState.gen loopEntryPrefix
  -- Handle measure: generate entry-block commands and a decrease-assert block
  -- that the body jumps through before looping back.
  let (measureCmds, bodyK, decreaseBlocks) ←
    match m with
    | none => pure ([], lentry, [])
    | some mExpr => do
      let mLabel ← StringGenState.gen loopMeasurePrefix
      let mIdent := HasIdent.ident mLabel
      let mOldExpr := HasFvar.mkFvar mIdent
      let initCmd  := HasInit.init mIdent HasInt.intTy .nondet synthesizedMd
      let assumeCmd := HasPassiveCmds.assume s!"assume_{mLabel}"
                         (HasIntOps.eq mOldExpr mExpr) synthesizedMd
      let lbCmd    := HasPassiveCmds.assert s!"measure_lb_{mLabel}"
                         (HasBoolOps.not (HasIntOps.lt mOldExpr HasInt.zero)) synthesizedMd
      let decCmd   := HasPassiveCmds.assert s!"measure_decrease_{mLabel}"
                         (HasIntOps.lt mExpr mOldExpr) synthesizedMd
      let ldec ← StringGenState.gen measureDecreasePrefix
      let decBlock := (ldec, { cmds := [decCmd], transfer := .goto lentry })
      pure ([initCmd, assumeCmd, lbCmd], ldec, [decBlock])
  -- Body jumps to bodyK (either directly to lentry, or through the decrease block).
  let (bl, bbs) ← stmtsToBlocks bodyK bss ((.none, kNext) :: exitConts) []
  -- For each invariant, emit an `assert` whose label preserves the source
  -- label when present.  When the source label is empty (frontend did not
  -- supply one), generate a fresh `inv$` label for uniqueness.
  let invCmds : List CmdT ←
    is.mapM (fun (srcLabel, i) => do
      let assertLabel ←
        if srcLabel.isEmpty then StringGenState.gen invariantPrefix
        else pure srcLabel
      pure (HasPassiveCmds.assert assertLabel i synthesizedMd))
  -- For nondet guards, introduce a fresh boolean variable
  match c with
  | .det e =>
    let b := (lentry, { cmds := invCmds ++ measureCmds, transfer := .condGoto e bl kNext .empty })
    let (accumEntry, accumBlocks) ← flushCmds beforeLoopPrefix accum .none lentry
    pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ decreaseBlocks ++ bsNext)
  | .nondet => do
    let freshName ← StringGenState.gen nondetLoopPrefix
    let ident := HasIdent.ident (P := P) freshName
    let initCmd := HasInit.init ident HasBool.boolTy .nondet synthesizedMd
    let b := (lentry, { cmds := [initCmd] ++ invCmds ++ measureCmds,
                        transfer := .condGoto (HasFvar.mkFvar ident) bl kNext .empty })
    let (accumEntry, accumBlocks) ← flushCmds beforeLoopPrefix accum .none lentry
    pure (accumEntry, accumBlocks ++ [b] ++ bbs ++ decreaseBlocks ++ bsNext)
| .exit l _md :: _ => do
  -- Find the continuation of the block labeled `l`.
  let bk :=
    match exitConts.lookup (.some l) with
    | .some k => k
    -- Just keep going if this is an invalid exit. We assume a prior
    -- check to avoid this.
    | .none => k
  -- Flush the accumulated commands, going to the continuation calculated above.
  -- Any statements after the `.exit` are skipped.
  let exitName := blockExitPrefix l
  flushCmds exitName accum .none bk

def stmtsToCFGM
  [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
  [HasIdent P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasBoolOps P]
  (ss : List (Stmt P CmdT)) :
  StringGenM (CFG String (DetBlock String CmdT P)) := do
  let lend ← StringGenState.gen endPrefix
  let bend := (lend, { cmds := [], transfer := .finish .empty })
  let (l, bs) ← stmtsToBlocks lend ss [] []
  pure { entry := l, blocks := bs ++ [bend] }

def stmtsToCFG
  [HasBool P] [HasPassiveCmds P CmdT] [HasInit P CmdT]
  [HasIdent P] [HasFvar P] [HasFvars P] [HasInt P] [HasIntOps P] [HasBoolOps P]
  (ss : List (Stmt P CmdT)) :
  CFG String (DetBlock String CmdT P) :=
  (stmtsToCFGM ss StringGenState.emp).fst
