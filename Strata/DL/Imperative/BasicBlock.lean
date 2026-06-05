/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData

public section

namespace Imperative

/-! # Imperative dialect: unstructured control-flow graphs

A control-flow graph consists of a list of labeled blocks paired with a
distinguished entry label. Each basic block consists of a list of normal
commands and a transfer command. The types of each of these components are
parameters, and the type of control flow can be deterministic or
non-deterministic based on the type of transfer command.

Note: basic block labels could just be `String`, like they are for `Stmt`.
However, when processing CFGs later, it'll be helpful to be able to create total
functions over labels, in which case it'll be nice to have `Label` be `Fin n`,
where `n` is the total number of blocks in the graph.
-/


/-- A `DetTransfer` command terminates a deterministic basic block, indicating
where execution should proceed next, if anywhere. -/
inductive DetTransferCmd (Label : Type) (P : PureExpr) where
  /-- Transfer to `lt` if `p` is true, or `lf` is `p` is false. -/
  | condGoto (p : P.Expr) (lt lf : Label) (md : MetaData P)
  /-- Stop execution of the current unstructured program. If in a procedure
  body, this can be interpreted as returning to the caller. -/
  | finish (md : MetaData P)

/-- For the moment, we don't have an unconditional jump in the language, and
model it instead using `condGoto`. By defining this function, we can easily
create unconditional jumps, and future proof against the possibility of adding
it as a constructor in the future.  -/
def DetTransferCmd.goto [HasBool P] (l : Label) (md : MetaData P) : DetTransferCmd Label P :=
  condGoto HasBool.tt l l md

/-- A `NondetTransfer` command terminates a non-deterministic basic block,
indicating the list of possible blocks where execution could proceed next, if
anywhere. -/
inductive NondetTransferCmd (Label : Type) (P : PureExpr) where
  /-- Transfer to any one of a list of labels, non-deterministically. `goto`
  with no labels is equivalent to `finish` in `DetTransferCmd` -/
  | goto (ls : List Label) (md : MetaData P)
  deriving Inhabited

def NondetTransferCmd.targets : NondetTransferCmd Label P → List Label
| .goto ls _ => ls

/-- A basic block consists of a list of body commands, and a transfer
command that indicates where to go next. It can be deterministic or
non-deterministic depending on the type of transfer command. -/
structure BasicBlock (TransferCmd Cmd : Type) where
  cmds : List Cmd
  transfer : TransferCmd

/-- A deterministic basic block is a basic block parameterized by deterministic
commands. -/
@[expose] def DetBlock (Label Cmd : Type) (P : PureExpr) :=
  BasicBlock (DetTransferCmd Label P) Cmd

/-- A non-deterministic basic block is a basic block parameterized by
non-deterministic commands. -/
@[expose] def NondetBlock (Label Cmd : Type) (P : PureExpr) :=
  BasicBlock (NondetTransferCmd Label P) Cmd

/-- A control flow graph is a list of blocks paired with a label indicating
where execution should start. -/
structure CFG (Label Block : Type) where
  entry : Label
  blocks : List (Label × Block)

--------

/-- Strip metadata from a deterministic transfer command. -/
def DetTransferCmd.stripMetaData : DetTransferCmd Label P → DetTransferCmd Label P
  | .condGoto p lt lf _ => .condGoto p lt lf .empty
  | .finish _ => .finish .empty

/-- Strip metadata from a non-deterministic transfer command. -/
def NondetTransferCmd.stripMetaData : NondetTransferCmd Label P → NondetTransferCmd Label P
  | .goto ls _ => .goto ls .empty

/-- Strip transfer metadata from a deterministic basic block. -/
def DetBlock.stripMetaData (blk : DetBlock Label Cmd P) : DetBlock Label Cmd P :=
  { blk with transfer := blk.transfer.stripMetaData }

/-- Strip transfer metadata from all blocks in a deterministic CFG. -/
def CFG.stripDetMetaData (cfg : CFG Label (DetBlock Label Cmd P)) :
    CFG Label (DetBlock Label Cmd P) :=
  { cfg with blocks := cfg.blocks.map fun (lbl, blk) => (lbl, blk.stripMetaData) }

--------

open Std (ToFormat Format format)

def formatDetTransferCmd (P : PureExpr) (c : DetTransferCmd Label P)
  [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .condGoto c lt lf md => f!"{md}condGoto {c} {lt} {lf}"
  | .finish md => f!"{md}finish"

def formatNondetTransferCmd (P : PureExpr) (c : NondetTransferCmd Label P)
  [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .goto ls md => f!"{md}goto {ls}"

def formatBasicBlock (b : BasicBlock TransferCmd TCmd)
  [ToFormat TransferCmd] [ToFormat TCmd] : Format :=
  let joined := Format.join (b.cmds.map (fun c => f!"  {c}{Format.line}"))
  f!"{joined}  {b.transfer}"

def formatCFG (cfg : CFG Label Blk)
  [ToFormat Label] [ToFormat Blk] : Format :=
  match cfg.blocks with
  | [] => f!"Entry: {cfg.entry}{Format.line}{Format.line}[]"
  | blocks =>
    let blocksFormatted := blocks.map fun (lbl, blk) =>
      f!"{lbl}:{Format.line}{format blk}"
    let joined := Format.joinSep blocksFormatted Format.line
    f!"Entry: {cfg.entry}{Format.line}{Format.line}{joined}"

instance [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
    : ToFormat (DetTransferCmd Label P) where
  format c := formatDetTransferCmd P c

instance [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
    : ToFormat (NondetTransferCmd Label P) where
  format c := formatNondetTransferCmd P c

instance [ToFormat TransferCmd] [ToFormat TCmd]
    : ToFormat (BasicBlock TransferCmd TCmd) where
  format b := formatBasicBlock b

instance [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat Label] [ToFormat TCmd]
    : ToFormat (DetBlock Label TCmd P) where
  format b := formatBasicBlock b

instance [ToFormat P.Expr] [ToFormat P.Ident] [ToFormat P.Ty] [ToFormat Label] [ToFormat TCmd]
    : ToFormat (NondetBlock Label TCmd P) where
  format b := formatBasicBlock b

instance [ToFormat Label] [ToFormat Blk]
    : ToFormat (CFG Label Blk) where
  format cfg := formatCFG cfg
