/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.MetaData
import Strata.DL.Imperative.PureExpr

namespace Imperative

/-! # Imperative dialect: unstructured control-flow graphs

A control-flow graph consists of a list of labeled blocks paired with a
distinguished entry label. Each basic block consists of a label, a list of
commands, and a transfer command. The types of each of these components are
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
  | cgoto (p : P.Expr) (lt lf : Label) (md : MetaData P := .empty)
  /-- Stop execution of the current unstructured program. If in a procedure
  body, this can be interpreted as returning to the caller. -/
  | finish (md : MetaData P := .empty)

/-- For the moment, we don't have an unconditional jump in the language, and
model it instead using `cgoto`. By defining this function, we can easily create
unconditional jumps, and future proof against the possibility of adding it as a
constructor in the future.  -/
def DetTransferCmd.goto [HasBool P] (l : Label) : DetTransferCmd Label P :=
  .cgoto HasBool.tt l l

/-- A `NondetTransfer` command terminates a non-deterministic basic block,
indicating the list of possible blocks where execution could proceed next, if
anywhere. -/
inductive NondetTransferCmd (Label : Type) (P : PureExpr) where
  /-- Transfer to any one of a list of labels, non-deterministically. `goto`
  with no labels is equivalent to `finish` in `DetTransferCmd` -/
  | goto (ls : List Label) (md : MetaData P := .empty)
  deriving Inhabited

def NondetTransferCmd.targets : NondetTransferCmd Label P → List Label
| .goto ls _ => ls

/-- A basic block consists of a label, a list of body commands, and a transfer
command that indicates where to go next. It can be deterministic or
non-deterministic depending on the type of transfer command. -/
structure BasicBlock (Label TransferCmd Cmd : Type) where
  label : Label
  cmds : List Cmd
  transfer : TransferCmd

def DetBlock (Label Cmd : Type) (P : PureExpr) :=
  BasicBlock Label (DetTransferCmd Label P) Cmd

def NondetBlock (Label Cmd : Type) (P : PureExpr) :=
  BasicBlock Label (NondetTransferCmd Label P) Cmd

/-- A control flow graph is a list of blocks paired with a label indicating
where execution should start. -/
structure CFG (Label Block : Type) where
  entry : Label
  blocks : List Block -- TODO: it would be very nice to have Label → Block

--------

open Std (ToFormat Format format)

def formatDetTransferCmd (P : PureExpr) (c : DetTransferCmd Label P)
  [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .cgoto c lt lf md => f!"{md}cgoto {c} {lt} {lf}"
  | .finish md => f!"{md}finish"

def formatNondetTransferCmd (P : PureExpr) (c : NondetTransferCmd Label P)
  [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty] : Format :=
  match c with
  | .goto ls md => f!"{md}goto {ls}"

def formatBasicBlock (b : BasicBlock Label TransferCmd TCmd)
  [ToFormat Label] [ToFormat TransferCmd] [ToFormat TCmd] : Format :=
  f!"{b.label}:{Format.line}  {b.cmds}{Format.line}  {b.transfer}"

def formatCFG (cfg : CFG Label Blk)
  [ToFormat Label] [ToFormat Blk] : Format :=
  f!"Entry: {cfg.entry}{Format.line}{Format.line}{cfg.blocks}"

instance [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
    : ToFormat (DetTransferCmd Label P) where
  format c := formatDetTransferCmd P c

instance [ToFormat Label] [ToFormat P.Ident] [ToFormat P.Expr] [ToFormat P.Ty]
    : ToFormat (NondetTransferCmd Label P) where
  format c := formatNondetTransferCmd P c

instance [ToFormat Label] [ToFormat TransferCmd] [ToFormat TCmd]
    : ToFormat (BasicBlock Label TransferCmd TCmd) where
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
