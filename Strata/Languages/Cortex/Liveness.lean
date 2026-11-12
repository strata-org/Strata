/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

/-!
# Live variables of a Cortex procedure body

A backward dataflow analysis over the blocks of a body. A variable is live at
a point when some path from that point reads it before assigning it.

Two kinds of edges leave a block: its transfer, and, for every handler that
covers the block, an edge from each command that may throw to the handler's
target. So whatever is live on entry to a covering handler, other than the
handler's binder, is live before every command of the block that may throw.
A `call`, a `virtualCall` and a `throw` may throw; no other command does.

The outputs of the procedure are live at `finish`.

The analysis treats every name as a variable of the procedure. It does not
model that a callee reads and writes the globals, so its result says nothing
about a global. `Vars.isPlain` identifies the variables for which the result
can justify deleting or redirecting an assignment.
-/

namespace Cortex.Liveness

open Imperative

public section

abbrev VarSet := Std.HashSet String

/-- The free variables of `e`. -/
def exprVars (e : Expr) : List String :=
  (HasFvars.getFvars (P := Core.Expression) e).map (·.name)

/-- The operators that occur in `e`. -/
def exprOps : Expr → List String
  | .op _ o _ => [o.name]
  | .app _ f a => exprOps f ++ exprOps a
  | .ite _ c t e => exprOps c ++ exprOps t ++ exprOps e
  | .eq _ a b => exprOps a ++ exprOps b
  | .abs _ _ _ b => exprOps b
  | .quant _ _ _ _ tr b => exprOps tr ++ exprOps b
  | _ => []

/-- Whether evaluating `e` always succeeds and carries no proof obligation:
every operator in `e` is a function of Core's factory that has no
precondition. An operator with a precondition, such as `Int.SafeDiv`, makes
the verifier check that precondition where the expression is evaluated, and
stops the interpreter when it does not hold. An operator that Core's factory
does not have, such as a function of one of the program's datatypes, counts as
having one. -/
def isTotal (e : Expr) : Bool :=
  (exprOps e).all fun o => match Core.Factory.get? o with
    | some f => f.preconditions.isEmpty
    | none => false

/-- Whether the right-hand side of a `set` or an `init` is total: a havoc, or
a total expression. Only an assignment with a total right-hand side may be
deleted. -/
def rhsIsTotal : ExprOrNondet Core.Expression → Bool
  | .det e => isTotal e
  | .nondet => true

/-- The expressions that a command evaluates. -/
def cmdExprs : IRCmd → List Expr
  | .cmd (.init _ _ (.det e) _) | .cmd (.set _ (.det e) _) => [e]
  | .cmd (.init _ _ .nondet _) | .cmd (.set _ .nondet _) => []
  | .cmd (.assert _ e _) | .cmd (.assume _ e _) | .cmd (.cover _ e _) => [e]
  | .cast _ _ e _ _ => [e]
  | .new .. => []
  | .readField _ o _ _ | .instanceOf _ o _ _ => [o]
  | .writeField o _ v _ => [o, v]
  | .call _ _ args _ | .virtualCall _ _ _ args _ => args
  | .throw e _ => [e]

/-- The variables that a command reads. -/
def cmdUses (c : IRCmd) : List String := (cmdExprs c).flatMap exprVars

/-- The variables that a transfer reads. -/
def transferUses : DetTransferCmd Label Core.Expression → List String
  | .condGoto c _ _ _ => exprVars c
  | .finish _ => []

/-- Whether a command can leave its block through an exception handler. -/
def mayThrow : IRCmd → Bool
  | .call .. | .virtualCall .. | .throw .. => true
  | _ => false

/-- The variables live before `c`, given those live after it and those live
into the handlers that cover its block. -/
def liveBeforeCmd (handlerLive : VarSet) (c : IRCmd) (live : VarSet) : VarSet :=
  let live := (assignedNames c).foldl (·.erase ·) live
  let live := live.insertMany (cmdUses c)
  if mayThrow c then live.insertMany handlerLive else live

/-- The variables live before the transfer of a block with live-out set `out`. -/
def liveBeforeTransfer (out : VarSet) (blk : LBlock) : VarSet :=
  out.insertMany (transferUses blk.transfer)

/-- The result of the analysis, per block label. -/
structure Info where
  /-- Live on entry to the block. -/
  liveIn : Std.HashMap Label VarSet := {}
  /-- Live after the block's transfer. -/
  liveOut : Std.HashMap Label VarSet := {}
  /-- Live on entry to a handler that covers the block, without that handler's
  binder. -/
  handlerLive : Std.HashMap Label VarSet := {}

def Info.liveInOf (i : Info) (l : Label) : VarSet := i.liveIn.getD l {}
def Info.liveOutOf (i : Info) (l : Label) : VarSet := i.liveOut.getD l {}
def Info.handlerLiveOf (i : Info) (l : Label) : VarSet := i.handlerLive.getD l {}

/-- One backward sweep over the blocks. Returns the new facts, and whether any
set grew. -/
private def sweep (outputs : List String) (b : Body) (info : Info) : Info × Bool :=
  b.cfg.blocks.reverse.foldl (init := (info, false)) fun (info, grew) (l, blk) =>
    let out : VarSet := match blk.transfer with
      | .finish _ => Std.HashSet.ofList outputs
      | .condGoto _ lt lf _ => (info.liveInOf lt).insertMany (info.liveInOf lf)
    let hl : VarSet := b.handlers.foldl (init := {}) fun acc h =>
      if h.covered.contains l then acc.insertMany ((info.liveInOf h.target).erase h.binder.name) else acc
    let live := blk.cmds.foldr (liveBeforeCmd hl) (liveBeforeTransfer out blk)
    let grew := grew || live.size != (info.liveInOf l).size || out.size != (info.liveOutOf l).size
      || hl.size != (info.handlerLiveOf l).size
    ({ liveIn := info.liveIn.insert l live, liveOut := info.liveOut.insert l out,
       handlerLive := info.handlerLive.insert l hl }, grew)

/-- Sweep until no set grows. The sets only grow from one sweep to the next,
so comparing sizes detects a change, and `fuel` sweeps suffice when `fuel`
exceeds the number of (block, variable) pairs. -/
private def iterate (outputs : List String) (b : Body) : Nat → Info → Info
  | 0, info => info
  | fuel + 1, info =>
    let (info, grew) := sweep outputs b info
    if grew then iterate outputs b fuel info else info

/-- The live variables of body `b` of procedure `p`. -/
def analyze (p : Procedure) (b : Body) : Info :=
  let names : VarSet := b.cfg.blocks.foldl (init := Std.HashSet.ofList (p.outputs.map (·.1.name)))
    fun s (_, blk) =>
      (blk.cmds.foldl (fun s c => (s.insertMany (cmdUses c)).insertMany (assignedNames c)) s).insertMany
        (transferUses blk.transfer)
  iterate (p.outputs.map (·.1.name)) b (3 * b.cfg.blocks.length * (names.size + 1) + 2) {}

/-- The variables live after each command of `blk`, in command order, for a
block with live-out set `out` covered by handlers with live-in `hl`. -/
def liveAfterCmds (hl out : VarSet) (blk : LBlock) : Array VarSet :=
  let (_, afters) := blk.cmds.foldr (init := (liveBeforeTransfer out blk, ([] : List VarSet)))
    fun c (live, afters) => (liveBeforeCmd hl c live, live :: afters)
  afters.toArray

/-- What the cleanup passes need to know about the variables of one procedure
body: the declared type of each parameter and each `init`, and which names
they must leave alone. -/
structure Vars where
  types : Std.HashMap String Core.Expression.Ty
  inputs : VarSet
  globals : VarSet
  /-- The names of the program's constrained types. `LowerCTE` adds a check at
  each assignment to a variable of such a type. -/
  constrained : VarSet

def Vars.of (prog : UnorderedProgram) (p : Procedure) (b : Body) : Vars :=
  let params := (p.inputs ++ p.outputs).foldl (fun m (x, t) => m.insert x.name t) {}
  let types := b.cfg.blocks.foldl (init := params) fun m (_, blk) =>
    blk.cmds.foldl (init := m) fun m c => match c with
      | .cmd (.init x t _ _) => m.insert x.name t
      | _ => m
  { types
    inputs := Std.HashSet.ofList (p.inputs.map (·.1.name))
    globals := Std.HashSet.ofList (prog.globals.map (·.1.name))
    constrained := Std.HashSet.ofList (prog.constrained.map (·.name)) }

/-- Whether `x` is a parameter or a declared local of the procedure, and not a
global. -/
def Vars.isLocal (vs : Vars) (x : String) : Bool :=
  vs.types.contains x && !vs.globals.contains x

/-- Whether `t` is a constrained type. -/
def Vars.isConstrainedTy (vs : Vars) (t : Core.Expression.Ty) : Bool :=
  match t with
  | .forAll [] (.tcons n []) => vs.constrained.contains n
  | _ => false

/-- Whether `x` is a local whose assignments carry no check: its type is not a
constrained type. Only an assignment to such a variable may be deleted or
redirected. -/
def Vars.isPlain (vs : Vars) (x : String) : Bool :=
  vs.isLocal x && match vs.types.get? x with
    | some t => !vs.isConstrainedTy t
    | none => false

end

end Cortex.Liveness
