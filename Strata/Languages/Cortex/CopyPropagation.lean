/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Liveness

/-!
# Copy propagation

Replaces a read of a variable by the variable or the literal it was copied
from. The pass deletes nothing: a copy whose target is no longer read is left
for dead-store elimination.

Within a block: after `x := y` or `x := k`, with `k` a literal, a read of `x`
becomes `y` or `k`, until `x` or `y` is assigned. The facts start empty in
every block, so a block entered through a handler, whose binder was just
assigned, sees none.

Across the body, for a copy of a parameter: a local `x` whose only assignment
is `x := a` in the entry block, where `a` is an input that the body never
assigns, is replaced by `a` everywhere. This requires that the entry block
runs once (no transfer and no handler enters it), and that no command before
the copy reads `x` or may throw, so that no handler can observe `x` before the
copy.

Globals are neither replaced nor used as a replacement, since a call can
assign them.
-/

namespace Cortex.CopyPropagation

open Imperative Liveness

public section

/-- A replacement for each variable that has one. -/
private abbrev Facts := Std.HashMap String Expr

private def isLiteral : Expr → Bool
  | .const .. => true
  | _ => false

private def substFacts (facts : Facts) (e : Expr) : Expr :=
  mapExpr (fun
    | .fvar _ n _ => facts.get? n.name
    | _ => none) e

private def reads (facts : Facts) (uses : List String) : Bool :=
  !facts.isEmpty && uses.any facts.contains

private def substCmd (facts : Facts) (c : IRCmd) : IRCmd × Bool :=
  if reads facts (cmdUses c) then (mapCmdExprs (substFacts facts) id c, true) else (c, false)

private def substTransfer (facts : Facts) (t : DetTransferCmd Label Core.Expression) :
    DetTransferCmd Label Core.Expression × Bool :=
  if reads facts (transferUses t) then (mapTransfer (substFacts facts) t, true) else (t, false)

/-- `facts` without what an assignment to `x` invalidates: the replacement of
`x`, and every replacement by `x`. -/
private def forget (facts : Facts) (x : String) : Facts :=
  (facts.erase x).filter fun _ e => match e with
    | .fvar _ n _ => n.name != x
    | _ => true

/-- The fact that `c` establishes, if it copies a variable or a literal into a
different local. -/
private def copyOf (vs : Vars) : IRCmd → Option (String × Expr)
  | .cmd (.init x _ (.det e) _) | .cmd (.set x (.det e) _) =>
    if !vs.isLocal x.name then none else
    match e with
    | .fvar _ y _ => if y.name != x.name && vs.isLocal y.name then some (x.name, e) else none
    | e => if isLiteral e then some (x.name, e) else none
  | _ => none

private def propagateBlock (vs : Vars) (blk : LBlock) : LBlock × Bool :=
  let (facts, cmds, changed) := blk.cmds.foldl (init := (({} : Facts), (#[] : Array IRCmd), false))
    fun (facts, cmds, changed) c =>
      let (c, ch) := substCmd facts c
      let facts := (assignedNames c).foldl forget facts
      let facts := match copyOf vs c with
        | some (x, e) => facts.insert x e
        | none => facts
      (facts, cmds.push c, changed || ch)
  let (transfer, ch) := substTransfer facts blk.transfer
  ({ cmds := cmds.toList, transfer }, changed || ch)

/-- How often the body assigns each variable: once per assigning command,
declarations included, and once per handler that binds it. -/
private def assignmentCounts (b : Body) : Std.HashMap String Nat :=
  let bump := fun (m : Std.HashMap String Nat) (x : String) => m.insert x (m.getD x 0 + 1)
  let m := b.cfg.blocks.foldl (init := {}) fun m (_, blk) =>
    blk.cmds.foldl (fun m c => (assignedNames c).foldl bump m) m
  b.handlers.foldl (fun m h => bump m h.binder.name) m

/-- The locals that are only a copy of a never-assigned input, with that input. -/
private def parameterCopies (vs : Vars) (p : Procedure) (b : Body) : Facts :=
  let entry := b.cfg.entry
  let entered := b.cfg.blocks.any (fun (_, blk) => blk.transfer.targets.contains entry)
    || b.handlers.any (·.target == entry)
  match (if entered then none else b.cfg.blocks.lookup entry) with
  | none => {}
  | some blk =>
    let counts := assignmentCounts b
    let outputs := p.outputs.map (·.1.name)
    let candidate := fun (x : String) (e : Expr) (assignments : Nat) =>
      match e with
      | .fvar _ a _ =>
        vs.inputs.contains a.name && counts.getD a.name 0 == 0 &&
          vs.isLocal x && !vs.inputs.contains x && !outputs.contains x &&
          counts.getD x 0 == assignments
      | _ => false
    -- `declared` holds the locals that the entry block has declared so far and
    -- not read since; the scan stops at the first command that may throw.
    let (facts, _, _) := blk.cmds.foldl (init := (({} : Facts), ({} : VarSet), false))
      fun (facts, declared, stop) c =>
        if stop || mayThrow c then (facts, declared, true) else
        let declared := (cmdUses c).foldl (·.erase ·) declared
        match c with
        | .cmd (.init x _ (.det e) _) =>
          if candidate x.name e 1 then (facts.insert x.name e, declared, false)
          else (facts, declared.insert x.name, false)
        | .cmd (.init x _ .nondet _) => (facts, declared.insert x.name, false)
        | .cmd (.set x (.det e) _) =>
          if declared.contains x.name && candidate x.name e 2 then (facts.insert x.name e, declared, false)
          else (facts, declared.erase x.name, false)
        | c => (facts, (assignedNames c).foldl (·.erase ·) declared, false)
    facts

private def propagateParameters (vs : Vars) (p : Procedure) (b : Body) : Body × Bool :=
  let facts := parameterCopies vs p b
  if facts.isEmpty then (b, false) else
  let (blocks, changed) := b.cfg.blocks.foldl (init := ((#[] : Array (Label × LBlock)), false))
    fun (blocks, changed) (l, blk) =>
      let (cmds, ch) := blk.cmds.foldl (init := ((#[] : Array IRCmd), false)) fun (cmds, ch) c =>
        let (c, ch') := substCmd facts c
        (cmds.push c, ch || ch')
      let (transfer, ch') := substTransfer facts blk.transfer
      (blocks.push (l, { cmds := cmds.toList, transfer }), changed || ch || ch')
  ({ b with cfg := { b.cfg with blocks := blocks.toList } }, changed)

/-- `p` with copies propagated, or `none` when nothing changes. -/
def onProcedure (prog : UnorderedProgram) (p : Procedure) : Option Procedure := do
  let b ← p.body
  let vs := Vars.of prog p b
  let (b, changed) := propagateParameters vs p b
  let (blocks, changed) := b.cfg.blocks.foldl (init := ((#[] : Array (Label × LBlock)), changed))
    fun (blocks, changed) (l, blk) =>
      let (blk, ch) := propagateBlock vs blk
      (blocks.push (l, blk), changed || ch)
  if changed then some { p with body := some { b with cfg := { b.cfg with blocks := blocks.toList } } }
  else none

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  .ok (prog.mapProcedures fun p => (onProcedure prog p).getD p)

def pass : Pass := Pass.onUnordered "CopyPropagation" run

end

end Cortex.CopyPropagation
