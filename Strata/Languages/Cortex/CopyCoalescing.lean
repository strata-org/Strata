/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Liveness

/-!
# Copy coalescing

Rewrites `call t := p(..); x := t` to `call x := p(..)`, and likewise for a
`virtualCall` with one result, a `new`, a field read and an `instanceOf`. The
defining command keeps its place and its source location, and only the copy
`x := t` is deleted.

The rewrite applies when all of these hold:
- `t` and `x` are different locals of the same type, which is not a
  constrained type, and `x` is not an input;
- no command between the two reads or assigns `t` or `x`;
- `t` is not live after the copy;
- neither `t` nor `x` is live into a handler that covers the block.

The last condition keeps what a handler observes. A call that throws assigns
nothing, so the handler must still see the old value of `x`; and a command
between the two that throws must not expose that `t` was not assigned.
-/

namespace Cortex.CopyCoalescing

open Imperative Liveness

public section

/-- The variable that `c` defines, when `c` is a command whose single result
can be redirected. -/
private def definedVar? : IRCmd → Option String
  | .new x .. | .readField x .. | .instanceOf x .. => some x.name
  | .call [x] .. | .virtualCall [x] .. => some x.name
  | _ => none

private def withDefinedVar (y : Core.Expression.Ident) : IRCmd → IRCmd
  | .new _ ty md => .new y ty md
  | .readField _ o f md => .readField y o f md
  | .instanceOf _ o ty md => .instanceOf y o ty md
  | .call _ p args md => .call [y] p args md
  | .virtualCall _ o m args md => .virtualCall [y] o m args md
  | c => c

private def mentions (c : IRCmd) (x : String) : Bool :=
  (cmdUses c).contains x || (assignedNames c).contains x

/-- The index after `i` of the copy `y := t` that can be merged into the
command at `i`, which defines `t`, with `y`. -/
private def findCopy (vs : Vars) (hl out : VarSet) (blk : LBlock) (cmds : Array IRCmd) (i : Nat)
    (t : String) : Option (Nat × Core.Expression.Ident) := do
  -- The first command after `i` that mentions `t` must be the copy.
  let j ← (List.range' (i + 1) (cmds.size - (i + 1))).find? fun j => cmds[j]?.any (mentions · t)
  let some (.cmd (.set y (.det (.fvar _ src _)) _)) := cmds[j]? | none
  guard (src.name == t && y.name != t)
  guard (vs.isPlain t && vs.isPlain y.name && !vs.inputs.contains y.name)
  guard (vs.types.get? t == vs.types.get? y.name)
  guard (!hl.contains t && !hl.contains y.name)
  guard ((List.range' (i + 1) (j - (i + 1))).all fun k => cmds[k]?.all (!mentions · y.name))
  let after := liveAfterCmds hl out { blk with cmds := cmds.toList }
  guard (!(after[j]?.getD {}).contains t)
  return (j, y)

/-- `blk` with its copies coalesced, and how many were. -/
private def coalesceBlock (vs : Vars) (hl out : VarSet) (blk : LBlock) : LBlock × Nat :=
  let (cmds, merged) := (List.range blk.cmds.length).foldl (init := (blk.cmds.toArray, 0))
    fun (cmds, merged) i =>
      match cmds[i]? >>= definedVar? >>= findCopy vs hl out blk cmds i with
      | some (j, y) => ((cmds.modify i (withDefinedVar y)).eraseIdxIfInBounds j, merged + 1)
      | none => (cmds, merged)
  ({ blk with cmds := cmds.toList }, merged)

/-- `p` with its copies coalesced, or `none` when there are none. -/
def onProcedure (prog : UnorderedProgram) (p : Procedure) : Option Procedure := do
  let b ← p.body
  let vs := Vars.of prog p b
  let info := analyze p b
  let (blocks, merged) := b.cfg.blocks.foldl (init := ((#[] : Array (Label × LBlock)), 0))
    fun (blocks, merged) (l, blk) =>
      let (blk, n) := coalesceBlock vs (info.handlerLiveOf l) (info.liveOutOf l) blk
      (blocks.push (l, blk), merged + n)
  if merged > 0 then some { p with body := some { b with cfg := { b.cfg with blocks := blocks.toList } } }
  else none

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  .ok (prog.mapProcedures fun p => (onProcedure prog p).getD p)

def pass : Pass := Pass.onUnordered "CopyCoalescing" run

end

end Cortex.CopyCoalescing
