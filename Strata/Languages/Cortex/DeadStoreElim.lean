/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Liveness

/-!
# Dead-store elimination

Deletes a `set` of a local, with a value or without one (a havoc), when the
local is not live after it, and deletes a `set` that copies a local to itself.

A `set` is deleted only when its right-hand side is total (`rhsIsTotal`). A
dead `t := Int.SafeDiv(a, b)` stays: evaluating it checks that `b` is not
zero, and deleting it would drop that check.

Nothing else is deleted: a declaration, a `call`, a `new`, a field command, an
`assert`, an `assume` and a `throw` all stay, with their source locations. A
`set` of a global, or of a variable of a constrained type, stays as well: a
callee reads the first, and `LowerCTE` checks the second.

Liveness follows the handler edges, so a store that a covering handler can
observe is live at every later command of the block that may throw.
-/

namespace Cortex.DeadStoreElim

open Imperative Liveness

public section

private def isSelfCopy (x : Core.Expression.Ident) : ExprOrNondet Core.Expression → Bool
  | .det (.fvar _ y _) => y.name == x.name
  | _ => false

/-- `blk` without its dead stores, and how many were deleted. -/
private def sweepBlock (vs : Vars) (hl out : VarSet) (blk : LBlock) : LBlock × Nat :=
  let (cmds, _, deleted) := blk.cmds.foldr (init := (([] : List IRCmd), liveBeforeTransfer out blk, 0))
    fun c (cmds, live, deleted) =>
      match c with
      | .cmd (.set x rhs _) =>
        if vs.isPlain x.name && rhsIsTotal rhs && (!live.contains x.name || isSelfCopy x rhs) then (cmds, live, deleted + 1)
        else (c :: cmds, liveBeforeCmd hl c live, deleted)
      | c => (c :: cmds, liveBeforeCmd hl c live, deleted)
  ({ blk with cmds }, deleted)

/-- `p` without its dead stores, or `none` when it has none. -/
def onProcedure (prog : UnorderedProgram) (p : Procedure) : Option Procedure := do
  let b ← p.body
  let vs := Vars.of prog p b
  let info := analyze p b
  let (blocks, deleted) := b.cfg.blocks.foldl (init := ((#[] : Array (Label × LBlock)), 0))
    fun (blocks, deleted) (l, blk) =>
      let (blk, n) := sweepBlock vs (info.handlerLiveOf l) (info.liveOutOf l) blk
      (blocks.push (l, blk), deleted + n)
  if deleted > 0 then some { p with body := some { b with cfg := { b.cfg with blocks := blocks.toList } } }
  else none

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  .ok (prog.mapProcedures fun p => (onProcedure prog p).getD p)

def pass : Pass := Pass.onUnordered "DeadStoreElim" run

end

end Cortex.DeadStoreElim
