/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
import Strata.DL.Imperative.CFG

/-!
# Unreachable-block pruning

Drops the blocks of each procedure body that no path from the entry reaches.
`LowerExceptions` leaves such blocks behind: a handler that no `throw` reaches,
and the block that follows a `throw`.

The CFG route to Core (`ToCore.programToCoreCFG`) requires the pass, and it has
to run before the Core type check: Core's CFG type checker gives an unreachable
block none of its dominators' locals, so it rejects every local that such a
block uses. On the structured route (`ToCore.programToCore`) the pass changes
nothing, since that route emits only the blocks that the entry reaches.

The pass runs after `LowerExceptions`. Before it, a handler block is entered
through the handler table and not through a transfer, so the pass refuses a
body that still has handlers.
-/

namespace Cortex.PruneUnreachable

open Imperative

public section

/-- `b` without the blocks that no path from its entry reaches. -/
private def pruneBody (b : Body) : Except String Body := do
  b.refuseHandlers "PruneUnreachable"
  let reachable := b.cfg.reachableLabels
  return { b with cfg := { b.cfg with blocks := b.cfg.blocks.filter fun (l, _) => reachable.contains l } }

def run (prog : UnorderedProgram) : Except String UnorderedProgram := do
  let procedures ← prog.procedures.mapM fun p => do
    return { p with body := ← p.body.mapM pruneBody }
  return { prog with procedures }

def pass : Pass := Pass.onUnordered "PruneUnreachable" run

end

end Cortex.PruneUnreachable
