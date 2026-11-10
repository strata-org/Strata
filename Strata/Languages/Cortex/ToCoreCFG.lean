/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.ToCore

/-!
# Cortex to unstructured Core

`programToCoreCFG` emits each procedure body as a Core CFG body (`.cfg`), block
for block: labels, commands and transfers are kept, so no control flow is
rebuilt. The structured route (`ToCore.programToCore`) stays the default, since
the verifier (`Core.verify`) and the evaluator behind
`Core.Program.interpretEntries` accept only structured bodies.

Core's CFG type checker puts two requirements on the Cortex CFG that the
structured route does not:
* Every `init` sits in a block that dominates the uses of its variable and
  that is not on a cycle. `FromLaurel` output meets this: it declares every
  local in one block that runs once, before the body, and the passes declare
  theirs in blocks that run before that one. Nothing here hoists declarations;
  a frontend that declares a local inside a loop has to hoist it first.
* Every block that uses a local is reachable from the entry. An unreachable
  block is scoped without the locals of any dominator, so its uses are
  rejected. `PruneUnreachable` removes unreachable blocks.
-/

namespace Cortex.ToCore

open Imperative Lambda

public section

/-- A Cortex CFG as a Core CFG with the same labels and transfers. -/
private def cfgToCore (sigs : Std.HashMap String Sig) (cfg : LCFG) : Except String Core.DetCFG := do
  let blocks ← cfg.blocks.mapM fun (l, b) => do
    let cmds ← b.cmds.mapM (toCoreCmd sigs)
    return (l, ({ cmds, transfer := b.transfer } : DetBlock String Core.Command Core.Expression))
  return { entry := cfg.entry, blocks }

/-- A Cortex procedure as a Core procedure with a CFG body. A procedure without
a body gets the structured body of `procedureToCore`. -/
def procedureToCoreCFG (sigs : Std.HashMap String Sig) (p : Procedure) :
    Except String Core.Procedure := do
  match p.body with
  | none => procedureToCore sigs p
  | some b =>
    b.refuseHandlers "Core"
    let header ← procedureHeader p
    let cfg ← cfgToCore sigs b.cfg
    return { header, spec := { preconditions := [], postconditions := [] }, body := .cfg cfg }

/-- An ordered Cortex program as a Core program whose procedure bodies are CFGs. -/
def programToCoreCFG : Program → Except String Core.Program :=
  programToCoreWith procedureToCoreCFG

end

end Cortex.ToCore
