/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

/-!
# Local copies of assigned inputs

A Core procedure body may assign only its outputs and its locals. This pass
gives every Cortex procedure body that shape: an input `x` that the body
assigns and that is not an output is renamed `x$in`, and the body starts with
`init x := x$in`, which makes `x` a local.

The copies are prepended to the entry block when no block transfers to the
entry, so that they run once. Otherwise they run in a new entry block,
`$inputCopy`, that jumps to the old entry.

The renamed input avoids the names of the procedure's parameters and of the
variables that its body assigns, and the label of the new entry block avoids
the labels of the body.

The pass runs after `LowerExceptions`. Before it, a handler can enter the entry
block without a transfer, so the pass refuses a body that still has handlers.
-/

namespace Cortex.CopyAssignedInputs

open Imperative

public section

/-- A name that `used` does not contain: `base`, or, when `base` is taken,
`base` padded with `$` until it is longer than every name in `used`. -/
private def fresh (used : List String) (base : String) : String :=
  if used.contains base then
    base.pushn '$' (used.foldl (fun n l => max n l.length) 0 + 1 - base.length)
  else base

/-- `b` running `copies` first: at the start of the entry block when no block
transfers to the entry, and otherwise in a new entry block. -/
private def withCopies (b : Body) (copies : List IRCmd) : Body :=
  let cfg := b.cfg
  if cfg.blocks.any fun (_, blk) => blk.transfer.targets.contains cfg.entry then
    let entry := fresh cfg.labels "$inputCopy"
    { b with cfg := { entry, blocks := (entry, { cmds := copies, transfer := .goto cfg.entry }) :: cfg.blocks } }
  else
    { b with cfg := { cfg with blocks := cfg.blocks.map fun (l, blk) =>
        if l == cfg.entry then (l, { blk with cmds := copies ++ blk.cmds }) else (l, blk) } }

/-- `p` with a local copy of each input that its body assigns and that is not
an output. -/
private def copyInputs (p : Procedure) : Except String Procedure := do
  let some b := p.body | return p
  b.refuseHandlers "CopyAssignedInputs"
  let outNames := p.outputs.map (·.1.name)
  let assigned := b.assignedNames
  let mut used := p.inputs.map (·.1.name) ++ outNames ++ assigned
  let mut inputs := #[]
  let mut copies : Array IRCmd := #[]
  for (x, t) in p.inputs do
    if assigned.contains x.name && !outNames.contains x.name then
      let renamed : Core.Expression.Ident := ⟨fresh used s!"{x.name}$in", ()⟩
      used := renamed.name :: used
      inputs := inputs.push (renamed, t)
      copies := copies.push (.cmd (.init x t (.det (.fvar () renamed none)) .empty))
    else
      inputs := inputs.push (x, t)
  if copies.isEmpty then return p
  return { p with inputs := inputs.toList, body := some (withCopies b copies.toList) }

def run : Program → Except String Program
  | .unordered prog => do
    return .unordered { prog with procedures := ← prog.procedures.mapM copyInputs }
  | .ordered prog => do
    let decls ← prog.decls.mapM fun
      | .procedure p => .procedure <$> copyInputs p
      | d => pure d
    return .ordered { decls }

def pass : Pass := { name := "CopyAssignedInputs", run }

end

end Cortex.CopyAssignedInputs
