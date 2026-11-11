/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Liveness

/-!
# Unused-variable elimination

Deletes the declaration of a local that nothing mentions: no command reads or
assigns it, no transfer reads it, and no handler binds it. The initializer of
a deleted declaration is not evaluated any more, so a declaration is deleted
only when its initializer is total (`rhsIsTotal`): an unused
`var t := Int.SafeDiv(a, b)` stays, since evaluating it checks that `b` is not
zero.

The declaration of a variable of a constrained type stays, since `LowerCTE`
checks its initializer.
-/

namespace Cortex.UnusedVarElim

open Imperative Liveness

public section

/-- The variables that `b` mentions outside of their own declaration. -/
private def mentioned (b : Body) : VarSet :=
  let s := b.cfg.blocks.foldl (init := ({} : VarSet)) fun s (_, blk) =>
    let s := blk.cmds.foldl (init := s) fun s c =>
      let s := s.insertMany (cmdUses c)
      match c with
      | .cmd (.init ..) => s
      | c => s.insertMany (assignedNames c)
    s.insertMany (transferUses blk.transfer)
  b.handlers.foldl (fun s h => s.insert h.binder.name) s

/-- `p` without the declarations of its unused locals, or `none` when it has
none. -/
def onProcedure (prog : UnorderedProgram) (p : Procedure) : Option Procedure := do
  let b ← p.body
  let vs := Vars.of prog p b
  let used := mentioned b
  let unused := fun (c : IRCmd) => match c with
    | .cmd (.init x t rhs _) =>
      !used.contains x.name && !vs.globals.contains x.name && !vs.isConstrainedTy t && rhsIsTotal rhs
    | _ => false
  if b.cfg.blocks.any fun (_, blk) => blk.cmds.any unused then
    some { p with body := some { b with cfg := { b.cfg with blocks := b.cfg.blocks.map fun (l, blk) =>
      (l, { blk with cmds := blk.cmds.filter (!unused ·) }) } } }
  else none

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  .ok (prog.mapProcedures fun p => (onProcedure prog p).getD p)

def pass : Pass := Pass.onUnordered "UnusedVarElim" run

end

end Cortex.UnusedVarElim
