/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.CopyPropagation
public import Strata.Languages.Cortex.CopyCoalescing
public import Strata.Languages.Cortex.DeadStoreElim
public import Strata.Languages.Cortex.UnusedVarElim

/-!
# Cleanup of Cortex programs

Runs the cleanup passes on every procedure body: copy propagation, copy
coalescing and dead-store elimination, repeated in that order until none of
them changes the procedure, and then unused-variable elimination once.

The passes keep the behaviour of the program. They delete only `set` commands
of locals and declarations of locals that nothing mentions, and only when the
deleted right-hand side is total; every other command stays, in order, with
its source location.

`Cleanup.pass` runs first in both routes: before the lowering passes on the
route to Core, and before `LowerCTE` on the interpreter route.
-/

namespace Cortex.Cleanup

public section

/-- A cleanup pass on one procedure: the changed procedure, or `none`. -/
structure ProcedurePass where
  name : String
  run : UnorderedProgram → Procedure → Option Procedure

/-- The passes that are repeated until none changes the procedure. -/
def repeatedPasses : List ProcedurePass :=
  [⟨"CopyPropagation", CopyPropagation.onProcedure⟩,
   ⟨"CopyCoalescing", CopyCoalescing.onProcedure⟩,
   ⟨"DeadStoreElim", DeadStoreElim.onProcedure⟩]

/-- The passes that run once, after the repeated ones. -/
def finalPasses : List ProcedurePass :=
  [⟨"UnusedVarElim", UnusedVarElim.onProcedure⟩]

/-- The cleanup passes as program passes, in the order of one round. -/
def cleanupPasses : List Pass :=
  [CopyPropagation.pass, CopyCoalescing.pass, DeadStoreElim.pass, UnusedVarElim.pass]

/-- The most rounds of the repeated passes on one procedure. Every pass keeps
the behaviour of the procedure, so stopping at the bound is safe. -/
def maxRounds : Nat := 64

private def runOnce (prog : UnorderedProgram) (ps : List ProcedurePass) (p : Procedure) : Procedure × Bool :=
  ps.foldl (init := (p, false)) fun (p, changed) pass =>
    match pass.run prog p with
    | some p' => (p', true)
    | none => (p, changed)

private def repeatRounds (prog : UnorderedProgram) : Nat → Nat → Procedure → Procedure × Nat
  | 0, rounds, p => (p, rounds)
  | fuel + 1, rounds, p =>
    let (p, changed) := runOnce prog repeatedPasses p
    if changed then repeatRounds prog fuel (rounds + 1) p else (p, rounds + 1)

/-- `p` cleaned up, and the number of rounds of the repeated passes that ran,
the last of which changed nothing unless the bound was reached. -/
def cleanupProcedure (prog : UnorderedProgram) (p : Procedure) : Procedure × Nat :=
  if p.body.isNone then (p, 0) else
  let (p, rounds) := repeatRounds prog maxRounds 0 p
  ((runOnce prog finalPasses p).1, rounds)

def run (prog : UnorderedProgram) : Except String UnorderedProgram :=
  .ok (prog.mapProcedures fun p => (cleanupProcedure prog p).1)

def pass : Pass := Pass.onUnordered "Cleanup" run

end

end Cortex.Cleanup
