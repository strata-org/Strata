/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.ToCore
public import Strata.Languages.Cortex.ToCoreCFG
public import Strata.Languages.Cortex.LowerDispatch
public import Strata.Languages.Cortex.LowerExceptions
public import Strata.Languages.Cortex.PruneUnreachable
public import Strata.Languages.Cortex.LowerComposites
public import Strata.Languages.Cortex.LowerCTE
public import Strata.Languages.Cortex.LowerHeap
public import Strata.Languages.Cortex.LowerGlobals
public import Strata.Languages.Cortex.LowerDynamic
public import Strata.Languages.Cortex.FieldCasts
public import Strata.Languages.Cortex.Ordering
public import Strata.Languages.Cortex.CopyAssignedInputs
public import Strata.Languages.Cortex.Cleanup

namespace Cortex

public section

/-- The passes that lower a Cortex program to the form `ToCore` translates. -/
def loweringPasses : List Pass :=
  [LowerDispatch.pass, LowerExceptions.pass, PruneUnreachable.pass, LowerComposites.pass,
   LowerHeap.pass, LowerGlobals.pass, LowerCTE.pass, LowerDynamic.pass, Ordering.pass,
   CopyAssignedInputs.pass]

/-- The passes of the route to Core: the cleanup, then the lowering passes. -/
def passes : List Pass := Cleanup.pass :: loweringPasses

def runPasses (ps : List Pass) (prog : Program) : Except String Program :=
  ps.foldlM (fun prog p => match p.run prog with
    | .ok prog' => .ok prog'
    | .error e => .error s!"{p.name}: {e}") prog

/-- The Core program of `prog`. With `cleanup := false` the cleanup passes are
skipped, for comparing the two results. -/
def toCoreProgram (prog : UnorderedProgram) (cleanup : Bool := true) : Except String Core.Program := do
  ToCore.programToCore (← runPasses (if cleanup then passes else loweringPasses) (.unordered prog))

/-- As `toCoreProgram`, with each procedure body emitted as a Core CFG body. -/
def toCoreProgramCFG (prog : UnorderedProgram) (cleanup : Bool := true) : Except String Core.Program := do
  ToCore.programToCoreCFG (← runPasses (if cleanup then passes else loweringPasses) (.unordered prog))

end

end Cortex
