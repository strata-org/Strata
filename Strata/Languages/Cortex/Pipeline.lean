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
public import Strata.Languages.Cortex.Ordering
public import Strata.Languages.Cortex.CopyAssignedInputs

namespace Cortex

public section

def passes : List Pass :=
  [LowerDispatch.pass, LowerExceptions.pass, PruneUnreachable.pass, LowerComposites.pass,
   LowerCTE.pass, LowerHeap.pass, LowerGlobals.pass, Ordering.pass, CopyAssignedInputs.pass]

def runPasses (ps : List Pass) (prog : Program) : Except String Program :=
  ps.foldlM (fun prog p => match p.run prog with
    | .ok prog' => .ok prog'
    | .error e => .error s!"{p.name}: {e}") prog

def toCoreProgram (prog : UnorderedProgram) : Except String Core.Program := do
  ToCore.programToCore (← runPasses passes (.unordered prog))

/-- As `toCoreProgram`, with each procedure body emitted as a Core CFG body. -/
def toCoreProgramCFG (prog : UnorderedProgram) : Except String Core.Program := do
  ToCore.programToCoreCFG (← runPasses passes (.unordered prog))

end

end Cortex
