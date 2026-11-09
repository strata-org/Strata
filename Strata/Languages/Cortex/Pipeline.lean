/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.ToCore
public import Strata.Languages.Cortex.LowerDispatch
public import Strata.Languages.Cortex.LowerExceptions
public import Strata.Languages.Cortex.LowerComposites
public import Strata.Languages.Cortex.LowerCTE
public import Strata.Languages.Cortex.LowerHeap
public import Strata.Languages.Cortex.LowerGlobals
public import Strata.Languages.Cortex.Ordering

namespace Cortex

public section

def passes : List Pass :=
  [LowerDispatch.pass, LowerExceptions.pass, LowerComposites.pass, LowerCTE.pass, LowerHeap.pass,
   LowerGlobals.pass, Ordering.pass]

def runPasses (ps : List Pass) (prog : Program) : Except String Program :=
  ps.foldlM (fun prog p => match p.run prog with
    | .ok prog' => .ok prog'
    | .error e => .error s!"{p.name}: {e}") prog

def toCoreProgram (prog : UnorderedProgram) : Except String Core.Program := do
  ToCore.programToCore (← runPasses passes (.unordered prog))

end

end Cortex
