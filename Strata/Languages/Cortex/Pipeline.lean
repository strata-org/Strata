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

def runPasses (ps : List Pass) (m : Module) : Except String Module :=
  ps.foldlM (fun m p => match p.run m with
    | .ok m' => .ok m'
    | .error e => .error s!"{p.name}: {e}") m

def toCoreProgram (m : Module) : Except String Core.Program := do
  ToCore.moduleToCore (← runPasses passes m)

end

end Cortex
