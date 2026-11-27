/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelineUnitChain
public import Strata.Transform.TerminationCheck
public import Strata.Transform.NondetElim
public import Strata.Transform.FilterProcedures

/-! # Successful runs of a pipeline phase

Key definitions: `PipelinePhase.Produces` (a phase ran successfully on a program and
produced another, from some transform state) and `Decl.isProcNamed` (a declaration is a
procedure of a given name). -/

namespace Core

open Imperative Transform

public section

/-- `d` is a procedure named `n`. -/
@[expose] def Decl.isProcNamed (n : String) : Decl → Bool
  | .proc q _ => q.header.name.1 == n
  | _ => false

/-- `pp` ran successfully on `p` and produced `p'`, as `runTransformsWithBackLinks` runs
    a phase (from some transform state). -/
@[expose] def PipelinePhase.Produces (pp : PipelinePhase) (p p' : Program) : Prop :=
  ∃ s s', Transform.runWith p (fun prog => do
    let (_, next) ← pp.transform prog
    return next) s = (.ok p', s')

end -- public section

end Core
