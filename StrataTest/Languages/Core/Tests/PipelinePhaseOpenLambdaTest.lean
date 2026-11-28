/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core.PipelinePhase

/-! Importing `Core.PipelinePhase` brings no `Core.Lambda` namespace into scope, also for a file
outside the module system, which sees every module the import loads: inside `namespace Core`,
`open Lambda` opens the root `Lambda`. -/

namespace Core

open Lambda

example := @LExpr.eval
example : LMonoTy := LMonoTy.int

end Core

/-! `Core.PipelinePhase` publicly imports `Core.Interpreter`, so `Core.Env` is in scope:
inside `namespace Core` a bare `Env` is `Core.Env` — the interpreter environment, which takes
no parameter — even under `open Imperative`, and the imperative execution environment must be
written `Imperative.Env Expression`. -/

namespace Core

open Imperative

example : Env = Core.Env := rfl
example (ρ : Imperative.Env Expression) := ρ.store

end Core
