/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core

/-! # Concrete Interpreter for Strata Core Programs

This module re-exports the concrete interpretation API whose implementation
now lives in the standard evaluation files:

- `EvalMode` and `defaultFuel` — `Env.lean`
- `initConcreteEnv` — `ProgramEval.lean`
- `InterpResult`, `interpProcedure`, `getValue?` — `ProcedureEval.lean`
- Loop iteration and body-inlining call logic — `StatementEval.lean`

## Usage

```lean
let E ← Core.initConcreteEnv prog
let result := Core.interpProcedure E "__main__"
```
-/
