/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.CmdEval
import Strata.DL.Lambda.LExprEval

/-! # Concrete Interpreter for Strata Core Programs

A fuel-based concrete interpreter that executes Strata Core programs by
actually running procedure bodies and iterating loops, rather than
performing symbolic verification.

## Design

- Uses `interpExpr` for expression evaluation (a thin wrapper around `LExpr.eval`).
- Three mutually recursive functions (`interpStmt`, `interpBlock`, `interpCmd`)
  with a shared `fuel : Nat` parameter decremented on each recursive call.
- Returns a structured `StepResult` distinguishing normal completion, exit
  propagation, fuel exhaustion, and stuck states.
-/

namespace Core

open Lambda Imperative Strata
open Std (ToFormat Format format)

/-! ## Helpers -/

/-- Default value based on an optional monotype from the store. -/
private def defaultValueOfMonoTy (ty : Option LMonoTy) : Expression.Expr :=
  match ty with
  | some (.tcons "int" _) => .intConst () 0
  | some (.tcons "bool" _) => .boolConst () false
  | some (.tcons "string" _) => .const () (.strConst "")
  | some (.tcons "real" _) => .const () (.realConst 0)
  | _ => .intConst () 0

/-- Produce a default value for a type. Used for havoc and uninitialized variables. -/
private def defaultValue (ty : Expression.Ty) : Expression.Expr :=
  if h : ty.isMonoType then
    defaultValueOfMonoTy (ty.toMonoType h)
  else .intConst () 0


/-! ## Interpreter Core -/

/-- Default fuel for the interpreter. -/
def defaultFuel : Nat := 10000


/-! ## Program-Level Interpreter -/


end Core
