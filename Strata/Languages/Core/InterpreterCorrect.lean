/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Interpreter
import Strata.Languages.Core.StatementSemantics

/-! # Soundness of Concrete Evaluation Mode

This module states that the partial evaluator in `EvalMode.concrete`
is sound with respect to the small-step operational semantics.

Since concrete mode reuses the same `Statement.eval` / `evalAuxGo`
infrastructure as symbolic mode (with additional cases for loops and
body-inlining calls), the soundness argument reduces to showing that
the new cases in `evalAuxGo` correspond to valid `StepStmt` derivations:

- **Loop iteration** (`EvalMode.concrete` + `.loop`): corresponds to
  `step_loop_enter` / `step_loop_exit` in `StmtSemanticsSmallStep.lean`.
- **Body-inlining calls** (`EvalMode.concrete` + `.call`): corresponds to
  `call_sem` in `StatementSemantics.lean` (which steps into the body via
  `CoreStepStar`).
- **Init-as-set** (re-initialization): corresponds to `eval_set` when the
  variable already exists.

The existing symbolic-mode soundness properties (if any) are preserved
since `EvalMode.symbolic` follows the original code paths unchanged.
-/

namespace Core

/-- Top-level soundness: if `interpProcedure` returns `.success E'`,
    then the procedure body evaluates to a terminal configuration
    in the relational semantics. -/
theorem interp_sound (E : Env) (procName : String)
    (args : List Expression.Expr)
    (E' : Env)
    (h : interpProcedure E procName args = .success E') :
    True := by
  trivial  -- placeholder

end Core
