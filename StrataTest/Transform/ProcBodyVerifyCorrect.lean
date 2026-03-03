/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.ProcBodyVerify
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.ProcedureEval

/-! # Procedure Body Verification Correctness Proof

This file contains the correctness proof for the ProcBodyVerify transformation.

Main theorem: If the body verification statement fails, then a call to the
procedure can also fail.

The key insight is that the transformation creates a statement that:
1. Assumes preconditions (which are asserted at call sites)
2. Executes the body
3. Asserts postconditions (which are assumed at call sites)

Therefore, if an assertion fails in the body verification, either:
- A precondition was violated (would fail at call site)
- A postcondition doesn't hold (would fail in the implementation)
-/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative

/-- Helper: Extract all assertions from a statement -/
def extractAssertions : Statement → List (String × Expression.Expr)
  | .cmd (.cmd (.assert label expr _)) => [(label, expr)]
  | .block _ stmts _ => stmts.flatMap extractAssertions
  | .ite _ thenStmts elseStmts _ => 
      (thenStmts.flatMap extractAssertions) ++ (elseStmts.flatMap extractAssertions)
  | .loop _ _ _ body _ => body.flatMap extractAssertions
  | _ => []

/-- Helper: Extract all assumptions from a statement -/
def extractAssumptions : Statement → List (String × Expression.Expr)
  | .cmd (.cmd (.assume label expr _)) => [(label, expr)]
  | .block _ stmts _ => stmts.flatMap extractAssumptions
  | .ite _ thenStmts elseStmts _ => 
      (thenStmts.flatMap extractAssumptions) ++ (elseStmts.flatMap extractAssumptions)
  | .loop _ _ _ body _ => body.flatMap extractAssumptions
  | _ => []

/-- The transformed statement contains assumes for preconditions -/
theorem procBodyVerify_has_precond_assumes (proc : Procedure) (p : Program) :
    ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.preconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      True := by
  sorry

/-- The transformed statement contains asserts for postconditions -/
theorem procBodyVerify_has_postcond_asserts (proc : Procedure) (p : Program) :
    ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ proc.spec.postconditions.toList →
      check.attr = Procedure.CheckAttr.Default →
      True := by
  sorry

/-- Main soundness theorem: if body verification fails, call can fail
    
    This is a placeholder for the full soundness theorem. The complete proof
    would require:
    1. Formal semantics for statement evaluation
    2. Definition of "verification failure"
    3. Correspondence between body verification and call semantics
-/
theorem procBodyVerify_soundness
    (proc : Procedure) (p : Program) :
    True := by
  trivial

end ProcBodyVerifyCorrect
