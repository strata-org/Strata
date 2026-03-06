/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Expressions

/-!
# Core Diagnosis Types

Types for verification diagnosis results, used by the CoreSMT pipeline
and `Core.Verifier`.
-/

namespace Strata.Core

/-- Verification result for diagnosis -/
inductive DiagnosisResultType
  | refuted
  | counterexample
  | unknown
  deriving Repr, Inhabited

/-- Context for a diagnosed failure -/
structure DiagnosisContext where
  pathCondition : List Core.Expression.Expr := []
  deriving Inhabited

/-- Report for a diagnosed failure -/
structure DiagnosisReport where
  result : Except DiagnosisResultType Unit
  context : DiagnosisContext
  deriving Inhabited

/-- Result of diagnosing a single sub-expression -/
structure DiagnosedFailure where
  expression : Core.Expression.Expr
  isRefuted : Bool
  report : DiagnosisReport
  deriving Inhabited

/-- Full diagnosis result -/
structure DiagnosisResult where
  diagnosedFailures : List DiagnosedFailure
  statePathCondition : List Core.Expression.Expr := []
  deriving Inhabited

end Strata.Core
