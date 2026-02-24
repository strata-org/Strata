/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Format
import Strata.Languages.B3.DDMTransform.DefinitionAST
import Strata.DL.SMT.Solver

/-!
# B3 Verification Diagnosis

Simple diagnosis for failed B3 verification checks.
-/

namespace B3.Verifier

open Strata

structure DiagnosedFailure where
  expression : B3AST.Expression SourceRange
  message : String

structure DiagnosisResult where
  diagnosedFailures : List DiagnosedFailure
  pathCondition : List (B3AST.Expression SourceRange)

/-- Split conjunction into list of conjuncts -/
def flattenConjunction : B3AST.Expression SourceRange → List (B3AST.Expression SourceRange)
  | .binaryOp _ (.and _) lhs rhs => flattenConjunction lhs ++ flattenConjunction rhs
  | expr => [expr]
  termination_by e => SizeOf.sizeOf e

end B3.Verifier
