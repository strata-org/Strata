/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.StatementSemantics
import Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.LExprEvalProps

/-!
# Concrete evaluator witnesses for semantic well-formedness

The Core evaluator satisfies `WellFormedSemanticEvalVal` and
`WellFormedSemanticEvalVar` simultaneously for every factory. These witnesses
discharge generic Imperative metatheory premises about value-producing
evaluation and free-variable lookup on well-formed stores.
-/

namespace Core

open Imperative
open _root_.Lambda (LExpr LConst)

/-- Corollary: the well-formedness conditions are jointly satisfiable. -/
theorem exists_wf_coreEval (f : Expression.Factory) :
    WellFormedSemanticEvalVar (P := Expression) f ∧ WellFormedSemanticEvalVal (P := Expression) f :=
  ⟨coreEvaluator_WellFormedSemanticEvalVar f, coreEvaluator_WellFormedSemanticEvalVal f⟩


end Core
