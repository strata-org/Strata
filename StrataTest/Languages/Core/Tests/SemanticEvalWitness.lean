/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.StatementSemantics
import Strata.DL.Lambda.Semantics
import all Strata.DL.Lambda.LExprEvalProps

/-!
# A concrete evaluator satisfying the semantic well-formedness conditions

`EvalCommand.call_sem` requires the Core's expression evaluator to satisfy
`WellFormedSemanticEvalVal` and `WellFormedSemanticEvalVar` simultaneously.

The two conditions are jointly satisfiable because they only constrain
value-only stores (`WellFormedStore`): on such a store the free-variable lookup
returns a value, so it agrees with the "every output is a value" requirement.
-/

namespace Core

open Imperative
open _root_.Lambda (LExpr LConst)

/-- Corollary: the well-formedness conditions are jointly satisfiable. -/
theorem exists_wf_coreEval (f : Expression.Factory) :
    WellFormedSemanticEvalVar (P := Expression) f ∧ WellFormedSemanticEvalVal (P := Expression) f :=
  ⟨coreEvaluator_WellFormedSemanticEvalVar f, coreEvaluator_WellFormedSemanticEvalVal f⟩


end Core
