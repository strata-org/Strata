/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.WfLabelMapAgree
import Strata.Backends.CBMC.GOTO.CoreCFGToGOTOConcrete

/-! # Axiom check for R10a's `h_labelMap_agree` discharge

Pure smoke test — ensures the labelMap-agreement theorem and the
updated `_v6` end-to-end concrete forward simulation theorem elaborate
and tracks their axiom dependencies. -/

#print axioms CProverGOTO.WfLabelMapAgree.labelMap_agree_of_translator
#print axioms CProverGOTO.coreCFGToGotoTransform_forward_simulation_concrete_v6
