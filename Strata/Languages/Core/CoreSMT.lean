/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SolverInterface
import Strata.DL.SMT.State
import Strata.Languages.Core.CoreSMT.IsCoreSMT
import Strata.Languages.Core.CoreSMT.ExprTranslator
import Strata.Languages.Core.CoreSMT.StmtVerifier
import Strata.Languages.Core.CoreSMT.Diagnosis
import Strata.Languages.Core.CoreSMT.Verifier

namespace Strata.Core.CoreSMT

-- Type aliases for backward compatibility
abbrev CoreSMTState := SMT.VerifierState
abbrev CoreSMTConfig := SMT.VerifierConfig

end Strata.Core.CoreSMT
