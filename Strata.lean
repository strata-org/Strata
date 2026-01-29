/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- This module serves as the root of the `Strata` library.

/- DDM -/
import Strata.DDM.Integration.Lean
import Strata.DDM.Ion

/- Dialect Library -/
import Strata.DL.SMT.SMT
import Strata.DL.Lambda.Lambda
import Strata.DL.Imperative.Imperative

/- Utilities -/
import Strata.Util.Sarif

/- Strata Core -/
import Strata.Languages.Core.StatementSemantics
import Strata.Languages.Core.SarifOutput

/- Backends -/
import Strata.Backends.CBMC.CProver
