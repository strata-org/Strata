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

/- Boogie -/
import Strata.Languages.Boogie.Examples.Examples
import Strata.Languages.Boogie.StatementSemantics

/- CSimp -/
import Strata.Languages.C_Simp.Examples.Examples

/- Code Transforms -/
import Strata.Transform.Examples
import Strata.Transform.CallElimCorrect
import Strata.Transform.DetToNondetCorrect
