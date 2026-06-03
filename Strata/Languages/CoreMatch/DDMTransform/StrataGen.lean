/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Grammar
meta import Strata.DDM.Integration.Lean

public section

namespace Strata.CoreMatchDDM

set_option maxHeartbeats 800000 in
#strata_gen CoreMatch

end Strata.CoreMatchDDM
