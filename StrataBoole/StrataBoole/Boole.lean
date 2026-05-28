/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataBoole.Grammar -- shake: keep
import StrataDDM.Integration.Lean.Gen -- shake: keep

public section

namespace Strata.BooleDDM

set_option maxHeartbeats 400000 in
-- set_option trace.Strata.generator true in
#strata_gen Boole

end Strata.BooleDDM

namespace Strata

open StrataDDM (SourceRange)

abbrev Boole.Type := BooleDDM.BooleType SourceRange
abbrev Boole.Expr := BooleDDM.Expr SourceRange
abbrev Boole.Program := BooleDDM.Program SourceRange

end Strata
