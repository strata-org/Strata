/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boole.Grammar

namespace Strata.BooleDDM

-- set_option trace.Strata.generator true in
#strata_gen Boole

end Strata.BooleDDM

namespace Strata

abbrev Boole.Type := BooleDDM.BooleType SourceRange
abbrev Boole.Expr := BooleDDM.Expr SourceRange
abbrev Boole.Program := BooleDDM.Program SourceRange

end Strata
