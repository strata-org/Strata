/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Boogie.DDMTransform.Parse
import Strata.Languages.Boogie.Verifier
import Strata.Languages.Python.BoogiePrelude

namespace Strata
namespace Python
namespace Internal

def Boogie.prelude : Boogie.Program := Strata.Boogie.prelude

end Internal
end Python
end Strata
