/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.AST
import Strata.Languages.Core.DDMTransform.Parse
import Strata.Languages.Core.Verifier
import Strata.Languages.Python.CorePrelude

namespace Strata
namespace Python
namespace Internal

def Core.prelude : Core.Program := Strata.Core.prelude

end Internal
end Python
end Strata
