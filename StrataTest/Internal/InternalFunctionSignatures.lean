/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Boogie
import Strata.Languages.Python.FunctionSignatures

namespace Strata
namespace Python
namespace Internal

-- We should extract the function signatures from the prelude:
def getFuncSigOrder (fname: String) : List String :=
  match fname with
  | _ => Strata.Python.getFuncSigOrder fname

-- We should extract the function signatures from the prelude:
def getFuncSigType (fname: String) (arg: String) : String :=
  match fname with
  | _ => Strata.Python.getFuncSigType fname arg

end Internal
end Python
end Strata
