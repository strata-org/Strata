/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn
import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def TrivialPgm :=
#strata
program Dyn;

def trivial (x : Any) -> Any
{
  return int_to_Any(0);
}

#end

end Dyn
end Strata
