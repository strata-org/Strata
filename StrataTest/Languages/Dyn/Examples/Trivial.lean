/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Dyn.Dyn
import StrataDDM.Integration.Lean.HashCommands

meta section

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
