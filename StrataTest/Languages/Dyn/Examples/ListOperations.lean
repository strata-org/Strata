/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Dyn.Dyn
import Strata.DDM.Integration.Lean.HashCommands

meta section

namespace Strata
namespace Dyn

def ListOpsPgm :=
#strata
program Dyn;

def test_list_ops (dummy : Any) -> Any
{
  var result : Any;
  result = [];
  return result;
}

#end

end Dyn
end Strata
