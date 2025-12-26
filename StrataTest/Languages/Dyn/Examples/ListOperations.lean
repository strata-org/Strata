/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

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
