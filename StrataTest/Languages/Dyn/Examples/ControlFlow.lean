/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def ControlFlowPgm :=
#strata
program Dyn;

def test_control_flow (dummy : Any) -> Any
{
  var result : Any;
  result = int_to_Any(0);
  if (bool_to_Any(True)) {
    result = int_to_Any(1);
  } else {
    result = int_to_Any(2);
  }
  return result;
}

#end

end Dyn
end Strata
