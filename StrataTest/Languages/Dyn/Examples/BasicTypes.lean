/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def BasicTypesPgm :=
#strata
program Dyn;

def test_basic_types (dummy : Any) -> Any
{
  var y : Any;
  y = int_to_Any(42);
  return y;
}

#end

end Dyn
end Strata
