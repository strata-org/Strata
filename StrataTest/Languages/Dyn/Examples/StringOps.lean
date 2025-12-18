/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def StringOpsPgm :=
#strata
program Dyn;

def test_strings (dummy : Any) -> Any
{
  var greeting : Any;
  greeting = str_to_Any("Hello");
  return greeting;
}

#end

end Dyn
end Strata
