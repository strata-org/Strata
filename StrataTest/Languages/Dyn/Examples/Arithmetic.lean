/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def ArithmeticPgm :=
#strata
program Dyn;

def test_arithmetic (dummy : Any) -> Any
{
  var sum : Any;
  sum = int_to_Any(1) + int_to_Any(2);
  return sum;
}

#end

end Dyn
end Strata
