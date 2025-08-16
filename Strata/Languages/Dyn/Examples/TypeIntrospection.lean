/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def TypeIntrospectionPgm :=
#strata
program Dyn;

def test_type_ops (dummy : Any) -> Any
{
  var result : int;
  result = 0;
  return bool_to_Any((str_to_Any(typeof(result)) == str_to_Any("string")));
}

#end

end Dyn
end Strata
