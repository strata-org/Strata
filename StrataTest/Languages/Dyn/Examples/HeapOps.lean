/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def HeapOpsPgm :=
#strata
program Dyn;

def test_heap_ops (dummy : Any) -> Any
{
  var p : Any;
  p = alloc();
  var success : Any;
  success = write(p, int_to_Any(5));
  var x : Any;
  x = read(p);
  success = free(p);
  return success and bool_to_Any((x == int_to_Any(5)));
}

#end

end Dyn
end Strata
