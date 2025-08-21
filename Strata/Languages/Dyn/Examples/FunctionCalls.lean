/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Dyn.Dyn

namespace Strata
namespace Dyn

def FunctionCallsPgm :=
#strata
program Dyn;

def test_fun (dummy : Any) -> Any
{
  return int_to_Any(0);
}

def test_fun_as_val (dummy : Any) -> Any
{
  var my_fun : Any;

  return call(my_fun, int_to_Any(20));
}

def apply_twice(f: Any, arg: Any) -> Any
{
  return call(f, call(f, arg));
}

def test_apply_twice(dummy : Any) -> Any
{
  var x : Any;
  x = int_to_Any(0);
  return call(fun_to_Any(apply_twice), test_fun, x);
}

#end

end Dyn
end Strata

-- my_fun = test_fun;
