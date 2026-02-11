/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier
import Strata.Transform.CallElim


---------------------------------------------------------------------
namespace Strata


def duplicateAssumes : Program :=
#strata
program Core;


procedure Double(n : int) returns (result : int)
spec {
  ensures [double_correct]: (result == n * 2);
}
{
  assume [test]: (n >= 2);
  assume [test]: (n >= 0);
  result := n + n;
  assert [after_double_internal]: (result >= 4);
};
#end


/-

info: [Strata.Core] Type checking succeeded.
-/
#guard_msgs in
#eval verify "cvc5" duplicateAssumes (options := .default)

---------------------------------------------------------------------
