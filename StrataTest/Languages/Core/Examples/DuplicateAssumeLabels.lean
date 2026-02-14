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


/--
info: [Strata.Core] Type checking succeeded.

⚠️ [addPathCondition] Label clash detected for test, using unique label test_1.

VCs:
Label: after_double_internal
Property: assert
Assumptions:
(test, (~Int.Ge $__n0 #2))
(test_1, (~Int.Ge $__n0 #0))

Proof Obligation:
(~Int.Ge (~Int.Add $__n0 $__n0) #4)

Label: double_correct
Property: assert
Assumptions:
(test, (~Int.Ge $__n0 #2))
(test_1, (~Int.Ge $__n0 #0))

Proof Obligation:
((~Int.Add $__n0 $__n0) == (~Int.Mul $__n0 #2))

---
info:
Obligation: after_double_internal
Property: assert
Result: ✅ pass

Obligation: double_correct
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" duplicateAssumes (options := .default)

---------------------------------------------------------------------
