/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

def selectiveVerificationPgm : Program :=
#strata
program Core;

procedure Helper(n : int, out result : int)
spec {
  // NOTE: This precondition is not satisfied in MainProc.
  requires [n_positive]: (n > 0);
  ensures [result_correct]: (result == n * 2);
}
{
  result := n + n;
};

procedure MainProc(x : int, out output : int)
spec {
  requires [x_nonneg]: (x >= 0);
  ensures [output_property]: (output == x * 4);
}
{
  call Helper(x, out output);
  call Helper(output, out output);
};

procedure IndependentProc(out y : int)
spec {
  ensures [y_value]: (y == 42);
}
{
  y := 42;
};

procedure UnusedProc(out z : int)
spec {
  ensures [z_value]: (z == 100);
}
{
  z := 100;
};
#end

----------- Verify only MainProc; imports contracts of Helper

/--
info:
Obligation: callElimAssert_n_positive_6
Property: assert
Result: ❌ fail

Obligation: callElimAssert_n_positive_2
Property: assert
Result: ❓ unknown

Obligation: output_property
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify selectiveVerificationPgm
        (options := .quiet)
        (proceduresToVerify := (some ["MainProc"]))

--------- Verify all procedures (default behavior)

/--
info:
Obligation: result_correct
Property: assert
Result: ✅ pass

Obligation: callElimAssert_n_positive_6
Property: assert
Result: ❌ fail

Obligation: callElimAssert_n_positive_2
Property: assert
Result: ❓ unknown

Obligation: output_property
Property: assert
Result: ✅ pass

Obligation: y_value
Property: assert
Result: ✅ pass

Obligation: z_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify selectiveVerificationPgm (options := .quiet)

---------- Verify only IndependentProc

/--
info:
Obligation: y_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify selectiveVerificationPgm
        (options := .quiet)
        (proceduresToVerify := ["IndependentProc"])

---------- Verify multiple specific procedures

/--
info:
Obligation: y_value
Property: assert
Result: ✅ pass

Obligation: z_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify selectiveVerificationPgm
          (options := .quiet)
          (proceduresToVerify := (some ["IndependentProc", "UnusedProc"]))

---------------------------------------------------------------------

end Strata
