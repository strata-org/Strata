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

var x : int;

procedure Helper(n : int) returns (result : int)
spec {
  // NOTE: This precondition is not satisfied in MainProc.
  requires [n_positive]: (n > 0);
  ensures [result_correct]: (result == n * 2);
}
{
  result := n + n;
};

procedure MainProc() returns (output : int)
spec {
  modifies x;
  requires [x_nonneg]: (x >= 0);
  ensures [output_property]: (output == old(x) * 4);
}
{
  call output := Helper(x);
  call output := Helper(output);
};

procedure IndependentProc() returns (y : int)
spec {
  ensures [y_value]: (y == 42);
}
{
  y := 42;
};

procedure UnusedProc() returns (z : int)
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
Result: ❌ fail

Obligation: output_property
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" selectiveVerificationPgm
        (options := Options.quiet)
        (proceduresToVerify := (some ["MainProc"]))

--------- Verify all procedures (default behavior)

/--
info:
Obligation: result_correct
Property: assert
Result: ✅ pass

Obligation: (Origin_Helper_Requires)n_positive
Property: assert
Result: ❌ fail

Obligation: (Origin_Helper_Requires)n_positive
Property: assert
Result: ❌ fail

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
#eval verify "cvc5" selectiveVerificationPgm (options := Options.quiet)

---------- Verify only IndependentProc

/--
info:
Obligation: y_value
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" selectiveVerificationPgm
        (options := Options.quiet)
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
#eval verify "cvc5" selectiveVerificationPgm
          (options := Options.quiet)
          (proceduresToVerify := (some ["IndependentProc", "UnusedProc"]))

---------------------------------------------------------------------

end Strata
