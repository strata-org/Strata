/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Ill-Formed Datatype Tests

Tests that the Core typechecker correctly rejects ill-formed datatype declarations:
- Duplicate datatype names across declarations
- Non-strictly positive occurrences
- Non-uniform type applications
-/

namespace Strata.DatatypeIllFormedTest

---------------------------------------------------------------------
-- Test 1: Non-Strictly Positive Occurrence
---------------------------------------------------------------------

def nonStrictlyPositivePgm : Program :=
#strata
program Core;

datatype OK {mkOK(x: int)};

// Bad appears in negative position (left of arrow)
datatype Bad () { MkBad(f: Bad -> int) };
#end

/--
info: error: (0, (0-0)) Error in constructor MkBad: Non-strictly positive occurrence of Bad in type (arrow Bad int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonStrictlyPositivePgm) |>.fst)

end Strata.DatatypeIllFormedTest
