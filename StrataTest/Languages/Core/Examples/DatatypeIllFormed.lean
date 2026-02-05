/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Ill-Formed Datatype Tests

Tests that the Core typechecker correctly rejects ill-formed datatype declarations:
- Non-strictly positive occurrences
- Nested datatypes
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
info: error: (669-710) Error in constructor MkBad: Non-strictly positive occurrence of Bad in type (arrow Bad int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonStrictlyPositivePgm) |>.fst)

---------------------------------------------------------------------
-- Test 2: Nested Datatype
---------------------------------------------------------------------

def nestedDatatypePgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

// Nest appears nested inside List
datatype Nest (a : Type) { Base(), MkNest(xs: List (Nest a)) };
#end

/--
info: error: (1288-1351) Error in constructor MkNest: Datatype Nest appears nested inside (List (Nest a)). Nested datatypes are not supported in Strata Core.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nestedDatatypePgm) |>.fst)

end Strata.DatatypeIllFormedTest
