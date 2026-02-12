/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

private def pgm : Program :=
#strata
program Core;

procedure bitVecParseTest() returns () {

  assert [bitvec32_test]: (bv{32}(0xF_FFFF_ABCD) == bv{32}(0xFFFF_ABCD));
  assert [bitvec64_test]: (bv{64}(0xF_FFFF_ABCD) == bv{64}(0xFFFF_ABCD));

};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: bitvec32_test
Property: assert
Assumptions:


Proof Obligation:
#true

Label: bitvec64_test
Property: assert
Assumptions:


Proof Obligation:
#false



Result: Obligation: bitvec64_test
Property: assert
Result: ❌ fail


Evaluated program:
procedure bitVecParseTest :  () → ()
  modifies: []
  preconditions: ⏎
  postconditions: ⏎
{
  assert [bitvec32_test] #true
  assert [bitvec64_test] #false
}
---
info:
Obligation: bitvec32_test
Property: assert
Result: ✅ pass

Obligation: bitvec64_test
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify "cvc5" pgm

---------------------------------------------------------------------
