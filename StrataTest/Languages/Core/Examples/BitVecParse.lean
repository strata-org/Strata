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
Obligation:
true

Label: bitvec64_test
Property: assert
Obligation:
false



Result: Obligation: bitvec64_test
Property: assert
Result: ❌ fail


[DEBUG] Evaluated program:
program Core;

procedure bitVecParseTest () returns ()
{
  assert [bitvec32_test]: bv{32}(4294945741) == bv{32}(4294945741);
  assert [bitvec64_test]: bv{64}(68719455181) == bv{64}(4294945741);
  };

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
#eval verify pgm

---------------------------------------------------------------------
