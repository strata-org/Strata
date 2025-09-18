/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

private def pgm : Program :=
#strata
program Boogie;

procedure bitVecParseTest() returns () {

  assert [bitvec32_test]: (bv{32}(0xF_FFFF_ABCD) == bv{32}(0xFFFF_ABCD));
  assert [bitvec64_test]: (bv{64}(0xF_FFFF_ABCD) == bv{64}(0xFFFF_ABCD));

};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: bitvec32_test
Assumptions:


Proof Obligation:
#true

Label: bitvec64_test
Assumptions:


Proof Obligation:
#false

Wrote problem to vcs/bitvec64_test.smt2.


Obligation bitvec64_test: could not be proved!

Result: failed
CEx: ⏎

Evaluated program:
(procedure bitVecParseTest :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [bitvec32_test] #true
assert [bitvec64_test] #false

---
info:
Obligation: bitvec32_test
Result: verified

Obligation: bitvec64_test
Result: failed
CEx:
-/
#guard_msgs in
#eval verify "cvc5" pgm

---------------------------------------------------------------------
