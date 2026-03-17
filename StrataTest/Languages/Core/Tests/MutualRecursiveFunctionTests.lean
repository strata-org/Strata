/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Mutual Recursive Function Verification Tests

Tests mutually recursive functions (isEven/isOdd) over algebraic datatypes,
verifying parsing, translation, axiom-based SMT encoding, and end-to-end
verification.
-/

namespace Strata.MutualRecursiveFunctionTest

def mutualRecPgm : Program :=
#strata
program Core;

datatype MyNat { Zero(), Succ(pred: MyNat) };

rec function isEven (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else isOdd(MyNat..pred(n))
}
function isOdd (@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else isEven(MyNat..pred(n))
};

procedure TestMutual() returns ()
spec {
  ensures true;
}
{
  assert [zeroEven]: isEven(Zero()) == true;
  assert [zeroNotOdd]: isOdd(Zero()) == false;
  assert [oneOdd]: isOdd(Succ(Zero())) == true;
  assert [oneNotEven]: isEven(Succ(Zero())) == false;
};
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mutualRecPgm) |>.snd |>.isEmpty

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: isEven_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero($__n0)) ==> MyNat..isSucc($__n0)

Label: isOdd_body_calls_MyNat..pred_0
Property: assert
Obligation:
!(MyNat..isZero($__n1)) ==> MyNat..isSucc($__n1)

Label: zeroEven
Property: assert
Obligation:
true

Label: zeroNotOdd
Property: assert
Obligation:
true

Label: oneOdd
Property: assert
Obligation:
true

Label: oneNotEven
Property: assert
Obligation:
true

Label: TestMutual_ensures_0
Property: assert
Obligation:
true

---
info: Obligation: isEven_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: zeroEven
Property: assert
Result: ✅ pass

Obligation: zeroNotOdd
Property: assert
Result: ✅ pass

Obligation: oneOdd
Property: assert
Result: ✅ pass

Obligation: oneNotEven
Property: assert
Result: ✅ pass

Obligation: TestMutual_ensures_0
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval verify mutualRecPgm (options := .default)

end Strata.MutualRecursiveFunctionTest
