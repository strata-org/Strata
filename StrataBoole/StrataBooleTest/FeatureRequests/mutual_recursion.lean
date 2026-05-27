/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/recursion`
- `vlir-tests:mutual_recursion`
- `vlir-tests:recursion`
- Verus link:
  `guide/recursion`: https://github.com/verus-lang/verus/blob/main/examples/guide/recursion.rs

Implemented (#599):
- Mutual recursion for spec functions over datatypes works end-to-end.
  The `rec function ... function ... ;` block pre-registers all sibling
  names before elaborating any body, so forward references are resolved.
  Termination is justified by structural recursion on the `@[cases]` param.

Remaining gap:
- Mutual recursion over `int` (or other non-datatype types) is not yet
  supported. Structural recursion does not apply; an explicit `decreases`
  clause would be needed for each function in the block, and the
  infrastructure for that is not yet in place.
-/

private def mutualRecursionSeed : Strata.Program :=
#strata
program Boole;

datatype MyNat () { Zero(), Succ(pred: MyNat) };

rec
function even(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then true else odd(MyNat..pred(n))
}
function odd(@[cases] n : MyNat) : bool
{
  if MyNat..isZero(n) then false else even(MyNat..pred(n))
}
;

procedure test_parity() returns ()
spec {
  ensures even(Zero()) == true;
  ensures odd(Zero()) == false;
  ensures even(Succ(Zero())) == false;
  ensures odd(Succ(Zero())) == true;
}
{
  assert even(Zero()) == true;
  assert odd(Zero()) == false;
  assert even(Succ(Zero())) == false;
  assert odd(Succ(Zero())) == true;
};
#end

/--
info:
Obligation: even_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: odd_body_calls_MyNat..pred_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: assert_4_1504
Property: assert
Result: ✅ pass

Obligation: assert_5_1535
Property: assert
Result: ✅ pass

Obligation: assert_6_1566
Property: assert
Result: ✅ pass

Obligation: assert_7_1604
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_0_1360
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_1_1392
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_2_1424
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_3_1463
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole mutualRecursionSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)

