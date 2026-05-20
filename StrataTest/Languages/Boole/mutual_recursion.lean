/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

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

Implemented (#1167):
- Mutual recursion over `int`: each function in a `rec` block may carry a
  `decreases` clause; termination VCs are discharged by cvc5.
  The functions remain opaque UFs in the SMT model, so concrete evaluation
  (e.g. `even(1) == false`) requires manual axioms.
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

/-- info:
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

Obligation: assert_4_1511
Property: assert
Result: ✅ pass

Obligation: assert_5_1542
Property: assert
Result: ✅ pass

Obligation: assert_6_1573
Property: assert
Result: ✅ pass

Obligation: assert_7_1611
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_0_1367
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_1_1399
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_2_1431
Property: assert
Result: ✅ pass

Obligation: test_parity_ensures_3_1470
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed (options := .quiet)

example : Strata.smtVCsCorrect mutualRecursionSeed := by
  gen_smt_vcs
  all_goals (try grind)

/-
Mutual recursion over int (#1167):
- `decreases n` on each function in the `rec` block; the termination VCs
  (`even_terminates_*`, `odd_terminates_*`) are discharged by cvc5.

Open gap — unfolding (Gap #1 / opaque+reveal):
- `even` and `odd` are emitted as uninterpreted functions (UFs) in the SMT
  query.  The solver knows their types and that they terminate, but not what
  they return at any specific argument.  Proving `even(1) == false` requires
  the defining equations as SMT assertions:
    ∀ n . n <= 0 ==> even(n) == true
    ∀ n . n >  0 ==> even(n) == odd(n - 1)
  (and symmetrically for `odd`).
- These are exactly the unfolding axioms that Dafny emits via `reveal` and
  that Verus controls via `opaque`/`reveal_with_fuel`.  The fix in Boole is
  to auto-emit them when `decreases` is present — bounded by a trigger on the
  function symbol to avoid infinite E-matching instantiation.
- Tracked as Gap #1 (`opaque`/`reveal`) in BooleFeatureRequests.md.
-/
private def mutualRecursionIntSeed : Strata.Program :=
#strata
program Boole;

rec
function even(n: int) : bool
  decreases n
{
  if n <= 0 then true else odd(n - 1)
}
function odd(n: int) : bool
  decreases n
{
  if n <= 0 then false else even(n - 1)
}
;
#end

/-- info:
Obligation: even_terminates_0
Property: assert
Result: ✅ pass

Obligation: even_terminates_1
Property: assert
Result: ✅ pass

Obligation: odd_terminates_0
Property: assert
Result: ✅ pass

Obligation: odd_terminates_1
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" mutualRecursionIntSeed (options := .quiet)
