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

Remaining gap:
- Mutual recursion over `int` (or other non-datatype types) is not yet
  supported. Structural recursion does not apply; an explicit `decreases`
  clause would be needed for each function in the block, and the
  infrastructure for that is not yet in place.
-/

-- Working: mutual recursion over a Peano-style datatype.
-- `even` calls `odd` and vice versa; both terminate by structural recursion
-- on the `@[cases]` MyNat parameter.
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

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed

example : Strata.smtVCsCorrect mutualRecursionSeed := by
  gen_smt_vcs
  all_goals (try grind)

-- Still open: mutual recursion over int requires a decreases clause.
-- Target shape once function-level decreases is supported:
--
-- rec
-- function even_int(n: int) : bool
-- {
--   if n == 0 then true else odd_int(n - 1)
-- }
-- function odd_int(n: int) : bool
-- {
--   if n == 0 then false else even_int(n - 1)
-- }
-- ;
