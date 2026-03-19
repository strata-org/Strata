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
- Gap: mutual recursion / forward references
-/

private def mutualRecursionSeed : Strata.Program :=
#strata
program Boole;

// Target shape once forward references are accepted:
//
// rec function even(n: int) : bool
// {
//   if n == 0 then true else odd(n - 1)
// }
//
// rec function odd(n: int) : bool
// {
//   if n == 0 then false else even(n - 1)
// }

function odd_stub(n: int) : bool;
function even_stub(n: int) : bool;

//rec function even(n: int) : bool
//{
//  // TODO(feature:mutual-recursion): use `odd(n - 1)` once forward references work.
//  if n == 0 then true else odd_stub(n - 1)
//}

procedure mutual_recursion_seed(n: int) returns ()
spec {
  requires 0 <= n;
  ensures even_stub(n) || odd_stub(n);
}
{
  assert even_stub(n) || odd_stub(n);
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" mutualRecursionSeed

example : Strata.smtVCsCorrect mutualRecursionSeed := by
  gen_smt_vcs
  all_goals (try grind)
