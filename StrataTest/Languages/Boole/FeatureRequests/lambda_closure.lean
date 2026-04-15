/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Local reduced Rust/Verus-style lambda example:

proof fn use_lambda() {
    let f: spec_fn(int) -> int = |x: int| x + 1;
    assert(f(2) == 3);
}

- Gap: direct lambda / closure support
- Current status: the seed verifies by naming the closure value explicitly and
  axiomatizing its behavior
- Remaining gap: parse and lower inline `fun x: int => x + 1` closures
  directly in Boole
-/

private def lambdaClosureSeed : Strata.Program :=
#strata
program Boole;

// Target shape:
//
// procedure use_lambda() returns ()
// {
//   var f : int -> int;
//   f := fun x: int => x + 1;
//   assert f(2) == 3;
// };

type FnIntInt;

function apply(f: FnIntInt, x: int) : int;
const add1 : FnIntInt;

axiom (∀ x: int . apply(add1, x) == x + 1);

procedure use_lambda() returns ()
{
  var f : FnIntInt;
  f := add1;
  assert apply(f, 2) == 3;
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" lambdaClosureSeed

example : Strata.smtVCsCorrect lambdaClosureSeed := by
  gen_smt_vcs
  all_goals (try grind)
