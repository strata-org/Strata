/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:fun_ext`
- `verus-examples:trait_for_fn`
- Verus links:
  `fun_ext`: https://github.com/verus-lang/verus/blob/main/examples/fun_ext.rs
  `trait_for_fn`: https://github.com/verus-lang/verus/blob/main/examples/trait_for_fn.rs

Implemented:
- `fun x : T => body` parses as Core's `lambda` op and lowers to a Core
  `.abs` node via `toCoreExpr`.
- `(f)(x)` parses as Core's `apply_expr` op and lowers to `.app`.
- Arrow type `T -> U` lowers to Core `.arrow`.

Remaining gap:
- Higher-order function *values* stored in variables (e.g.
  `var f : int -> int`) and passed as procedure arguments still require
  the abstract-type encoding for the SMT path — the lambda syntax works
  in spec expression positions but the full higher-order value story
  (assignment, procedure parameters of function type) needs more work.
-/

private def lambdaClosureSeed : Strata.Program :=
#strata
program Boole;

// Lambda in a spec (ensures) position: `(fun x : int => x + 1)(2) == 3`
// uses Core's `lambda` for abstraction and `apply_expr` for application.
procedure use_lambda() returns ()
spec {
  ensures (fun x : int => x + 1)(2) == 3;
}
{
  assert (fun x : int => x + 1)(2) == 3;
};

// Higher-order spec function: takes a function value as an abstract type
// (still needed for passing functions as arguments — open gap).
type FnIntInt;
function apply(f: FnIntInt, x: int) : int;
const add1 : FnIntInt;
axiom (∀ x: int . apply(add1, x) == x + 1);

procedure higher_order_seed(f: FnIntInt, x: int) returns (y: int)
spec {
  ensures y == apply(f, x);
}
{
  y := apply(f, x);
};
#end

/-- info:
Obligation: assert_1_1330
Property: assert
Result: ✅ pass

Obligation: use_lambda_ensures_0_1284
Property: assert
Result: ✅ pass

Obligation: higher_order_seed_ensures_3_1718
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" lambdaClosureSeed (options := .quiet)

example : Strata.smtVCsCorrect lambdaClosureSeed := by
  gen_smt_vcs
  all_goals (try grind)
