/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:trigger_loops` (`choose_example`, `quantifier_example`)
- Verus link:
  `trigger_loops`: https://github.com/verus-lang/verus/blob/main/examples/trigger_loops.rs
- Status: implemented — `w := ε z: T . pred(z)` desugars to:
    assert ∃ z : T . pred(z);   -- existence obligation (soundness guard)
    havoc w;
    assume pred[z/w];
  The existence assertion prevents `assume false` false positives when
  `pred` is unsatisfiable.
-/

private def chooseOperatorSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

procedure choose_seed(x: int) returns (w: int)
spec {
  requires ∃ z: int . good(z, x);
  ensures good(w, x);
}
{
  w := ε z: int . good(z, x);
};
#end

/-- info:
Obligation: choose_2_879_exists
Property: assert
Result: ✅ pass

Obligation: choose_seed_ensures_1_853
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseOperatorSeed (options := .quiet)

example : Strata.smtVCsCorrectBoole chooseOperatorSeed := by
  gen_smt_vcs_boole
  all_goals (try grind)

-- Regression: an unsatisfiable predicate must be caught by the existence
-- assertion, not silently turned into `assume false` (which would make every
-- subsequent obligation a false positive).
private def chooseUnsatSeed : StrataDDM.Program :=
#strata
program Boole;

procedure choose_unsat() returns (w: int)
spec {
  ensures true;
}
{
  w := ε z: int . z != z;
};
#end

/-- info:
Obligation: choose_1_1603_exists
Property: assert
Result: ❌ fail

Obligation: choose_unsat_ensures_0_1583
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseUnsatSeed (options := .quiet)

/-!
## choose-function declarations

`function f(params) : R := ε z . pred(z, params);` declares an uninterpreted
function `f` together with the axiom:
  ∀ params, ∀ z, z = f(params) → pred(z, params)

This lets a specification define a function by its property rather than its
implementation — similar to Verus choose-based spec functions.

Note: unlike `w := ε z . pred(z)` (which guards soundness with an existence
assertion), the function form emits the axiom unconditionally. The user must
ensure `pred` is satisfiable for all inputs (e.g. via a precondition) to avoid
an unsound axiom.
-/

private def chooseFnSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

function best(x: int) : int :=
  ε z : int . good(z, x);

procedure test_choose_fn(x: int) returns (w: int)
spec {
  requires ∃ z: int :: good(z, x);
  ensures good(w, x);
}
{
  w := best(x);
};
#end

/-- info:
Obligation: test_choose_fn_ensures_1_2749
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseFnSeed (options := .quiet)

-- Without the ∃ precondition the ensures still passes, because the axiom
-- `∀ z, z = best(x) → good(z, x)` unconditionally asserts good(best(x), x).
-- This demonstrates that soundness relies on the caller supplying the witness.
private def chooseFnNoPrecondSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

function best(x: int) : int :=
  ε z : int . good(z, x);

procedure test_no_precond(x: int) returns (w: int)
spec {
  ensures good(w, x);
}
{
  w := best(x);
};
#end

/-- info:
Obligation: test_no_precond_ensures_0_3444
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseFnNoPrecondSeed (options := .quiet)
