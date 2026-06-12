/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-!
## choose-function declarations

`function f(params) : R := choose z . pred(z, params);` declares an
uninterpreted function f together with the axiom:
  ∀ params, ∀ z, z = f(params) → pred(z, params)

This lets a specification define a function by its property rather than its
implementation — similar to Verus `choose`-based spec functions.

Design notes
- `f` is emitted as an uninterpreted Core function (no body).
- The axiom uses a 3-forall form: ∀ params, ∀ z, (z = f(params)) → pred(z, params),
  which avoids de Bruijn index shifting and is logically equivalent to the direct
  ∀ params, pred(f(params), params) form.
-/

private def chooseFnSeed : StrataDDM.Program :=
#strata
program Boole;

function good(z: int, x: int) : bool;

function best(x: int) : int :=
  choose z : int . good(z, x);

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
Obligation: test_choose_fn_ensures_1_1052
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" chooseFnSeed (options := .quiet)
