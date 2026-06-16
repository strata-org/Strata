/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/integers`
- `verus-examples:quantifiers`
- `verus-examples:statements`
- Verus links:
  `guide/integers`: https://github.com/verus-lang/verus/blob/main/examples/guide/integers.rs
  `quantifiers`: https://github.com/verus-lang/verus/blob/main/examples/quantifiers.rs
  `statements`: https://github.com/verus-lang/verus/blob/main/examples/statements.rs

Gap #6 implemented: `as_uint(e)` lowers to native `Bv{n}.ToUInt` Core op → SMT-LIB 2.7 `ubv_to_int`.
No axioms injected.
-/

private def wideningCastsSeed : StrataDDM.Program :=
#strata
program Boole;

// `as_uint(v[i])` lowers to `Bv32.ToUInt` Core op → SMT-LIB 2.7 `ubv_to_int`.
procedure widening_cast_seed(v: Map int bv32, n: int) returns ()
spec {
  requires 0 <= n;
  ensures ∀ i: int . 0 <= i && i < n ==> 0 <= (as_uint(v[i]));
}
{
  assert ∀ i: int . 0 <= i && i < n ==> 0 <= (as_uint(v[i]));
};
#end

/-- info:
Obligation: assert_2_1011
Property: assert
Result: ✅ pass

Obligation: widening_cast_seed_ensures_1_941
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" wideningCastsSeed (options := .quiet)

/--
The VCs are provable regardless of `useArrayTheory`: under `true` the `Map` is
encoded as an SMT array (denoted by `SmtArray`), under `false` as an
uninterpreted sort with an axiomatized `select` function.
Since `as_uint` lowers to `ubv_to_int` (unsigned), the result is `Int.ofNat _`
which is always non-negative — no axiom required.
-/
example : ∀ useArrayTheory,
    Strata.smtVCsCorrectBoole wideningCastsSeed { useArrayTheory } := by
  intro useArrayTheory
  cases useArrayTheory
  case false =>
    gen_smt_vcs_boole
    all_goals
      intro Map inst n select v hn i hi
      exact Int.natCast_nonneg _
  case true =>
    gen_smt_vcs_boole
    all_goals
      intro n v hn i hi
      exact Int.natCast_nonneg _
