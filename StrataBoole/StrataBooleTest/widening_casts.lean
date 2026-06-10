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

Gap #6 implemented: `e as_int` lowers to native `Bv{n}.ToUInt` Core op → SMT-LIB 2.7 `ubv_to_int`.
No axioms injected.
-/

private def wideningCastsSeed : StrataDDM.Program :=
#strata
program Boole;

// `v[i] as_int` lowers to `Bv32.ToUInt` Core op → SMT-LIB 2.7 `ubv_to_int`.
procedure widening_cast_seed(v: Map int bv32, n: int) returns ()
spec {
  requires 0 <= n;
  ensures ∀ i: int . 0 <= i && i < n ==> 0 <= (v[i] as_int);
}
{
  assert ∀ i: int . 0 <= i && i < n ==> 0 <= (v[i] as_int);
};
#end

/-- info:
Obligation: assert_2_1005
Property: assert
Result: ✅ pass

Obligation: widening_cast_seed_ensures_1_937
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" wideningCastsSeed (options := .quiet)
