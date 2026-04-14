/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:proposal-rw2022`
- `verus-examples:rw2022_script`
- `verus-lang/verus:examples/recursion.rs`
- Verus links:
  `proposal-rw2022`: https://github.com/verus-lang/verus/blob/main/examples/proposal-rw2022.rs
  `rw2022_script`: https://github.com/verus-lang/verus/blob/main/examples/rw2022_script.rs
  `recursion`: https://github.com/verus-lang/verus/blob/main/examples/recursion.rs
- `vlir-tests:tests/LoopSimpleWithSpec`
- Status: loop-level `decreases` is available in the CST/Core path
- Remaining gap: function/procedure/spec-function `decreases`
-/

private def decreasesMetadataSeed : Strata.Program :=
#strata
program Boole;

// Target shape for the remaining gap:
//
// function dec_to_zero(n: int) : int
//   decreases n
// {
//   if n <= 0 then 0 else dec_to_zero(n - 1)
// }
//
// procedure call_dec_to_zero(n: int) returns (r: int)
//   decreases n
// {
//   r := dec_to_zero(n);
// }

procedure loop_measure_seed(n: int) returns (i: int)
spec {
  requires 0 <= n;
  ensures i == n;
}
{
  i := 0;
  while (i < n)
    decreases n - i
    invariant 0 <= i
    invariant i <= n
  {
    i := i + 1;
  }
};
#end

/-- info:
Obligation: entry_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0_1
Property: assert
Result: ✅ pass

Obligation: loop_measure_seed_ensures_1_1174
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" decreasesMetadataSeed (options:=.quiet)

example : Strata.smtVCsCorrect decreasesMetadataSeed := by
  gen_smt_vcs
  all_goals (try grind)
