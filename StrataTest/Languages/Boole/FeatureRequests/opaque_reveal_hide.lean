/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:generics`
- `verus-examples:test_expand_errors`
- `verus-examples:debug_expand`
- `verus-examples:modules`
- Gaps: `opaque` / `reveal`, `hide`, `closed`
-/

private def opaqueRevealHideSeed : Strata.Program :=
#strata
program Boole;

// Target shape once these proof-visibility controls exist directly in Boole:
//
// opaque function square(x: int) : int { x * x }
//
// procedure opaque_reveal_hide_seed(x: int) returns ()
// {
//   reveal square;
//   assert square(x) == x * x;
//   hide square;
// };

function square(x: int) : int;

axiom (forall x: int :: square(x) == x * x);

procedure opaque_reveal_hide_seed(x: int) returns ()
{
  // TODO(feature:opaque-reveal): treat `square` as opaque by default.
  // TODO(feature:hide): let a proof step reveal and then re-hide the body.
  // TODO(feature:closed): keep the body hidden across module boundaries.
  assert square(x) == x * x;
};
#end

#eval Strata.Boole.verify "cvc5" opaqueRevealHideSeed

example : Strata.smtVCsCorrect opaqueRevealHideSeed := by
  gen_smt_vcs
  all_goals (try grind)
