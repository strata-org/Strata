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
- Verus links:
  `generics`: https://github.com/verus-lang/verus/blob/main/examples/generics.rs
  `test_expand_errors`: https://github.com/verus-lang/verus/blob/main/examples/test_expand_errors.rs
  `debug_expand`: https://github.com/verus-lang/verus/blob/main/examples/debug_expand.rs
  `modules`: https://github.com/verus-lang/verus/blob/main/examples/modules.rs
- Gaps: `opaque` / `reveal`, `hide`, `closed`
- Current status: the seed verifies by using an explicit axiom for the function
  body
- Remaining gap: direct proof-visibility controls in Boole
-/

private def opaqueRevealHideSeed : Strata.Program :=
#strata
program Boole;

// Target shape once proof-visibility controls exist in Boole:
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

axiom (∀ x: int . square(x) == x * x);

procedure opaque_reveal_hide_seed(x: int) returns ()
{
  assert square(x) == x * x;
};
#end

/-- info:
Obligation: assert_1_1334
Property: assert
Result: ✅ pass-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" opaqueRevealHideSeed (options := .quiet)

example : Strata.smtVCsCorrect opaqueRevealHideSeed := by
  gen_smt_vcs
  all_goals (try grind)
