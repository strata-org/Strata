/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

open Strata

/-
Near-upstream anchors from `differential_status.md`:
- `verus-examples:guide/ext_equal`
- Verus link:
  `guide/ext_equal`: https://github.com/verus-lang/verus/blob/main/examples/guide/ext_equal.rs
- Original gap: extensional equality lowered to ordinary equality
- Current status: implemented for direct `Map` types via Boole `=~=`
- Lowering: `a =~= b` becomes `∀ i . a[i] == b[i]`
- Remaining gap: named map synonyms and non-map extensional equality
-/

private def mapExtensionalitySeed : Strata.Program :=
#strata
program Boole;

// Implemented shape for direct `Map` types: `a =~= b` lowers to
// `∀ i: int . a[i] == b[i]`.
//
// spec {
//   requires ∀ i: int . a[i] == b[i];
//   ensures a =~= b;
// }

// TODO(feature:extensional-equality): normalize type synonyms so
// `type IntMap := Map int int` also works with `=~=`.
// TODO(feature:extensional-equality): extend the same idea to other collection
// types such as sequences once we settle the intended semantics.
// TODO(feature:extensional-equality): review quantified triggers/solver
// behavior as more extensional cases are added.

procedure map_extensionality_seed(a: Map int int, b: Map int int) returns ()
spec {
  requires ∀ i: int . a[i] == b[i];
  ensures a =~= b;
}
{
  assert a =~= b;
};
#end

#guard_msgs (drop info) in
#eval Strata.Boole.verify "cvc5" mapExtensionalitySeed

example : Strata.smtVCsCorrect mapExtensionalitySeed := by
  gen_smt_vcs
  all_goals
    intro Map inst select a b hPointwise i
    exact hPointwise i
