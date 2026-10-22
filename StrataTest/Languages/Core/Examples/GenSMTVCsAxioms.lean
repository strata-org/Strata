/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands
import Strata.MetaVerifier

open StrataDDM (Program)
---------------------------------------------------------------------
/-!
## Axioms used by `gen_smt_vcs`

`gen_smt_vcs` expands `smtVCsCorrect p` into one subgoal per VC. The subgoals
are built by `translateQuery`, and for each VC the tactic also proves that the
subgoal is the denotation of the VC, so `translateQuery` is not trusted.
Beyond the standard axioms, the proof only depends on `Lean.ofReduceBool` and
`Lean.trustCompiler`, used to evaluate VC generation, and on
`Core.WFFactory._native.native_decide.ax_1`, which comes from Strata's factory
rather than from this tactic.

If the proof cannot be produced for some VC, the tactic fails, naming the VC.
-/
namespace Strata

private def minPgm : Program :=
#strata
program Core;

procedure min(n : int, m : int, out k : int)
spec {
  ensures (int.le(k, n) && int.le(k, m));
}
{
  k := if int.lt(n, m) then n else m;
  k := k;
};
#end

theorem minCorrect : smtVCsCorrect minPgm := by
  gen_smt_vcs
  grind

/--
info: 'Strata.minCorrect' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝]
-/
#guard_msgs in
#print axioms minCorrect

/-! Uninterpreted sorts are covered by the proof-producing translation. -/

private def sortPgm : Program :=
#strata
program Core;
type T;
function f(x : T) : int;
axiom [f_pos]: forall x : T :: int.gt(f(x), 0);
procedure p(x : T, out r : int)
spec {
  ensures int.gt(r, 0);
}
{
  r := f(x);
};
#end

theorem sortCorrect : smtVCsCorrect sortPgm := by
  gen_smt_vcs
  all_goals grind

/--
info: 'Strata.sortCorrect' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝]
-/
#guard_msgs in
#print axioms sortCorrect

/-! Bitvectors are covered as well. -/

private def bvPgm : Program :=
#strata
program Core;
procedure q(x : bv W8, out r : bv W8)
spec {
  ensures r == x;
}
{
  r := bv8.add(x, bv{8}(0));
};
#end

theorem bvCorrect : smtVCsCorrect bvPgm := by
  gen_smt_vcs
  all_goals bv_decide

/--
info: 'Strata.bvCorrect' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 Core.WFFactory._native.native_decide.ax_1✝]
-/
#guard_msgs in
#print axioms bvCorrect

end Strata
---------------------------------------------------------------------
