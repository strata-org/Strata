/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core
public import StrataDDM.Integration.Lean.HashCommands
public import Strata.MetaVerifier
-- The tactic's elaborator runs at compile time, so it needs a `meta` import.
public meta import Strata.MetaVerifier

open StrataDDM (Program)
---------------------------------------------------------------------
/-!
## `gen_smt_vcs` inside a `module` file

In a `module` file the bodies of the denotation functions (`denoteQuery`,
`denoteTerm`, ...) are not visible to the kernel, so the goals cannot be
connected to `smtVCsCorrect` by unfolding. `gen_smt_vcs` proves the connection
with the lemmas of `Strata.SMT.DenoteProps` instead. This file checks that the
tactic works here, both for a private and for a public theorem, and that no
bridge axiom is introduced. Using the tactic in a `module` file requires
`public meta import Strata.MetaVerifier`.
-/
namespace Strata

private def modPgm : Program :=
#strata
program Core;
type T;
function f(x : T) : int;
axiom [f_pos]: forall x : T :: int.gt(f(x), 0);
procedure p(x : T, n : int, m : int, out r : int, out k : int)
spec {
  ensures int.gt(r, 0);
  ensures int.le(k, n) && int.le(k, m);
}
{
  r := f(x);
  k := if int.lt(n, m) then n else m;
};
#end

private theorem modCorrect : smtVCsCorrect modPgm := by
  gen_smt_vcs
  all_goals grind

public def modBvPgm : Program :=
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

public theorem modBvCorrect : smtVCsCorrect modBvPgm := by
  gen_smt_vcs
  all_goals bv_decide

/--
info: 'Strata.modBvCorrect' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound,
 _private.Strata.Languages.Core.Factory.0.Core.WFFactory._native.native_decide.ax_1]
-/
#guard_msgs in
#print axioms modBvCorrect

end Strata
---------------------------------------------------------------------
