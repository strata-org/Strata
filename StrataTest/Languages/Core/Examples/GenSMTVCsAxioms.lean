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
## Axioms emitted by `gen_smt_vcs`

`gen_smt_vcs` expands `smtVCsCorrect p` into one subgoal per VC and
adds a per-theorem local axiom that bridges the `translateQuery`-based
conjunction back to the `smtVCsCorrect` goal type.  This axiom makes
`translateQuery` part of the trusted computing base but does not weaken
the individual VC proofs that the user must supply.

`#print axioms` on a theorem proved with `gen_smt_vcs` will list this
bridge axiom alongside the standard Lean kernel axioms.
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

-- `#print axioms` shows the per-theorem TCB bridge axiom produced by
-- `gen_smt_vcs`.  It is scoped to this theorem and named after it, so
-- different theorems get independent axioms.
-- Expected output includes:
--   Strata.minCorrect._genSMTVCs_tcbBridge : andN [...] → smtVCsCorrect minPgm
-- alongside the standard Lean kernel axioms (Classical.choice, propext, etc.).
#print axioms minCorrect

end Strata
---------------------------------------------------------------------
