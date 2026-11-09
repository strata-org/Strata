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
## `gen_smt_vcs` on less common query shapes

End-to-end counterparts of cases in `StrataTest/DL/SMT/DenoteProofTests.lean`:
a parameterized uninterpreted sort, a sort synonym in the signature of an
interpreted function, an existential inside a function body, and quantifiers
with triggers.
-/
namespace Strata

private def shapesPgm : Program :=
#strata
program Core;

type Box (a : Type);
type IntBox := Box int;

function get(b : IntBox) : int;
function bump(b : IntBox) : int { int.add(get(b), 1) }
function hasLarger(x : int) : bool { exists y : int :: int.gt(y, x) }

axiom [get_pos]: forall b : IntBox :: { get(b) } int.gt(get(b), 0);

procedure p(b : IntBox, out r : int)
spec {
  ensures int.gt(r, 1);
}
{
  assert [larger]: hasLarger(r);
  assert [triggered]: forall c : IntBox :: { bump(c) } int.gt(bump(c), 1);
  r := bump(b);
};
#end

theorem shapesCorrect : smtVCsCorrect shapesPgm := by
  gen_smt_vcs
  case larger => intro _ _ r _ _ _; exact ⟨r + 1, by omega⟩
  all_goals grind

end Strata
