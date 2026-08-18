/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # Tests for `VerifyOptions.disableCSE`

Smoke-tests the pipeline with common subexpression elimination disabled.
CSE is model-preserving (it only introduces definitional equalities), so
disabling it cannot make verification unsound — though, since it changes the
SMT encoding's shape, obligations may in general flip between conclusive and
`unknown`. On this small program both configurations are expected to reach
the same conclusive outcome, which is what is pinned here.
-/

meta section
---------------------------------------------------------------------
namespace Strata

/-- A program where CSE has real work: `int.add(a, b)` appears twice in the
    body, and the postcondition needs the solver (it is not resolved by
    partial evaluation alone). -/
def cseProbePgm :=
#strata
program Core;
procedure CseProbe(a : int, b : int, out c : int)
spec {
  requires (int.ge(a, 0));
  requires (int.ge(b, 0));
  ensures (int.ge(c, int.add(a, b)));
}
{
  c := int.add(int.add(a, b), int.add(a, b));
};
#end

-- Baseline: the default pipeline (CSE enabled).
/--
info:
Obligation: CseProbe_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cseProbePgm (options := Core.VerifyOptions.quiet)

-- With CSE disabled the pipeline still verifies the same obligation. On a
-- program this small the outcome matches the baseline exactly; in general
-- only soundness is guaranteed, not identical solver results.
/--
info:
Obligation: CseProbe_ensures_2
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify cseProbePgm (options :=
  { Core.VerifyOptions.quiet with disableCSE := true })

/-- A failing twin of `cseProbePgm`: same duplicated `int.add(a, b)`
    subexpressions for CSE to extract, but the postcondition is false at
    `a = b = 0` (there `c = 0`, and `int.gt(c, int.add(a, b))` needs
    `0 > 0`). -/
def cseProbeFailPgm :=
#strata
program Core;
procedure CseProbeFail(a : int, b : int, out c : int)
spec {
  requires (int.ge(a, 0));
  requires (int.ge(b, 0));
  ensures (int.gt(c, int.add(a, b)));
}
{
  c := int.add(int.add(a, b), int.add(a, b));
};
#end

-- Baseline: the false postcondition fails with the default pipeline.
/--
info:
Obligation: CseProbeFail_ensures_2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cseProbeFailPgm (options := Core.VerifyOptions.quiet)

-- Soundness with CSE disabled: the false postcondition must still fail —
-- skipping CSE must not turn a failing obligation into a pass.
/--
info:
Obligation: CseProbeFail_ensures_2
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify cseProbeFailPgm (options :=
  { Core.VerifyOptions.quiet with disableCSE := true })

end Strata
end
---------------------------------------------------------------------
