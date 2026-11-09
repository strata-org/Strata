/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core
import Strata.MetaVerifier
import StrataTest.Languages.Core.Tests.WPTestUtils

/-! # Verdicts of `--vcgen wp` on branches that are never taken

Under `--vcgen wp` the obligations of a branch whose condition is `false` are reported, on a path
assuming `false`, as symbolic evaluation reports them; the code after an `exit` is not run, and
its obligations are not reported, in both modes; a variable assigned before an exit keeps, at
the exit's target, the value it had at the exit. -/

namespace Strata.WPVerdictTest

open Strata.WPTestUtils

/-- A branch whose condition is `false` (from `Examples/Cover.lean`). -/
def falseBranchPgm :=
#strata
program Core;
procedure Test()
{
  var x : int;
  assume (int.ge(x, 0));

  if (false) {
    cover [unreachable_cover1]: (true);
    cover [unreachable_cover2]: (false);
    assert [unreachable_assert]: (false);
  } else {
    cover [reachable_cover]: (true);
    cover [unsatisfiable_cover]: (x == int.neg(1));
    assert [reachable_assert]: (true);
  }
};
#end

/-- Exits (from `Examples/Exit.lean`). -/
def exitPgm :=
#strata
program Core;
procedure Test1(x : bool, out y : bool)
{
    l1: {
      assert [a1]: x == x;
      exit l1;
      assert [a2]: !(x == x); // skipped because we exited l1
    }
    assert [a3]: x == x;
};

procedure Test2(x : int, out y : bool)
{
    l5: {
      l4: {
        l4_before: {
          l3_before: {
            l1: {
              assert [a4]: x == x;
              if (int.gt(x, 0)) {
                exit l3_before;
              } else {
                exit l4_before;
              }
            }
            l2: {
              assert [a5]: !(x == x); // skipped over
            }
          }
          assert [a6]: int.gt(int.mul(x, 2), x);
          exit l5;
        }
        assert [a7]: int.le(x, 0);
        exit l5;
      }
    }
};
#end

/-- An exit, then an `ite` whose two arms exit to the same block and assign the same variable. -/
def earlyExitPgm :=
#strata
program Core;
procedure P(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L3: {
      if (int.add(x, 0) == 1) {} else { x := int.add(y, int.neg(4)); exit Out; }
    }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [early]: int.ge(x, y);
};

procedure Min1(c : int, d : int, out x : int, out y : int)
{
  Out: {
    L0: {
      if (int.ge(int.add(d, 4), 2)) {} else { x := y; exit Out; }
      y := x;
    }
    if (d == 1) { x := y; exit Out; } else { x := int.add(x, 4); exit Out; }
  }
  assert [min1]: int.ge(x, y);
};

procedure Min2(c : int, d : int, out x : int, out y : int)
{
  Out: {
    L3: {
      if (int.add(x, 0) == 1) {} else { x := int.add(y, 4); exit Out; }
    }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(x, y); exit Out; }
  }
  assert [min2]: int.ge(x, y);
};

procedure Min3(c : int, d : int, out x : int, out y : int)
{
  L0: {
    L1: {
      L2: {
        L3: {
          if (int.gt(int.add(d, 3), 0)) {} else { x := int.add(c, d); exit L0; }
          assume [h6]: 3 == 1;
        }
      }
    }
    if (4 == 1) { x := c; exit L0; } else { havoc x; exit L0; }
  }
  if (int.gt(x, 0)) {
    L36: {
      assert [a37]: int.gt(c, 0);
    }
  } else {}
};
#end

/-- Variants: two earlier exits; an exit two blocks deep; an earlier `ite` whose two arms
    exit; different variables in the arms. -/
def earlyExitVariantsPgm :=
#strata
program Core;
procedure TwoExits(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: { if (x == 1) {} else { x := int.add(y, int.neg(4)); exit Out; } }
    L2: { if (x == 2) {} else { x := int.add(y, int.neg(5)); exit Out; } }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [two]: int.ge(x, y);
};

procedure Deep(out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: { L2: { if (x == 1) {} else { x := int.add(y, int.neg(4)); exit Out; } } }
    if (int.gt(6, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [deep]: int.ge(x, y);
};

procedure BothEarly(c : int, d : int, out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: {
      if (int.gt(c, 0)) {
        if (x == 1) { x := int.add(y, int.neg(4)); exit Out; }
        else { x := int.add(y, int.neg(5)); exit Out; }
      } else {}
    }
    if (int.gt(d, 0)) { x := int.add(y, 2); exit Out; } else { x := int.add(y, 1); exit Out; }
  }
  assert [both]: int.ge(x, y);
};

procedure Vars(d : int, out x : int, out y : int)
{
  assume [h]: int.ge(x, y);
  Out: {
    L1: {
      if (x == 1) {} else { y := int.add(y, int.neg(1)); x := int.add(y, int.neg(4)); exit Out; }
    }
    if (int.gt(d, 0)) { y := int.add(y, int.neg(1)); x := int.add(y, 2); exit Out; }
    else { x := int.add(y, 1); exit Out; }
  }
  assert [vars]: int.ge(x, y);
};
#end

/--
info: symbolic: unreachable_cover1 failed, unreachable_cover2 failed, unreachable_assert proved, reachable_cover unknown, unsatisfiable_cover failed, reachable_assert proved
wp: unreachable_cover1 failed, unreachable_cover2 failed, unreachable_assert proved, reachable_cover unknown, unsatisfiable_cover failed, reachable_assert proved
-/
#guard_msgs in
#eval printModesVerdicts falseBranchPgm

/--
info: symbolic: a1 proved, a3 proved, a4 proved, a6 proved, a7 proved
wp: a1 proved, a3 proved, a4 proved, a6 proved, a7 proved
-/
#guard_msgs in
#eval printModesVerdicts exitPgm

/--
info: symbolic: a37 proved, early failed, min1 proved, min2 proved
wp: a37 proved, early failed, min1 proved, min2 proved
-/
#guard_msgs in
#eval printModesVerdicts earlyExitPgm (sorted := true)

/--
info: symbolic: both failed, deep failed, two failed, vars failed
wp: both failed, deep failed, two failed, vars failed
-/
#guard_msgs in
#eval printModesVerdicts earlyExitVariantsPgm (sorted := true)

end Strata.WPVerdictTest
