/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
## Tests for VCG path merging with exit (goto) inside if-then-else

When a procedure contains an `exit` (goto) inside an `if` branch, the VCG
should merge environments by exit label rather than producing separate paths.
Without merging, subsequent procedures in the program get verified once per
path from the previous procedure, causing duplicate proof obligations.

See: https://github.com/strata-org/Strata/issues/419
-/

/-- Reproduction case from the bug report: exit inside one branch of an if.
    `second` should produce exactly one `assert_0` failure, not two. -/
def exitItePgm :=
#strata
program Core;

procedure first(a : int) returns (r : int)
spec { }
{
  done: {
    if (a > 0) {
      r := 1;
      exit done;
    }
    r := 0;
  }
};

procedure second(a : int) returns (r : int)
spec { }
{
  assert [assert_0]: a > 0;
  r := a;
};
#end

/--
info:
Obligation: assert_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify exitItePgm (options := .quiet)

/-- Multiple exit targets: both branches exit to different labels.
    The third procedure should still produce exactly one obligation. -/
def exitIteMultiTargetPgm :=
#strata
program Core;

procedure multi(a : int) returns (r : int)
spec { }
{
  outer: {
    mid: {
      if (a > 0) {
        r := 1;
        exit outer;
      } else {
        r := 0;
        exit mid;
      }
    }
    r := r + 1;
  }
};

procedure check(a : int) returns (r : int)
spec { }
{
  assert [check_0]: a > 0;
  r := a;
};
#end

/--
info:
Obligation: check_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify exitIteMultiTargetPgm (options := .quiet)

/-- Both branches exit to the same label — should merge into one path. -/
def exitIteSameLabelPgm :=
#strata
program Core;

procedure same_exit(a : int) returns (r : int)
spec { }
{
  done: {
    if (a > 0) {
      r := 1;
      exit done;
    } else {
      r := 0;
      exit done;
    }
  }
};

procedure after(a : int) returns (r : int)
spec { }
{
  assert [after_0]: a > 0;
  r := a;
};
#end

/--
info:
Obligation: after_0
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval verify exitIteSameLabelPgm (options := .quiet)

end Strata
