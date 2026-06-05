/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

-- Two consecutive unlabeled cover statements get distinct default labels
def coverDefaultNames :=
#strata
program Core;
procedure Test(x : int)
spec {
  requires x >= 0;
}
{
  cover (true);
  cover (true);
};
#end

/--
info: program Core;

procedure Test (x : int)
spec {
  requires [Test_requires_0]: x >= 0;
  } {
  cover [cover_0]: true;
  cover [cover_1]: true;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram coverDefaultNames) |>.fst

/--
info:
Obligation: cover_0
Property: cover
Result: ✅ pass

Obligation: cover_1
Property: cover
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify coverDefaultNames (options := .quiet)

---------------------------------------------------------------------

-- assert followed by cover: counters are independent
def assertThenCover :=
#strata
program Core;
procedure Test(x : int)
spec {
  requires x >= 0;
}
{
  assert (true);
  cover (true);
};
#end

/--
info: program Core;

procedure Test (x : int)
spec {
  requires [Test_requires_0]: x >= 0;
  } {
  assert [assert_0]: true;
  cover [cover_0]: true;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram assertThenCover) |>.fst

---------------------------------------------------------------------

-- cover followed by assert: counters are independent
def coverThenAssert :=
#strata
program Core;
procedure Test(x : int)
spec {
  requires x >= 0;
}
{
  cover (true);
  assert (true);
};
#end

/--
info: program Core;

procedure Test (x : int)
spec {
  requires [Test_requires_0]: x >= 0;
  } {
  cover [cover_0]: true;
  assert [assert_0]: true;
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram coverThenAssert) |>.fst

---------------------------------------------------------------------
