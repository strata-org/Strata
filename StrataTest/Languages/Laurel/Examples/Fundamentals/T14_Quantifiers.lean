/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- info: 26:2-49  error: assertion does not hold
30:2-17  error: assertion could not be proved -/
#guard_msgs in
#eval testLaurelExpect <|
#strata_expect
program Laurel;
procedure testForall()
  opaque
{
    assert forall(x: int) => x + 0 == x
};

procedure testExists()
  opaque
{
    assert exists(x: int) => x == 42
};

procedure testQuantifierInContract(n: int)
  requires n > 0
  opaque
  ensures forall(i: int) => i >= 0 ==> i < n ==> i < n + 1
{
};

function P(x: int): int;
function Q(): int;
procedure triggers()
  opaque
{
  assert forall(i: int) { P(i) } => P(i) == i + 1;
  assert forall(i: int) => true;

  assume forall(i: int) { P(i) } => P(i) == i + 1 && Q() == 0;
  assert Q() == 0;
  assert P(1) == 2
};
#end
