/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#guard_msgs (drop info) in
#eval testLaurel
#strata
program Laurel;

procedure mustNotCallProc(): int
  requires false
  opaque
{
  return 0
};

// Pure path: division by zero

procedure testAndThenDivByZero()
  opaque
{
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero()
  opaque
{
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero()
  opaque
{
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc()
  opaque
{
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc()
  opaque
{
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc()
  opaque
{
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
#end
