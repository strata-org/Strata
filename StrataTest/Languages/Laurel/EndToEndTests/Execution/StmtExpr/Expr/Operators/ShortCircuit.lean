/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple
#strata
program Laurel;
procedure mustNotCallFunc(x: int): int
  requires false
{ return x };

procedure mustNotCallProc(): int
  requires false
  opaque
{
  return 0
};

// Pure path: function with requires false
procedure testAndThenFunc()
  entry
  opaque
{
  var b: bool := false && mustNotCallFunc(0) > 0;
  assert !b
};

procedure testOrElseFunc()
  entry
  opaque
{
  var b: bool := true || mustNotCallFunc(0) > 0;
  assert b
};

procedure testImpliesFunc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallFunc(0) > 0;
  assert b
};

// Pure path: division by zero

procedure testAndThenDivByZero()
  entry
  opaque
{
  assert !(false && 1 / 0 > 0)
};

procedure testOrElseDivByZero()
  entry
  opaque
{
  assert true || 1 / 0 > 0
};

procedure testImpliesDivByZero()
  entry
  opaque
{
  assert false ==> 1 / 0 > 0
};

// Imperative path: procedure with requires false

procedure testAndThenProc()
  entry
  opaque
{
  var b: bool := false && mustNotCallProc() > 0;
  assert !b
};

procedure testOrElseProc()
  entry
  opaque
{
  var b: bool := true || mustNotCallProc() > 0;
  assert b
};

procedure testImpliesProc()
  entry
  opaque
{
  var b: bool := false ==> mustNotCallProc() > 0;
  assert b
};
#end
