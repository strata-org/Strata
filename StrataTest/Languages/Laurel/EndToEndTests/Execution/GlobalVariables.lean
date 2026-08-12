/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelMultiple <|
#strata
program Laurel;
var answer: int := 42
var derived: int := 2 * 3 + 1
var flag: bool := true
procedure readInitial()
  entry
  opaque
{
  assert answer == 42;
  assert derived == 7;
  assert flag
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var counter: int := 10
procedure writeThenRead()
  entry
  opaque
{
  counter := counter + 5;
  assert counter == 15;
  counter += 1;
  assert counter == 16
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var a: int := 1
var b: int := 2
procedure framing()
  entry
  opaque
{
  assert a == 1;
  assert b == 2;
  a := a + b;
  assert a == 3;
  assert b == 2
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var g: int := 0
procedure setG(v: int)
  opaque
  ensures g == v
{
  g := v
};
procedure readG() returns (r: int) {
  return g
};
procedure driver()
  entry
  opaque
{
  var initial: int := readG();
  assert initial == 0;
  setG(7);
  assert g == 7;
  var final: int := readG();
  assert final == 7
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var g: int := 3
procedure shadows()
  entry
  opaque
{
  assert g == 3;
  var g: int := 100;
  assert g == 100
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var shared: int := 1
procedure firstEntry()
  entry
  opaque
{
  assert shared == 1;
  shared := 99
};
procedure secondEntry()
  entry
  opaque
{
  assert shared == 1
};
#end

#eval testLaurelMultiple <|
#strata
program Laurel;
var g: int := 5
procedure wrongClaim()
  entry
  opaque
{
  g := g + 1;
  assert g == 7
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end
