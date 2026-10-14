/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! Reading a `Map` at a key it does not hold is unconstrained but fixed: the same
read twice agrees, and the value can be computed with. The Laurel interpreter
answers the value type's default; the Core interpreter does not reduce an
assertion over an unconstrained value, so it does not run this block. -/

#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure absentKey()
  entry
  opaque
{
  var m: Map<int, int> := mapEmpty();
  m := mapSet(m, 1, 2);
  var x: int := mapGet(m, 7);
  var y: int := x + 0;
  assert y == x;
  assert mapGet(m, 7) == mapGet(m, 7);
  assert mapGet(m, 1) == 2
};
#end

/-! A value type with no default, here a composite: two reads of the same absent key
are still the same value. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box {
  var v: int
}

procedure absentComposite()
  entry
  opaque
  modifies *
{
  var m: Map<int, Box> := mapEmpty();
  var a: Box := mapGet(m, 1);
  var b: Box := mapGet(m, 1);
  assert a == b
};
#end

/-! Two total maps are equal when they agree at every key, so maps with different
constant values differ, even though neither holds an explicit entry.
The verifier cannot decide map extensionality here ("could not be proved"), and the
Core interpreter does not reduce `mapConst`, so this block runs the Laurel
interpreter only. -/

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true } <|
#strata
program Laurel;
procedure constantMaps()
  entry
  opaque
{
  var a: TotalMap int int := mapConst(1);
  var b: TotalMap int int := mapConst(2);
  assert select(a, 0) != select(b, 0);
  assert !(a == b)
};
#end
