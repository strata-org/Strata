/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! Native arrays run on the Laurel interpreter and on the Cortex interpreter. The
translation to Core does not support them yet, so neither the verifier nor the Core
interpreter runs these blocks, and the Core program of the Cortex translation is not
checked. -/

private def arrayPaths : MultiplePathTestOptions :=
  { skipVerification := true, skipCoreInterpreter := true, skipCortexInterpreter := false,
    skipCortexCoreCheck := true }

/-! Arrays: allocation with default elements, element writes and reads, and the length. -/

#eval testLaurelExecution arrayPaths <|
#strata
program Laurel;
procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<int> := new Array<int>(3);
  a[1] := 7;
  assert a[0] == 0;
  assert a[1] == 7;
  assert a#length() == 3
};
#end

/-! An index outside the array stops the run, on each interpreter. Both stop by throwing, so
each interpreter gets its own block. -/

/-- error: index 2 is out of range for an array of length 2 -/
#guard_msgs in
#eval testLaurelExecution { arrayPaths with skipCortexInterpreter := true } <|
#strata
program Laurel;
procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<int> := new Array<int>(2);
  var x: int := a[2]
};
#end

/--
error: cortex-interpret: 'main': an expression did not evaluate (diagnostics: [the interpreter fails here: an expression did not evaluate])
-/
#guard_msgs in
#eval testLaurelExecution { arrayPaths with skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<int> := new Array<int>(2);
  var x: int := a[2]
};
#end

/-! An array of a composite: an element of it is a value of that composite. -/

#eval testLaurelExecution arrayPaths <|
#strata
program Laurel;
composite Box { var v: int }

procedure main()
  entry
  opaque
  modifies *
{
  var a: Array<Box> := new Array<Box>(1);
  a[0] := new Box;
  var b: Box := a[0];
  b#v := 3;
  assert a[0]#v == 3
};
#end
