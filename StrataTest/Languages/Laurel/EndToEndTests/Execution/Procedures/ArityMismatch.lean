/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Function called with too many arguments

`showLocations := true` makes `testLaurel` echo each diagnostic's file-relative
`line:col` range (computed from the snippet's base line — no manual offsets),
while the inline `// ^^^` annotation still asserts the error. The golden below
thus *shows* the localization without catching a spurious "unexpected
diagnostic". (Other tests omit the flag and stay silent on success.) -/

/--
info: 32:16-23  error: call to 'f' expects 1 argument(s) but 2 were provided
-/
#guard_msgs in
#eval testLaurel (showLocations := true) <|
#strata
program Laurel;
function f(x: int): int { x };

procedure caller()
  opaque
{
  var y: int := f(1, 2)
//              ^^^^^^^ error: call to 'f' expects 1 argument(s) but 2 were provided
};
#end

/-! ## Multi-return procedure assigned to single target -/

#eval testLaurel <|
#strata
program Laurel;
procedure twoReturns() returns (a: int, b: int)
  opaque
  ensures a == 1 && b == 2;

procedure mismatch()
  opaque
{
  var x: int;
  assign x := twoReturns()
//            ^^^^^^^^^^^^ error: expected 'int', got '(int, int)'
};
#end
