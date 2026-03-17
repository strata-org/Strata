/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def testPgm1 :=
#strata
program Core;
procedure first(x : int) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  body: {
    if (x < 0) { r := 0 - x; exit body; }
    r := x;
    exit body;
  }
};

procedure second() returns () { assert [a]: true; };
#end


/--
info:
Obligation: post
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify testPgm1 (options := .quiet)

def sequentialExitPgm :=
#strata
program Core;


procedure wrong(c1 : bool, c2 : bool) returns (r : int)
spec { ensures r > 0; }
{
  done: {
    if (c1) { r := -1; exit done; }
    if (c2) { r := 2; exit done; }
    r := 3;
  }
};
#end


/--
info:
Obligation: wrong_ensures_0
Property: assert
Result: ❌ fail

Obligation: wrong_ensures_0
Property: assert
Result: ✅ pass

Obligation: wrong_ensures_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify sequentialExitPgm (options := .quiet)
