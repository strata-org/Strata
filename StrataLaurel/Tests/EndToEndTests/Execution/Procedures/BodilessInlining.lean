/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Bodiless Procedure Inlining Test

Verifies that inlining a bodiless Laurel procedure does not introduce
`assume false`. Previously, bodiless procedures had `assume false` as their
body, so inlining would make everything after the call trivially provable.
Now the body assumes the postconditions instead, so `assert false` after
the inlined call is correctly rejected. -/

-- No interpreters: `bodilessProcedure` has no body, so the Laurel interpreter refuses the call, and Core says "condition did not reduce to bool".
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } (options := { verifyOptions := .quiet, translateOptions := { inlineFunctionsWhenPossible := true } }) <|
#strata
program Laurel;
procedure bodilessProcedure() returns (r: int)
  opaque
  ensures r > 0
;

procedure caller()
  opaque
{
  var x: int := bodilessProcedure();
  assert x > 0;
  assert false
//^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- A call to a bodiless `modifies *` procedure runs in the Core interpreter: the heap, an inout
-- parameter of the call, gets a fresh value.
#eval testLaurelExecution { skipVerification := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure env() opaque modifies *;
procedure main() entry opaque modifies * { var k: int := 1; env(); assert k == 1 };
#end

-- A read of the heap after such a call does not evaluate: the call havocked the heap, and a
-- concrete run chooses no value for it. The error names the call.
/--
error: interpret: 'main' raised a non-assertion error: [ERROR] assert (assert(2211)) condition did not reduce to bool: it reads the value of '$heap' that the call to the abstract procedure 'env' havocked, which a concrete run does not choose
-/
#guard_msgs in
#eval testLaurelExecution { skipVerification := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Cell { var x: int }
procedure env() opaque modifies *;
procedure main() entry opaque modifies * { var c: Cell := new Cell; c#x := 5; env(); assert c#x == 5 };
#end
