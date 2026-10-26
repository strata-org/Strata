/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure foo()
  opaque
{
  <?>
//^^^ error: could not infer type
};
#end

-- A hole as an `if`'s then-branch is typed at the else-branch's `int`.
#eval testLaurelVerification <|
#strata
program Laurel;
procedure holeBranch(b: bool, x: int) opaque {
  assert (if b then <?> else x) == x
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
