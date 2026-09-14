/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
# `throws` binding corner cases

A binder reusing an input's name, and the short return form whose value output
is `$result` (a name the ContractPass helper also binds). Both must lower and
verify regardless of how the binding is eliminated.
-/

#guard_msgs in
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure binderShadowsInput(e: int)
  throws (e: Err)
  opaque
  throwsOn true {
    ensures e#code == 5
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
#end

#guard_msgs in
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite Err { var code: int }
procedure shortFormThrows(): int
  throws (e: Err)
  opaque
  ensures $result > 0
  throwsOn true {
    ensures e#code == 5
  }
{
  var x: Err := new Err;
  x#code := 5;
  throw x
};
#end
