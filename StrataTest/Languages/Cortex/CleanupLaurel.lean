/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

/-!
# The Cortex cleanup on programs translated from Laurel

The results of the divisions below are never read, so the cleanup removes the
stores. The checks that the divisors are not zero must survive it, on the
route to the verifier and on the Cortex interpreter.
-/

open StrataTest.Util
open Strata

#eval testCortexVerification <|
#strata
program Laurel;
procedure deadDivision(x: int, y: int)
  opaque
{
    var t: int := x / y
//                ^^^^^ error: divisor is non-zero does not hold
};

procedure overwrittenModulus(x: int, y: int)
  opaque
{
    var t: int := 0;
    t := x % y;
//       ^^^^^ error: modulus is non-zero does not hold
    t := 1
};

procedure guardedDivision(x: int, y: int)
  opaque
{
    if y != 0 then { var t: int := x / y }
};
#end

#eval testLaurelExecution { skipVerification := true, skipCoreInterpreter := true, skipLaurelInterpreter := true, skipCortexInterpreter := false } <|
#strata
program Laurel;
procedure main() entry
  opaque
{
    var y: int := 0;
    var t: int := 7 / y;
//                ^^^^^ error: divisor is non-zero does not hold
    t := 7 % y;
//       ^^^^^ error: modulus is non-zero does not hold
    t := 1
};
#end
