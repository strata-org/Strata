/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

/-!
# The Cortex cleanup on programs translated from Laurel

The results of the divisions below are never read, so the cleanup removes the
stores. The checks that the divisors are not zero must survive it: in the Core
program, where each check is an `assert` that the divisor is not zero, and on
the Cortex interpreter.
-/

open StrataTest.Util
open Strata

/--
info: procedure deadDivision (x : int, y : int)
cfg $heapEntry {
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $start: {
    assert [pre_0]: !(y == 0);
    goto $return;
  }
  $return: {
    return;
  }
};
procedure overwrittenModulus (x : int, y : int)
cfg $heapEntry {
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $start: {
    assert [pre_3]: !(y == 0);
    goto $return;
  }
  $return: {
    return;
  }
};
procedure guardedDivision (x : int, y : int)
cfg $heapEntry {
  $heapEntry: {
    goto $exnEntry;
  }
  $exnEntry: {
    goto $entry;
  }
  $entry: {
    goto $start;
  }
  $start: {
    branch (!(y == 0)) goto $then$6 else goto $else$7;
  }
  $then$6: {
    assert [pre_9]: !(y == 0);
    goto $endif$8;
  }
  $else$7: {
    goto $endif$8;
  }
  $endif$8: {
    goto $return;
  }
  $return: {
    return;
  }
};
type check: ok
-/
#guard_msgs in
#eval printCortexCoreCFG (procs := ["deadDivision", "overwrittenModulus", "guardedDivision"]) <|
#strata
program Laurel;
procedure deadDivision(x: int, y: int)
  opaque
{
    var t: int := x / y
};

procedure overwrittenModulus(x: int, y: int)
  opaque
{
    var t: int := 0;
    t := x % y;
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
