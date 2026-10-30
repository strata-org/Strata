/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Tests.EndToEndTests.Verification.Algorithms.BenchmarkOptions

open StrataTest.Util
open StrataTest.Util.Algorithms
open Strata

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure isEven(n: int) returns (r: bool)
  requires n >= 0
  opaque
  ensures r == (n % 2 == 0)
{
  if n == 0 then { r := true } else { r := isOdd(n - 1) }
};

procedure isOdd(n: int) returns (r: bool)
  requires n >= 0
  opaque
  ensures r == (n % 2 == 1)
{
  if n == 0 then { r := false } else { r := isEven(n - 1) }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure isEven(n: int) returns (r: bool)
  requires n >= 0
  opaque
  ensures r == (n % 2 == 0)
{
  if n == 0 then { r := true } else { r := isOdd(n - 1) }
};

procedure isOdd(n: int) returns (r: bool)
  requires n >= 0
  opaque
  ensures r == (n % 2 == 1)
//        ^^^^^^^^^^^^^^^^^ error: postcondition does not hold
{
  if n == 0 then { r := true } else { r := isEven(n - 1) }
};
#end
