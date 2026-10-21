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

procedure isqrt(n: int) returns (r: int)
  requires n >= 0
  opaque
  ensures 0 <= r
  ensures r * r <= n
  ensures n < (r + 1) * (r + 1)
{
  var x: int := 0;
  while ((x + 1) * (x + 1) <= n)
    invariant 0 <= x
    invariant x * x <= n
  {
    x := x + 1
  };
  r := x
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure isqrt(n: int) returns (r: int)
  requires n >= 0
  opaque
  ensures 0 <= r
  ensures r * r <= n
//        ^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures n < (r + 1) * (r + 1)
{
  var x: int := 0;
  while (x * x <= n)
    invariant 0 <= x
  {
    x := x + 1
  };
  r := x
};
#end
