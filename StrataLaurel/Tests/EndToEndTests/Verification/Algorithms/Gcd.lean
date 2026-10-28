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

procedure gcd(a: int, b: int) returns (r: int)
  requires a > 0
  requires b >= 0
  opaque
  ensures r > 0
  ensures a % r == 0
//        ^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures b % r == 0
{
  if b == 0 then { r := a } else { r := gcd(b, a % b) }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure gcd(a: int, b: int) returns (r: int)
  requires a > 0
  requires b >= 0
  opaque
  ensures r > 0
//        ^^^^^ error: postcondition does not hold
{
  if b == 0 then { r := b } else { r := gcd(b, a % b) }
};
#end
