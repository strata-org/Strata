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

constrained int32 = x: int where -2147483648 <= x && x <= 2147483647 witness 0

procedure fact(n: int): int;

procedure factorial(n: int) returns (r: int32)
//                                      ^^^^^ error: postcondition could not be proved
// desired: verifies
  requires 0 <= n
  requires n <= 12
  requires fact(0) == 1
  requires forall(k: int) => k >= 1 ==> fact(k) == k * fact(k - 1)
  requires forall(k: int) => k >= 0 ==> fact(k) >= 1
  requires fact(n) <= 2147483647
  opaque
  ensures r == fact(n)
{
  if n == 0 then { r := 1 }
  else {
    var rest: int32 := factorial(n - 1);
    r := n * rest
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

constrained int32 = x: int where -2147483648 <= x && x <= 2147483647 witness 0

procedure fact(n: int): int;

procedure factorial(n: int) returns (r: int32)
//                                      ^^^^^ error: postcondition could not be proved
  requires 0 <= n
  requires n <= 13
  requires fact(0) == 1
  requires forall(k: int) => k >= 1 ==> fact(k) == k * fact(k - 1)
  requires forall(k: int) => k >= 0 ==> fact(k) >= 1
  opaque
  ensures r == fact(n)
{
  if n == 0 then { r := 1 }
  else {
    var rest: int32 := factorial(n - 1);
    r := n * rest
//  ^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  }
};
#end
