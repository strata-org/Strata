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

procedure mult(a: int, b: int) returns (r: int)
  requires a >= 0
  requires b >= 0
  opaque
  ensures r == a * b
{
  if a == 0 then { r := 0 } else {
    var rest: int := mult(a - 1, b);
    r := b + rest
  }
};

procedure commutative(a: int, b: int)
  requires a >= 0
  requires b >= 0
  opaque
{
  var left: int := mult(a, b);
  var right: int := mult(b, a);
  assert left == right
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure mult(a: int, b: int) returns (r: int)
  requires a >= 0
  requires b >= 0
  opaque
  ensures r == a * b
//        ^^^^^^^^^^ error: postcondition does not hold
{
  if a == 0 then { r := 0 } else {
    var rest: int := mult(a - 1, b - 1);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
    r := b + rest
  }
};
#end
