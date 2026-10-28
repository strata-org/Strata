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

procedure pow2(n: int): int;

procedure moves(n: int) returns (r: int)
  requires n >= 0
  requires pow2(0) == 1
  requires forall(k: int) => k >= 1 ==> pow2(k) == 2 * pow2(k - 1)
  opaque
  ensures r == pow2(n) - 1
{
  if n == 0 then { r := 0 }
  else {
    var m: int := moves(n - 1);
    r := 2 * m + 1
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure pow2(n: int): int;

procedure moves(n: int) returns (r: int)
  requires n >= 0
  requires pow2(0) == 1
  requires forall(k: int) => k >= 1 ==> pow2(k) == 2 * pow2(k - 1)
  opaque
  ensures r == pow2(n) - 1
//        ^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
{
  if n == 0 then { r := 0 }
  else {
    var m: int := moves(n - 1);
    r := 2 * m + 2
  }
};
#end
