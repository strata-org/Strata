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

procedure pw(b: int, e: int): int;

procedure power(base: int, exp: int) returns (r: int)
  requires exp >= 0
  requires forall(b: int) => pw(b, 0) == 1
  requires forall(b: int) => forall(e: int) => e >= 1 ==> pw(b, e) == b * pw(b, e - 1)
  opaque
  ensures r == pw(base, exp)
{
  var acc: int := 1;
  var i: int := 0;
  while (i < exp)
    invariant 0 <= i
    invariant i <= exp
    invariant acc == pw(base, i)
  {
    acc := acc * base;
    i := i + 1
  };
  r := acc
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure pw(b: int, e: int): int;

procedure power(base: int, exp: int) returns (r: int)
  requires exp >= 1
  requires forall(b: int) => pw(b, 0) == 1
  requires forall(b: int) => forall(e: int) => e >= 1 ==> pw(b, e) == b * pw(b, e - 1)
  opaque
  ensures r == pw(base, exp)
{
  var acc: int := 1;
  var i: int := 1;
  while (i < exp)
    invariant 0 <= i
    invariant i <= exp
    invariant acc == pw(base, i)
//            ^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    acc := acc * base;
    i := i + 1
  };
  r := acc
};
#end
