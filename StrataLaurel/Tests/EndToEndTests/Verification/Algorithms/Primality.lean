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

procedure noDivisorBelow(n: int, limit: int): bool
{
  forall(k: int) => 2 <= k ==> k < limit ==> n % k != 0
};

procedure isPrime(n: int) returns (r: bool)
  requires n >= 2
  opaque
  ensures r == noDivisorBelow(n, n)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var d: int := 2;
  var found: bool := false;
  while (d < n && !found)
    invariant 2 <= d
    invariant d <= n
    invariant found ==> n % d == 0
    invariant found ==> d < n
    invariant noDivisorBelow(n, d)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if n % d == 0 then { found := true } else { d := d + 1 }
  };
  r := !found
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure noDivisorBelow(n: int, limit: int): bool
{
  forall(k: int) => 2 <= k ==> k < limit ==> n % k != 0
};

procedure isPrime(n: int) returns (r: bool)
  requires n >= 2
  opaque
  ensures r == noDivisorBelow(n, n)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var d: int := 3;
  var found: bool := false;
  while (d < n && !found)
    invariant 2 <= d
    invariant d <= n
//            ^^^^^^ error: assertion does not hold
    invariant found ==> n % d == 0
    invariant found ==> d < n
    invariant noDivisorBelow(n, d)
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
//            ^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
  {
    if n % d == 0 then { found := true } else { d := d + 1 }
  };
  r := !found
};
#end
