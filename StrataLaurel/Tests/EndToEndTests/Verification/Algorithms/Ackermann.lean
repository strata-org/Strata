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

procedure ack(m: int, n: int) returns (r: int)
  requires m >= 0
  requires n >= 0
  opaque
  ensures r > 0
{
  if m == 0 then { r := n + 1 }
  else if n == 0 then { r := ack(m - 1, 1) }
  else {
    var inner: int := ack(m, n - 1);
    r := ack(m - 1, inner)
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure ack(m: int, n: int) returns (r: int)
  requires m >= 0
  requires n >= 0
  opaque
  ensures r > 0
{
  if m == 0 then { r := n + 1 }
  else if n == 0 then { r := ack(m, 1) }
  else {
    var inner: int := ack(m, n - 1);
    r := ack(m - 1, inner)
  }
};
#end
