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

procedure mc91(n: int) returns (r: int)
  opaque
  ensures r == (if n > 100 then n - 10 else 91)
{
  if n > 100 then { r := n - 10 }
  else {
    var t: int := mc91(n + 11);
    r := mc91(t)
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure mc91(n: int) returns (r: int)
  opaque
  ensures r == (if n > 100 then n - 10 else 91)
{
  if n > 100 then { r := n - 10 }
  else {
    var t: int := mc91(n + 10);
    r := mc91(t)
  }
};
#end
