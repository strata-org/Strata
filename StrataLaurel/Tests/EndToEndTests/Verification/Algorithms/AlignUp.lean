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

procedure alignUp(value: int, align: int) returns (r: int)
  requires value >= 0
  requires align >= 1
  opaque
  ensures value <= r
  ensures r % align == 0
  ensures r - value < align
{
  r := ((value + align - 1) / align) * align
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure alignUp(value: int, align: int) returns (r: int)
  requires value >= 0
  requires align >= 1
  opaque
  ensures value <= r
//        ^^^^^^^^^^ error: postcondition does not hold
  ensures r % align == 0
  ensures r - value < align
{
  r := (value / align) * align
};
#end
