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

procedure paddedBelow(res: Sequence<int>, c: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(res) ==> seqSelect(res, k) == c
};

procedure copiedBelow(res: Sequence<int>, s: Sequence<int>, pad: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(s) ==> 0 <= pad + k ==> pad + k < seqLength(res) ==>
    seqSelect(res, pad + k) == seqSelect(s, k)
};

procedure leftPad(s: Sequence<int>, c: int, n: int) returns (res: Sequence<int>)
  requires n >= 0
  opaque
  ensures seqLength(res) == (if n > seqLength(s) then n else seqLength(s))
  ensures paddedBelow(res, c, seqLength(res) - seqLength(s))
  ensures copiedBelow(res, s, seqLength(res) - seqLength(s), seqLength(s))
{
  var pad: int := if n > seqLength(s) then n - seqLength(s) else 0;
  var out: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < pad)
    invariant 0 <= i
    invariant i <= pad
    invariant seqLength(out) == i
    invariant paddedBelow(out, c, i)
  {
    out := seqBuild(out, c);
    i := i + 1
  };
  var j: int := 0;
  while (j < seqLength(s))
    invariant 0 <= j
    invariant j <= seqLength(s)
    invariant seqLength(out) == pad + j
    invariant paddedBelow(out, c, pad)
    invariant copiedBelow(out, s, pad, j)
  {
    out := seqBuild(out, seqSelect(s, j));
    j := j + 1
  };
  res := out
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure paddedBelow(res: Sequence<int>, c: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(res) ==> seqSelect(res, k) == c
};

procedure copiedBelow(res: Sequence<int>, s: Sequence<int>, pad: int, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(s) ==> 0 <= pad + k ==> pad + k < seqLength(res) ==>
    seqSelect(res, pad + k) == seqSelect(s, k)
};

procedure leftPad(s: Sequence<int>, c: int, n: int) returns (res: Sequence<int>)
  requires n >= 0
  opaque
  ensures seqLength(res) == (if n > seqLength(s) then n else seqLength(s))
  ensures paddedBelow(res, c, seqLength(res) - seqLength(s))
  ensures copiedBelow(res, s, seqLength(res) - seqLength(s), seqLength(s))
{
  var pad: int := if n > seqLength(s) then n - seqLength(s) else 0;
  var out: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i <= pad)
    invariant 0 <= i
    invariant i <= pad
//            ^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
    invariant seqLength(out) == i
    invariant paddedBelow(out, c, i)
  {
    out := seqBuild(out, c);
    i := i + 1
  };
  var j: int := 0;
  while (j < seqLength(s))
    invariant 0 <= j
    invariant j <= seqLength(s)
    invariant seqLength(out) == pad + j
    invariant paddedBelow(out, c, pad)
    invariant copiedBelow(out, s, pad, j)
  {
    out := seqBuild(out, seqSelect(s, j));
    j := j + 1
  };
  res := out
};
#end
