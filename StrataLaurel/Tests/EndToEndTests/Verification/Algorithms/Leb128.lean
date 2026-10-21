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

procedure bytes(s: Sequence<int>): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(s) ==> 0 <= seqSelect(s, k) && seqSelect(s, k) <= 255
};

procedure encode(value: int) returns (out: Sequence<int>)
  requires value >= 0
  opaque
  ensures seqLength(out) >= 1
  ensures bytes(out)
{
  var v: int := value;
  var o: Sequence<int> := seqEmpty();
  while (v >= 128)
    invariant v >= 0
    invariant bytes(o)
  {
    o := seqBuild(o, v % 128 + 128);
    v := v / 128
  };
  out := seqBuild(o, v)
};

procedure decode(input: Sequence<int>, maxBytes: int) returns (ok: bool, value: int)
  requires maxBytes >= 1
  opaque
  ensures ok ==> value >= 0
{
  var result: int := 0;
  var scale: int := 1;
  var i: int := 0;
  var done: bool := false;
  ok := false;
  while (!done && i < maxBytes && i < seqLength(input))
    invariant 0 <= i
    invariant result >= 0
    invariant scale >= 1
  {
    var b: int := seqSelect(input, i);
    if b < 0 || b > 255 then { done := true }
    else {
      result := result + (b % 128) * scale;
      if b < 128 then { ok := true; done := true }
      else { scale := scale * 128; i := i + 1 }
    }
  };
  value := result
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure bytes(s: Sequence<int>): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(s) ==> 0 <= seqSelect(s, k) && seqSelect(s, k) <= 255
};

procedure encode(value: int) returns (out: Sequence<int>)
  requires value >= 0
  opaque
  ensures seqLength(out) >= 1
  ensures bytes(out)
{
  var v: int := value;
  var o: Sequence<int> := seqEmpty();
  while (v >= 128)
    invariant v >= 0
    invariant bytes(o)
  {
    o := seqBuild(o, v % 128 + 128);
    v := v / 128
  };
  out := seqBuild(o, v)
};

procedure decode(input: Sequence<int>, maxBytes: int) returns (ok: bool, value: int)
  requires maxBytes >= 1
  opaque
  ensures ok ==> value >= 0
{
  var result: int := 0;
  var scale: int := 1;
  var i: int := 0;
  var done: bool := false;
  ok := false;
  while (!done && i < maxBytes + seqLength(input))
    invariant 0 <= i
    invariant result >= 0
    invariant scale >= 1
  {
    var b: int := seqSelect(input, i);
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: error: precondition does not hold
    if b < 0 || b > 255 then { done := true }
    else {
      result := result + (b % 128) * scale;
      if b < 128 then { ok := true; done := true }
      else { scale := scale * 128; i := i + 1 }
    }
  };
  value := result
};
#end
