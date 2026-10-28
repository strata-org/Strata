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

procedure sameBelow(a: Sequence<int>, b: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> k < seqLength(b) ==> seqSelect(a, k) == seqSelect(b, k)
};

procedure symbol(x: int): int
{
  if x < 26 then 65 + x else if x < 52 then 97 + x - 26 else if x < 62 then 48 + x - 52 else if x == 62 then 43 else 47
};

procedure sextet(c: int): int
{
  if 65 <= c && c <= 90 then c - 65
  else if 97 <= c && c <= 122 then c - 97 + 26
  else if 48 <= c && c <= 57 then c - 48 + 52
  else if c == 43 then 62 else if c == 47 then 63 else -1
};

procedure padOf(text: Sequence<int>): int
  requires seqLength(text) % 4 == 0
{
  if seqLength(text) == 0 then 0
  else (if seqSelect(text, seqLength(text) - 1) == 61 then 1 else 0) + (if seqSelect(text, seqLength(text) - 2) == 61 then 1 else 0)
};

procedure encode(data: Sequence<int>) returns (out: Sequence<int>)
  requires bytes(data)
  opaque
  ensures seqLength(out) == ((seqLength(data) + 2) / 3) * 4
  ensures padOf(out) == (3 - seqLength(data) % 3) % 3
{
  var o: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i + 2 < seqLength(data))
    invariant 0 <= i
    invariant i % 3 == 0
    invariant i <= seqLength(data)
    invariant seqLength(o) == i / 3 * 4
    invariant i > 0 ==> seqSelect(o, seqLength(o) - 1) != 61 && seqSelect(o, seqLength(o) - 2) != 61
  {
    var t: int := seqSelect(data, i) * 65536 + seqSelect(data, i + 1) * 256 + seqSelect(data, i + 2);
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), symbol(t / 64 % 64)), symbol(t % 64));
    i := i + 3
  };
  if seqLength(data) - i == 1 then {
    var t: int := seqSelect(data, i) * 65536;
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), 61), 61)
  } else if seqLength(data) - i == 2 then {
    var t: int := seqSelect(data, i) * 65536 + seqSelect(data, i + 1) * 256;
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), symbol(t / 64 % 64)), 61)
  };
  out := o
};

procedure decode(text: Sequence<int>) returns (out: Sequence<int>)
  requires seqLength(text) % 4 == 0
  opaque
  ensures seqLength(out) == seqLength(text) / 4 * 3 - padOf(text)
{
  var n: int := seqLength(text);
  var pad: int := if n == 0 then 0 else (if seqSelect(text, n - 1) == 61 then 1 else 0) + (if seqSelect(text, n - 2) == 61 then 1 else 0);
  var o: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i % 4 == 0
    invariant i <= n
    invariant seqLength(o) == i / 4 * 3
  {
    var s2: int := if seqSelect(text, i + 2) == 61 then 0 else sextet(seqSelect(text, i + 2));
    var s3: int := if seqSelect(text, i + 3) == 61 then 0 else sextet(seqSelect(text, i + 3));
    var t: int := sextet(seqSelect(text, i)) * 262144 + sextet(seqSelect(text, i + 1)) * 4096 + s2 * 64 + s3;
    o := seqBuild(seqBuild(seqBuild(o, t / 65536 % 256), t / 256 % 256), t % 256);
    i := i + 4
  };
  out := seqTake(o, seqLength(o) - pad)
};

procedure roundTrip(data: Sequence<int>)
  requires bytes(data)
  opaque
{
  var text: Sequence<int> := encode(data);
  var back: Sequence<int> := decode(text);
  assert seqLength(back) == seqLength(data);
  assert sameBelow(back, data, seqLength(data))
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;

procedure bytes(s: Sequence<int>): bool
{
  forall(k: int) => 0 <= k ==> k < seqLength(s) ==> 0 <= seqSelect(s, k) && seqSelect(s, k) <= 255
};

procedure sameBelow(a: Sequence<int>, b: Sequence<int>, hi: int): bool
{
  forall(k: int) => 0 <= k ==> k < hi ==> k < seqLength(a) ==> k < seqLength(b) ==> seqSelect(a, k) == seqSelect(b, k)
};

procedure symbol(x: int): int
{
  if x < 26 then 65 + x else if x < 52 then 97 + x - 26 else if x < 62 then 48 + x - 52 else if x == 62 then 43 else 47
};

procedure sextet(c: int): int
{
  if 65 <= c && c <= 90 then c - 65
  else if 97 <= c && c <= 122 then c - 97 + 26
  else if 48 <= c && c <= 57 then c - 48 + 52
  else if c == 43 then 62 else if c == 47 then 63 else -1
};

procedure padOf(text: Sequence<int>): int
  requires seqLength(text) % 4 == 0
{
  if seqLength(text) == 0 then 0
  else (if seqSelect(text, seqLength(text) - 1) == 61 then 1 else 0) + (if seqSelect(text, seqLength(text) - 2) == 61 then 1 else 0)
};

procedure encode(data: Sequence<int>) returns (out: Sequence<int>)
  requires bytes(data)
  opaque
  ensures seqLength(out) == ((seqLength(data) + 2) / 3) * 4
  ensures padOf(out) == (3 - seqLength(data) % 3) % 3
{
  var o: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i + 2 < seqLength(data))
    invariant 0 <= i
    invariant i % 3 == 0
    invariant i <= seqLength(data)
    invariant seqLength(o) == i / 3 * 4
    invariant i > 0 ==> seqSelect(o, seqLength(o) - 1) != 61 && seqSelect(o, seqLength(o) - 2) != 61
  {
    var t: int := seqSelect(data, i) * 65536 + seqSelect(data, i + 1) * 256 + seqSelect(data, i + 2);
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), symbol(t / 64 % 64)), symbol(t % 64));
    i := i + 3
  };
  if seqLength(data) - i == 1 then {
    var t: int := seqSelect(data, i) * 65536;
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), 61), 61)
  } else if seqLength(data) - i == 2 then {
    var t: int := seqSelect(data, i) * 65536 + seqSelect(data, i + 1) * 256;
    o := seqBuild(seqBuild(seqBuild(seqBuild(o, symbol(t / 262144)), symbol(t / 4096 % 64)), symbol(t / 64 % 64)), 61)
  };
  out := o
};

procedure decode(text: Sequence<int>) returns (out: Sequence<int>)
  requires seqLength(text) % 4 == 0
  opaque
  ensures seqLength(out) == seqLength(text) / 4 * 3 - padOf(text)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var n: int := seqLength(text);
  var pad: int := if n == 0 then 0 else (if seqSelect(text, n - 1) == 61 then 1 else 0);
  var o: Sequence<int> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i % 4 == 0
    invariant i <= n
    invariant seqLength(o) == i / 4 * 3
  {
    var s2: int := if seqSelect(text, i + 2) == 61 then 0 else sextet(seqSelect(text, i + 2));
    var s3: int := if seqSelect(text, i + 3) == 61 then 0 else sextet(seqSelect(text, i + 3));
    var t: int := sextet(seqSelect(text, i)) * 262144 + sextet(seqSelect(text, i + 1)) * 4096 + s2 * 64 + s3;
    o := seqBuild(seqBuild(seqBuild(o, t / 65536 % 256), t / 256 % 256), t % 256);
    i := i + 4
  };
  out := seqTake(o, seqLength(o) - pad)
};

procedure roundTrip(data: Sequence<int>)
  requires bytes(data)
  opaque
{
  var text: Sequence<int> := encode(data);
  var back: Sequence<int> := decode(text);
  assert seqLength(back) == seqLength(data);
  assert sameBelow(back, data, seqLength(data))
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end
