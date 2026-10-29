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

composite Ring {
  var buf: Sequence<int>
  var head: int
  var count: int
}

procedure inRange(q: Ring): bool
{
  seqLength(q#buf) > 0 && 0 <= q#head && q#head < seqLength(q#buf) && 0 <= q#count && q#count <= seqLength(q#buf)
};

procedure elementAt(buf: Sequence<int>, head: int, k: int): int
  requires seqLength(buf) > 0 && 0 <= head && 0 <= k
{
  seqSelect(buf, (head + k) % seqLength(buf))
};

procedure push(q: Ring, v: int)
  requires inRange(q)
  requires q#count < seqLength(q#buf)
  opaque
  ensures inRange(q)
  ensures q#count == old(q#count) + 1
  ensures elementAt(q#buf, q#head, q#count - 1) == v
  modifies q
{
  q#buf := seqUpdate(q#buf, (q#head + q#count) % seqLength(q#buf), v);
  q#count := q#count + 1
};

procedure pop(q: Ring) returns (r: int)
  requires inRange(q)
  requires q#count > 0
  opaque
  ensures inRange(q)
  ensures r == old(elementAt(q#buf, q#head, 0))
  ensures q#count == old(q#count) - 1
  modifies q
{
  r := seqSelect(q#buf, q#head);
  q#head := (q#head + 1) % seqLength(q#buf);
  q#count := q#count - 1
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Ring {
  var buf: Sequence<int>
  var head: int
  var count: int
}

procedure inRange(q: Ring): bool
{
  seqLength(q#buf) > 0 && 0 <= q#head && q#head < seqLength(q#buf) && 0 <= q#count && q#count <= seqLength(q#buf)
};

procedure elementAt(buf: Sequence<int>, head: int, k: int): int
  requires seqLength(buf) > 0 && 0 <= head && 0 <= k
{
  seqSelect(buf, (head + k) % seqLength(buf))
};

procedure push(q: Ring, v: int)
  requires inRange(q)
  requires q#count < seqLength(q#buf)
  opaque
  ensures inRange(q)
  ensures q#count == old(q#count) + 1
  ensures elementAt(q#buf, q#head, q#count - 1) == v
  modifies q
{
  q#buf := seqUpdate(q#buf, (q#head + q#count) % seqLength(q#buf), v);
  q#count := q#count + 1
};

procedure pop(q: Ring) returns (r: int)
  requires inRange(q)
  requires q#count > 0
  opaque
  ensures inRange(q)
//        ^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures r == old(elementAt(q#buf, q#head, 0))
  ensures q#count == old(q#count) - 1
  modifies q
{
  r := seqSelect(q#buf, q#head);
  q#head := q#head + 1;
  q#count := q#count - 1
};
#end
