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

composite Queue {
  var front: Sequence<int>
  var back: Sequence<int>
}

procedure elementAt(front: Sequence<int>, back: Sequence<int>, k: int): int
{
  if k < seqLength(front) then seqSelect(front, seqLength(front) - 1 - k) else seqSelect(back, k - seqLength(front))
//                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
};

procedure enqueue(q: Queue, v: int)
  opaque
  ensures seqLength(q#front) + seqLength(q#back) == old(seqLength(q#front) + seqLength(q#back)) + 1
  ensures elementAt(q#front, q#back, seqLength(q#front) + seqLength(q#back) - 1) == v
  modifies q
{
  q#back := seqBuild(q#back, v)
};

procedure dequeue(q: Queue) returns (r: int)
  requires seqLength(q#front) + seqLength(q#back) > 0
  opaque
  ensures r == old(elementAt(q#front, q#back, 0))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures seqLength(q#front) + seqLength(q#back) == old(seqLength(q#front) + seqLength(q#back)) - 1
  modifies q
{
  if seqLength(q#front) == 0 then {
    var moved: Sequence<int> := seqEmpty();
    var i: int := 0;
    while (i < seqLength(q#back))
      invariant 0 <= i
      invariant i <= seqLength(q#back)
      invariant seqLength(moved) == i
    {
      moved := seqBuild(moved, seqSelect(q#back, seqLength(q#back) - 1 - i));
      i := i + 1
    };
    q#front := moved;
    q#back := seqEmpty()
  };
  r := seqSelect(q#front, seqLength(q#front) - 1);
  q#front := seqTake(q#front, seqLength(q#front) - 1)
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

composite Queue {
  var front: Sequence<int>
  var back: Sequence<int>
}

procedure elementAt(front: Sequence<int>, back: Sequence<int>, k: int): int
{
  if k < seqLength(front) then seqSelect(front, seqLength(front) - 1 - k) else seqSelect(back, k - seqLength(front))
//                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                                                                             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

procedure enqueue(q: Queue, v: int)
  opaque
  ensures seqLength(q#front) + seqLength(q#back) == old(seqLength(q#front) + seqLength(q#back)) + 1
  ensures elementAt(q#front, q#back, seqLength(q#front) + seqLength(q#back) - 1) == v
  modifies q
{
  q#back := seqBuild(q#back, v)
};

procedure dequeue(q: Queue) returns (r: int)
  requires seqLength(q#front) + seqLength(q#back) > 0
  opaque
  ensures r == old(elementAt(q#front, q#back, 0))
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures seqLength(q#front) + seqLength(q#back) == old(seqLength(q#front) + seqLength(q#back)) - 1
  modifies q
{
  if seqLength(q#front) == 0 then {
    var moved: Sequence<int> := seqEmpty();
    var i: int := 0;
    while (i < seqLength(q#back))
      invariant 0 <= i
      invariant i <= seqLength(q#back)
      invariant seqLength(moved) == i
    {
      moved := seqBuild(moved, seqSelect(q#back, i));
      i := i + 1
    };
    q#front := moved;
    q#back := seqEmpty()
  };
  r := seqSelect(q#front, seqLength(q#front) - 1);
  q#front := seqTake(q#front, seqLength(q#front) - 1)
};
#end
