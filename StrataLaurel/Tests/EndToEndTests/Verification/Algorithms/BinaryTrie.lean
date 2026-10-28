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

procedure stored(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, n: int, w: Sequence<int>, d: int): bool;

procedure trieAxioms(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, w: Sequence<int>): bool
{
  seqLength(c0) == seqLength(c1) && seqLength(c1) == seqLength(term)
  && (forall(d: int) => !stored(c0, c1, term, -1, w, d))
  && (forall(n: int) => forall(d: int) => 0 <= n ==> n < seqLength(c0) ==> d == seqLength(w) ==>
        stored(c0, c1, term, n, w, d) == seqSelect(term, n))
  && (forall(n: int) => forall(d: int) => 0 <= n ==> n < seqLength(c0) ==> 0 <= d ==> d < seqLength(w) ==>
        stored(c0, c1, term, n, w, d) ==
          stored(c0, c1, term, if seqSelect(w, d) == 0 then seqSelect(c0, n) else seqSelect(c1, n), w, d + 1))
};

procedure validChildren(c0: Sequence<int>, c1: Sequence<int>): bool
{
  forall(n: int) => 0 <= n ==> n < seqLength(c0) ==> n < seqLength(c1) ==>
    -1 <= seqSelect(c0, n) && seqSelect(c0, n) < seqLength(c0) && -1 <= seqSelect(c1, n) && seqSelect(c1, n) < seqLength(c0)
};

procedure contains(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, root: int, w: Sequence<int>) returns (r: bool)
  requires trieAxioms(c0, c1, term, w)
  requires validChildren(c0, c1)
  requires 0 <= root
  requires root < seqLength(c0)
  opaque
  ensures r == stored(c0, c1, term, root, w, 0)
{
  var cur: int := root;
  var d: int := 0;
  while (cur != -1 && d < seqLength(w))
    invariant 0 <= d
    invariant d <= seqLength(w)
    invariant -1 <= cur
    invariant cur < seqLength(c0)
    invariant stored(c0, c1, term, root, w, 0) == stored(c0, c1, term, cur, w, d)
  {
    if seqSelect(w, d) == 0 then { cur := seqSelect(c0, cur) } else { cur := seqSelect(c1, cur) };
    d := d + 1
  };
  r := cur != -1 && seqSelect(term, cur)
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure stored(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, n: int, w: Sequence<int>, d: int): bool;

procedure trieAxioms(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, w: Sequence<int>): bool
{
  seqLength(c0) == seqLength(c1) && seqLength(c1) == seqLength(term)
  && (forall(d: int) => !stored(c0, c1, term, -1, w, d))
  && (forall(n: int) => forall(d: int) => 0 <= n ==> n < seqLength(c0) ==> d == seqLength(w) ==>
        stored(c0, c1, term, n, w, d) == seqSelect(term, n))
  && (forall(n: int) => forall(d: int) => 0 <= n ==> n < seqLength(c0) ==> 0 <= d ==> d < seqLength(w) ==>
        stored(c0, c1, term, n, w, d) ==
          stored(c0, c1, term, if seqSelect(w, d) == 0 then seqSelect(c0, n) else seqSelect(c1, n), w, d + 1))
};

procedure validChildren(c0: Sequence<int>, c1: Sequence<int>): bool
{
  forall(n: int) => 0 <= n ==> n < seqLength(c0) ==> n < seqLength(c1) ==>
    -1 <= seqSelect(c0, n) && seqSelect(c0, n) < seqLength(c0) && -1 <= seqSelect(c1, n) && seqSelect(c1, n) < seqLength(c0)
};

procedure contains(c0: Sequence<int>, c1: Sequence<int>, term: Sequence<bool>, root: int, w: Sequence<int>) returns (r: bool)
  requires trieAxioms(c0, c1, term, w)
  requires validChildren(c0, c1)
  requires 0 <= root
  requires root < seqLength(c0)
  opaque
  ensures r == stored(c0, c1, term, root, w, 0)
{
  var cur: int := root;
  var d: int := 0;
  while (cur != -1 && d < seqLength(w))
    invariant 0 <= d
    invariant d <= seqLength(w)
    invariant -1 <= cur
    invariant cur < seqLength(c0)
    invariant stored(c0, c1, term, root, w, 0) == stored(c0, c1, term, cur, w, d)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
  {
    if seqSelect(w, d) == 0 then { cur := seqSelect(c1, cur) } else { cur := seqSelect(c0, cur) };
    d := d + 1
  };
  r := cur != -1 && seqSelect(term, cur)
};
#end
