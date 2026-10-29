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

procedure square(m: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(m) == n && (forall(r: int) => 0 <= r ==> r < n ==> seqLength(seqSelect(m, r)) == n)
};

procedure at(m: Sequence<Sequence<int>>, r: int, c: int): int
  requires 0 <= r && r < seqLength(m) && 0 <= c && c < seqLength(seqSelect(m, r))
{
  seqSelect(seqSelect(m, r), c)
};

procedure dot(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, i: int, j: int, k: int): int;

procedure dotAxioms(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int): bool
{
  (forall(i: int) => forall(j: int) => dot(a, b, i, j, 0) == 0)
  && (forall(i: int) => forall(j: int) => forall(k: int) =>
        square(a, n) ==> square(b, n) ==> 0 <= i ==> i < n ==> 0 <= j ==> j < n ==> 1 <= k ==> k <= n ==>
          dot(a, b, i, j, k) == dot(a, b, i, j, k - 1) + at(a, i, k - 1) * at(b, k - 1, j))
};

procedure rowsHaveLength(m: Sequence<Sequence<int>>, n: int, rows: int): bool
{
  forall(r: int) => 0 <= r ==> r < rows ==> r < seqLength(m) ==> seqLength(seqSelect(m, r)) == n
};

procedure rowIsProduct(row: Sequence<int>, a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, i: int, n: int, cols: int): bool
{
  forall(c: int) => 0 <= c ==> c < cols ==> c < seqLength(row) ==> seqSelect(row, c) == dot(a, b, i, c, n)
};

procedure isProduct(res: Sequence<Sequence<int>>, a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int, rows: int): bool
{
  forall(r: int) => 0 <= r ==> r < rows ==> r < seqLength(res) ==> rowIsProduct(seqSelect(res, r), a, b, r, n, n)
};

procedure multiply(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int) returns (res: Sequence<Sequence<int>>)
  requires n >= 0
  requires square(a, n)
  requires square(b, n)
  requires dotAxioms(a, b, n)
  opaque
  ensures square(res, n)
  ensures isProduct(res, a, b, n, n)
{
  var out: Sequence<Sequence<int>> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant seqLength(out) == i
    invariant rowsHaveLength(out, n, i)
    invariant isProduct(out, a, b, n, i)
  {
    var row: Sequence<int> := seqEmpty();
    var j: int := 0;
    while (j < n)
      invariant 0 <= j
      invariant j <= n
      invariant seqLength(row) == j
      invariant rowIsProduct(row, a, b, i, n, j)
    {
      var s: int := 0;
      var k: int := 0;
      while (k < n)
        invariant 0 <= k
        invariant k <= n
        invariant s == dot(a, b, i, j, k)
      {
        s := s + at(a, i, k) * at(b, k, j);
        k := k + 1
      };
      row := seqBuild(row, s);
      j := j + 1
    };
    out := seqBuild(out, row);
    i := i + 1
  };
  res := out
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure square(m: Sequence<Sequence<int>>, n: int): bool
{
  seqLength(m) == n && (forall(r: int) => 0 <= r ==> r < n ==> seqLength(seqSelect(m, r)) == n)
};

procedure at(m: Sequence<Sequence<int>>, r: int, c: int): int
  requires 0 <= r && r < seqLength(m) && 0 <= c && c < seqLength(seqSelect(m, r))
{
  seqSelect(seqSelect(m, r), c)
};

procedure dot(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, i: int, j: int, k: int): int;

procedure dotAxioms(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int): bool
{
  (forall(i: int) => forall(j: int) => dot(a, b, i, j, 0) == 0)
  && (forall(i: int) => forall(j: int) => forall(k: int) =>
        square(a, n) ==> square(b, n) ==> 0 <= i ==> i < n ==> 0 <= j ==> j < n ==> 1 <= k ==> k <= n ==>
          dot(a, b, i, j, k) == dot(a, b, i, j, k - 1) + at(a, i, k - 1) * at(b, k - 1, j))
};

procedure rowsHaveLength(m: Sequence<Sequence<int>>, n: int, rows: int): bool
{
  forall(r: int) => 0 <= r ==> r < rows ==> r < seqLength(m) ==> seqLength(seqSelect(m, r)) == n
};

procedure rowIsProduct(row: Sequence<int>, a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, i: int, n: int, cols: int): bool
{
  forall(c: int) => 0 <= c ==> c < cols ==> c < seqLength(row) ==> seqSelect(row, c) == dot(a, b, i, c, n)
};

procedure isProduct(res: Sequence<Sequence<int>>, a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int, rows: int): bool
{
  forall(r: int) => 0 <= r ==> r < rows ==> r < seqLength(res) ==> rowIsProduct(seqSelect(res, r), a, b, r, n, n)
};

procedure multiply(a: Sequence<Sequence<int>>, b: Sequence<Sequence<int>>, n: int) returns (res: Sequence<Sequence<int>>)
  requires n >= 0
  requires square(a, n)
  requires square(b, n)
  requires dotAxioms(a, b, n)
  opaque
  ensures square(res, n)
  ensures isProduct(res, a, b, n, n)
{
  var out: Sequence<Sequence<int>> := seqEmpty();
  var i: int := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant seqLength(out) == i
    invariant rowsHaveLength(out, n, i)
    invariant isProduct(out, a, b, n, i)
  {
    var row: Sequence<int> := seqEmpty();
    var j: int := 0;
    while (j < n)
      invariant 0 <= j
      invariant j <= n
      invariant seqLength(row) == j
      invariant rowIsProduct(row, a, b, i, n, j)
    {
      var s: int := 0;
      var k: int := 0;
      while (k < n)
        invariant 0 <= k
        invariant k <= n
        invariant s == dot(a, b, i, j, k)
//                ^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: error: assertion does not hold
      {
        s := s + at(a, i, k) * at(b, j, k);
        k := k + 1
      };
      row := seqBuild(row, s);
      j := j + 1
    };
    out := seqBuild(out, row);
    i := i + 1
  };
  res := out
};
#end
