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

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

procedure len(l: IntList, n: int): bool;
procedure valueAt(l: IntList, k: int): int;
procedure suffix(l: IntList, k: int): IntList;

procedure listAxioms(): bool
{
  (forall(n: int) => len(Nil(), n) == (n == 0))
  && (forall(h: int) => forall(t: IntList) => forall(n: int) => len(Cons(h, t), n) == (n >= 1 && len(t, n - 1)))
  && (forall(h: int) => forall(t: IntList) => valueAt(Cons(h, t), 0) == h)
  && (forall(h: int) => forall(t: IntList) => forall(k: int) => k >= 1 ==> valueAt(Cons(h, t), k) == valueAt(t, k - 1))
  && (forall(l: IntList) => suffix(l, 0) == l)
  && (forall(h: int) => forall(t: IntList) => forall(k: int) => k >= 1 ==> suffix(Cons(h, t), k) == suffix(t, k - 1))
};

procedure setAt(l: IntList, n: int, k: int, v: int) returns (res: IntList)
  requires listAxioms()
  requires len(l, n)
  requires 0 <= k && k < n
  opaque
  ensures len(res, n)
  ensures valueAt(res, k) == v
  ensures forall(j: int) => 0 <= j ==> j < n ==> j != k ==> valueAt(res, j) == valueAt(l, j)
  ensures suffix(res, k + 1) == suffix(l, k + 1)
{
  if k == 0 then { res := Cons(v, IntList..tail!(l)) }
  else {
    var rest: IntList := setAt(IntList..tail!(l), n - 1, k - 1, v);
    res := Cons(IntList..head!(l), rest)
  }
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

datatype IntList {
  Nil(),
  Cons(head: int, tail: IntList)
}

procedure len(l: IntList, n: int): bool;
procedure valueAt(l: IntList, k: int): int;
procedure suffix(l: IntList, k: int): IntList;

procedure listAxioms(): bool
{
  (forall(n: int) => len(Nil(), n) == (n == 0))
  && (forall(h: int) => forall(t: IntList) => forall(n: int) => len(Cons(h, t), n) == (n >= 1 && len(t, n - 1)))
  && (forall(h: int) => forall(t: IntList) => valueAt(Cons(h, t), 0) == h)
  && (forall(h: int) => forall(t: IntList) => forall(k: int) => k >= 1 ==> valueAt(Cons(h, t), k) == valueAt(t, k - 1))
  && (forall(l: IntList) => suffix(l, 0) == l)
  && (forall(h: int) => forall(t: IntList) => forall(k: int) => k >= 1 ==> suffix(Cons(h, t), k) == suffix(t, k - 1))
};

procedure setAt(l: IntList, n: int, k: int, v: int) returns (res: IntList)
  requires listAxioms()
  requires len(l, n)
  requires 0 <= k && k < n
  opaque
  ensures len(res, n)
//        ^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures valueAt(res, k) == v
  ensures forall(j: int) => 0 <= j ==> j < n ==> j != k ==> valueAt(res, j) == valueAt(l, j)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
  ensures suffix(res, k + 1) == suffix(l, k + 1)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: error: postcondition does not hold
{
  if k == 0 then { res := Cons(v, l) }
  else {
    var rest: IntList := setAt(IntList..tail!(l), n - 1, k - 1, v);
    res := Cons(IntList..head!(l), rest)
  }
};
#end
