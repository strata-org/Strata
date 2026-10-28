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

procedure closedWorld(lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(lf) == seqLength(rt)
  && (forall(i: int) => 0 <= i ==> i < seqLength(lf) ==>
        -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(lf) && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(lf))
};

procedure markClosed(lf: Sequence<int>, rt: Sequence<int>, mk: Sequence<bool>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(mk) ==> i < seqLength(lf) ==> i < seqLength(rt) ==> seqSelect(mk, i) ==>
    (seqSelect(lf, i) == -1 || (0 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(mk) && seqSelect(mk, seqSelect(lf, i))))
    && (seqSelect(rt, i) == -1 || (0 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(mk) && seqSelect(mk, seqSelect(rt, i))))
};

procedure samePointers(a: Sequence<int>, b: Sequence<int>): bool
{
  seqLength(a) == seqLength(b) && (forall(i: int) => 0 <= i ==> i < seqLength(a) ==> seqSelect(a, i) == seqSelect(b, i))
};

procedure noneMarked(mk: Sequence<bool>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(mk) ==> !seqSelect(mk, i)
};

procedure mark(lf0: Sequence<int>, rt0: Sequence<int>, mk0: Sequence<bool>, root: int)
  returns (lf: Sequence<int>, rt: Sequence<int>, mk: Sequence<bool>)
  requires closedWorld(lf0, rt0)
  requires seqLength(mk0) == seqLength(lf0)
  requires noneMarked(mk0)
  requires -1 <= root && root < seqLength(lf0)
  opaque
  ensures root == -1 || seqSelect(mk, root)
//                      ^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
  ensures markClosed(lf, rt, mk)
  ensures samePointers(lf, lf0)
  ensures samePointers(rt, rt0)
{
  var l: Sequence<int> := lf0;
  var r: Sequence<int> := rt0;
  var m: Sequence<bool> := mk0;
  var vr: Sequence<bool> := mk0;
  var t: int := root;
  var p: int := -1;
  while (p != -1 || (t != -1 && !seqSelect(m, t)))
    invariant closedWorld(l, r)
    invariant seqLength(m) == seqLength(l)
    invariant seqLength(vr) == seqLength(l)
    invariant -1 <= t && t < seqLength(l)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
    invariant -1 <= p && p < seqLength(l)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
// desired: verifies
  {
    if t == -1 || seqSelect(m, t) then {
      if seqSelect(vr, p) then {
//       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        var q: int := t;
        t := p;
        p := seqSelect(r, p);
//      ^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        r := seqUpdate(r, t, q)
//      ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      } else {
        var q: int := t;
        t := seqSelect(r, p);
//      ^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        r := seqUpdate(r, p, seqSelect(l, p));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                           ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        l := seqUpdate(l, p, q);
//      ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        vr := seqUpdate(vr, p, true)
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      }
    } else {
      var q: int := p;
      p := t;
      t := seqSelect(l, t);
      l := seqUpdate(l, p, q);
      m := seqUpdate(m, p, true);
      vr := seqUpdate(vr, p, false)
    }
  };
  lf := l;
  rt := r;
  mk := m
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure closedWorld(lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(lf) == seqLength(rt)
  && (forall(i: int) => 0 <= i ==> i < seqLength(lf) ==>
        -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(lf) && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(lf))
};

procedure markClosed(lf: Sequence<int>, rt: Sequence<int>, mk: Sequence<bool>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(mk) ==> i < seqLength(lf) ==> i < seqLength(rt) ==> seqSelect(mk, i) ==>
    (seqSelect(lf, i) == -1 || (0 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(mk) && seqSelect(mk, seqSelect(lf, i))))
    && (seqSelect(rt, i) == -1 || (0 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(mk) && seqSelect(mk, seqSelect(rt, i))))
};

procedure samePointers(a: Sequence<int>, b: Sequence<int>): bool
{
  seqLength(a) == seqLength(b) && (forall(i: int) => 0 <= i ==> i < seqLength(a) ==> seqSelect(a, i) == seqSelect(b, i))
};

procedure noneMarked(mk: Sequence<bool>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(mk) ==> !seqSelect(mk, i)
};

procedure mark(lf0: Sequence<int>, rt0: Sequence<int>, mk0: Sequence<bool>, root: int)
  returns (lf: Sequence<int>, rt: Sequence<int>, mk: Sequence<bool>)
  requires closedWorld(lf0, rt0)
  requires seqLength(mk0) == seqLength(lf0)
  requires noneMarked(mk0)
  requires -1 <= root && root < seqLength(lf0)
  opaque
  ensures root == -1 || seqSelect(mk, root)
//                      ^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
  ensures markClosed(lf, rt, mk)
  ensures samePointers(lf, lf0)
  ensures samePointers(rt, rt0)
// desired: error: postcondition could not be proved
{
  var l: Sequence<int> := lf0;
  var r: Sequence<int> := rt0;
  var m: Sequence<bool> := mk0;
  var vr: Sequence<bool> := mk0;
  var t: int := root;
  var p: int := -1;
  while (p != -1 || (t != -1 && !seqSelect(m, t)))
    invariant closedWorld(l, r)
    invariant seqLength(m) == seqLength(l)
    invariant seqLength(vr) == seqLength(l)
    invariant -1 <= t && t < seqLength(l)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
    invariant -1 <= p && p < seqLength(l)
//            ^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
  {
    if t == -1 || seqSelect(m, t) then {
      if seqSelect(vr, p) then {
//       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
        var q: int := t;
        t := p;
        p := seqSelect(r, p);
//      ^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        r := seqUpdate(r, t, p)
//      ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      } else {
        var q: int := t;
        t := seqSelect(r, p);
//      ^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        r := seqUpdate(r, p, seqSelect(l, p));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
//                           ^^^^^^^^^^^^^^^ error: precondition could not be proved
        l := seqUpdate(l, p, q);
//      ^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        vr := seqUpdate(vr, p, true)
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
      }
    } else {
      var q: int := p;
      p := t;
      t := seqSelect(l, t);
      l := seqUpdate(l, p, q);
      m := seqUpdate(m, p, true);
      vr := seqUpdate(vr, p, false)
    }
  };
  lf := l;
  rt := r;
  mk := m
};
#end
