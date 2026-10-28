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

procedure valid(lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(lf) == seqLength(rt)
  && (forall(i: int) => 0 <= i ==> i < seqLength(lf) ==>
        -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(lf) && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(lf))
};

procedure image(fwd: Sequence<int>, o: int): int
  requires o == -1 || (0 <= o && o < seqLength(fwd))
{
  if o == -1 then -1 else seqSelect(fwd, o)
};

procedure isomorphic(lf: Sequence<int>, rt: Sequence<int>, fwd: Sequence<int>, tl: Sequence<int>, tr: Sequence<int>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(fwd) ==> i < seqLength(lf) ==> i < seqLength(rt) ==> seqSelect(fwd, i) != -1 ==>
    -1 <= seqSelect(lf, i) ==> seqSelect(lf, i) < seqLength(fwd) ==> -1 <= seqSelect(rt, i) ==> seqSelect(rt, i) < seqLength(fwd) ==>
    0 <= seqSelect(fwd, i) && seqSelect(fwd, i) < seqLength(tl) && seqSelect(fwd, i) < seqLength(tr)
    && seqSelect(tl, seqSelect(fwd, i)) == image(fwd, seqSelect(lf, i))
    && seqSelect(tr, seqSelect(fwd, i)) == image(fwd, seqSelect(rt, i))
};

procedure injective(fwd: Sequence<int>): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i < j ==> j < seqLength(fwd) ==> seqSelect(fwd, i) != -1 ==>
    seqSelect(fwd, i) != seqSelect(fwd, j)
};

procedure collect(lf: Sequence<int>, rt: Sequence<int>, root: int)
  returns (fwd: Sequence<int>, tl: Sequence<int>, tr: Sequence<int>)
  requires valid(lf, rt)
  requires 0 <= root && root < seqLength(lf)
  opaque
  ensures isomorphic(lf, rt, fwd, tl, tr)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
  ensures injective(fwd)
//        ^^^^^^^^^^^^^^ error: postcondition could not be proved
// desired: verifies
{
  var f: Sequence<int> := seqEmpty();
  var x: int := 0;
  while (x < seqLength(lf))
    invariant 0 <= x
    invariant x <= seqLength(lf)
    invariant seqLength(f) == x
  {
    f := seqBuild(f, -1);
    x := x + 1
  };
  var from: Sequence<int> := seqBuild(seqEmpty(), root);
  var l: Sequence<int> := seqBuild(seqEmpty(), seqSelect(lf, root));
  var r: Sequence<int> := seqBuild(seqEmpty(), seqSelect(rt, root));
  f := seqUpdate(f, root, 0);
  var scan: int := 0;
  while (scan < seqLength(l))
    invariant 0 <= scan
    invariant scan <= seqLength(l)
    invariant seqLength(l) == seqLength(r)
    invariant seqLength(from) == seqLength(l)
    invariant seqLength(f) == seqLength(lf)
  {
    var a: int := seqSelect(l, scan);
    if a != -1 then {
      if seqSelect(f, a) == -1 then {
//       ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        f := seqUpdate(f, a, seqLength(l));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        from := seqBuild(from, a);
        l := seqBuild(l, seqSelect(lf, a));
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        r := seqBuild(r, seqSelect(rt, a))
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      };
      l := seqUpdate(l, scan, seqSelect(f, a))
//                            ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    };
    var b: int := seqSelect(r, scan);
    if b != -1 then {
      if seqSelect(f, b) == -1 then {
//       ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        f := seqUpdate(f, b, seqLength(l));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        from := seqBuild(from, b);
        l := seqBuild(l, seqSelect(lf, b));
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
        r := seqBuild(r, seqSelect(rt, b))
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
      };
      r := seqUpdate(r, scan, seqSelect(f, b))
//                            ^^^^^^^^^^^^^^^ error: precondition could not be proved
// desired: verifies
    };
    scan := scan + 1
  };
  fwd := f;
  tl := l;
  tr := r
};
#end

#eval testLaurelVerification (options := benchmarkOptions) <|
#strata
program Laurel;
// desired: refuted

procedure valid(lf: Sequence<int>, rt: Sequence<int>): bool
{
  seqLength(lf) == seqLength(rt)
  && (forall(i: int) => 0 <= i ==> i < seqLength(lf) ==>
        -1 <= seqSelect(lf, i) && seqSelect(lf, i) < seqLength(lf) && -1 <= seqSelect(rt, i) && seqSelect(rt, i) < seqLength(lf))
};

procedure image(fwd: Sequence<int>, o: int): int
  requires o == -1 || (0 <= o && o < seqLength(fwd))
{
  if o == -1 then -1 else seqSelect(fwd, o)
};

procedure isomorphic(lf: Sequence<int>, rt: Sequence<int>, fwd: Sequence<int>, tl: Sequence<int>, tr: Sequence<int>): bool
{
  forall(i: int) => 0 <= i ==> i < seqLength(fwd) ==> i < seqLength(lf) ==> i < seqLength(rt) ==> seqSelect(fwd, i) != -1 ==>
    -1 <= seqSelect(lf, i) ==> seqSelect(lf, i) < seqLength(fwd) ==> -1 <= seqSelect(rt, i) ==> seqSelect(rt, i) < seqLength(fwd) ==>
    0 <= seqSelect(fwd, i) && seqSelect(fwd, i) < seqLength(tl) && seqSelect(fwd, i) < seqLength(tr)
    && seqSelect(tl, seqSelect(fwd, i)) == image(fwd, seqSelect(lf, i))
    && seqSelect(tr, seqSelect(fwd, i)) == image(fwd, seqSelect(rt, i))
};

procedure injective(fwd: Sequence<int>): bool
{
  forall(i: int) => forall(j: int) => 0 <= i ==> i < j ==> j < seqLength(fwd) ==> seqSelect(fwd, i) != -1 ==>
    seqSelect(fwd, i) != seqSelect(fwd, j)
};

procedure collect(lf: Sequence<int>, rt: Sequence<int>, root: int)
  returns (fwd: Sequence<int>, tl: Sequence<int>, tr: Sequence<int>)
  requires valid(lf, rt)
  requires 0 <= root && root < seqLength(lf)
  opaque
  ensures isomorphic(lf, rt, fwd, tl, tr)
//        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: postcondition could not be proved
  ensures injective(fwd)
//        ^^^^^^^^^^^^^^ error: postcondition could not be proved
{
  var f: Sequence<int> := seqEmpty();
  var x: int := 0;
  while (x < seqLength(lf))
    invariant 0 <= x
    invariant x <= seqLength(lf)
    invariant seqLength(f) == x
  {
    f := seqBuild(f, -1);
    x := x + 1
  };
  var from: Sequence<int> := seqBuild(seqEmpty(), root);
  var l: Sequence<int> := seqBuild(seqEmpty(), seqSelect(lf, root));
  var r: Sequence<int> := seqBuild(seqEmpty(), seqSelect(rt, root));
  f := seqUpdate(f, root, 0);
  var scan: int := 0;
  while (scan < seqLength(l))
    invariant 0 <= scan
    invariant scan <= seqLength(l)
    invariant seqLength(l) == seqLength(r)
    invariant seqLength(from) == seqLength(l)
    invariant seqLength(f) == seqLength(lf)
  {
    var a: int := seqSelect(l, scan);
    if a != -1 then {
      if seqSelect(f, a) == -1 then {
//       ^^^^^^^^^^^^^^^ error: precondition could not be proved
        f := seqUpdate(f, a, seqLength(l));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        from := seqBuild(from, a);
        l := seqBuild(l, seqSelect(lf, a));
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
        r := seqBuild(r, seqSelect(rt, a))
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
      };
      l := l
    };
    var b: int := seqSelect(r, scan);
    if b != -1 then {
      if seqSelect(f, b) == -1 then {
//       ^^^^^^^^^^^^^^^ error: precondition could not be proved
        f := seqUpdate(f, b, seqLength(l));
//      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
        from := seqBuild(from, b);
        l := seqBuild(l, seqSelect(lf, b));
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
        r := seqBuild(r, seqSelect(rt, b))
//                       ^^^^^^^^^^^^^^^^ error: precondition could not be proved
      };
      r := seqUpdate(r, scan, seqSelect(f, b))
//                            ^^^^^^^^^^^^^^^ error: precondition could not be proved
    };
    scan := scan + 1
  };
  fwd := f;
  tl := l;
  tr := r
};
#end
