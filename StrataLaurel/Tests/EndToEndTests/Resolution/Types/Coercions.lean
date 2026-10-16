/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Resolution-level tests for the proof-relevant coercion judgment (`coerce`) and the frontend
`gradualTypes` hook.

`coerce sub sup` returns *how* one type coerces to another (`refl`/`inject`/`project`/`upcast`/
`widen`) rather than a bare yes/no. This file pins the coercion *decision* at resolution level;
the coercion *realized* end-to-end through Core + SMT is tested in
`Verification/Fundamentals/Coercions.lean`.

The gradual-top blocks (1-2, and 5 at a tuple position) are `testLaurelResolution` on purpose: their
verdict is `inject`/`project` (box into, or unbox out of, the dynamic top), which native Laurel has
no `realizeCoercion` to realize, so carrying them into the full pipeline is out of scope for native
Laurel. End-to-end coercion is exercised via `upcast` (the one non-`refl` verdict native Laurel
realizes, as identity) in the Verification file.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## 1. Without `gradualTypes`: assigning an `int` into a `Foo`-typed slot is a strict type error. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Foo { var a: int }
procedure p() returns (b: bool)
  opaque
  modifies *
{
  var x: Foo := 7;
//              ^ error: expected 'Foo', got 'int'
  true
};
#end

/-! ## 2. With `Foo` in `gradualTypes`: `coerce` accepts the `int` (gradual top), no diagnostic.

`var x: Foo := 7` is a plain initialization of a `Foo`-typed slot with the int `7`. It is NOT a
composite literal — `7` is not assigned to field `a`, and no field write occurs. Because `Foo` is
registered gradual (the dynamic top), `coerce int Foo` succeeds and the `int` flows into the slot
uninterpreted, exactly as block 1's same assignment is REJECTED without the gradual registration.

The gradual verdict here is `inject` (box the `int` into the dynamic top), which native Laurel has
no `realizeCoercion` to realize. Carried into the full pipeline with an identity realizer, the
un-boxed `int` reaches a `Foo` slot and a later pass (`ModifiesClausesTransform` re-resolution)
correctly rejects it (`expected 'Composite', got 'int'`). Realizing the box is the frontend's job
(Python's `realizeCoercion` / `Any` prelude), out of scope here — so end-to-end coercion is
exercised via `upcast` in the Verification file instead. -/

#eval testLaurelResolution (gradualTypes := ({} : Std.HashSet String).insert "Foo") <|
#strata
program Laurel;
composite Foo { var a: int }
procedure p() returns (b: bool)
  opaque
  modifies *
{
  var x: Foo := 7;
  true
};
#end

/-! ## 3. A procedure-output tuple coerces PER POSITION, covariantly.

The positions are independent slots, so each admits a subtype on its own, by the same rule that
lets the one-output `var q2: Animal := g()` take a `Dog`. Both forms are here so the two stay in
step. `h` covers the other way a position can be a subtype — a generic INSTANTIATION, related by
`substitutedAncestors` rather than by the `ancestors` name walk. `assign q4, var m` mixes a
pre-declared target with an unannotated `var`, which is the resolver's OTHER route to the tuple
check: an unannotated target forces the RHS to be synthesized first, so the boundary is enforced by
a trailing `checkSubtype` instead of the usual push-in through `Check.resolveStmtExpr`.

`assign q5, var n` targets a wildcard, which the per-position test admits through `isConsistent`
rather than `isSubtype`, so this line is what rejects narrowing the arm to covariance alone. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { var a: int }
composite Dog extends Animal { var d: int }
composite Box<T> extends Animal { var v: T }
procedure f() returns (r: Dog, i: int) opaque ensures i == 1 { r := new Dog; i := 1 };
procedure g() returns (r: Dog) opaque { r := new Dog };
procedure h() returns (r: Box<int>, i: int) opaque { r := new Box<int>; i := 0 };
procedure p() opaque {
  var q: Animal; var j: int;
  assign q, j := f();
  var q2: Animal := g();
  var q3: Animal; var k: int;
  assign q3, k := h();
  var q4: Animal;
  assign q4, var m := f();
  var q5 := <?>;
  assign q5, var n := f();
  assert m == 1
};
#end

/-! ## 4. Only in the SUBTYPE direction, and only per position.

Covariance changes which pairs relate, not how many positions there are: `zip` truncates, so both
arity directions have to stay rejected. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal2 { var a: int }
composite Dog2 extends Animal2 { var d: int }
procedure widen() returns (r: Animal2, i: int) opaque { r := new Animal2; i := 0 };
procedure pair() returns (a: int, b: bool) opaque { a := 1; b := true };
procedure triple() returns (a: int, b: int, c: int) opaque { a := 1; b := 2; c := 3 };
procedure p2() opaque {
  var narrow: Dog2; var j: int;
  assign narrow, j := widen();
//                    ^^^^^^^ error: expected '(Dog2, int)', got '(Animal2, int)'
  var x: int; var y: int;
  assign x, y := pair();
//               ^^^^^^ error: expected '(int, int)', got '(int, bool)'
  assign x, y := triple();
//               ^^^^^^^^ error: expected '(int, int)', got '(int, int, int)'
  var z: int; var w: int;
  assign x, y, z, w := triple();
//                     ^^^^^^^^ error: expected '(int, int, int, int)', got '(int, int, int)'
  assert 1 == 1
};
#end

/-! ## 5. Block 2's gradual top, at a tuple POSITION, in both directions.

This block is what rejects recursing into `coerce` and filtering the verdicts to `{refl, upcast}`,
and the only thing that does: a registered gradual is the one position shape reachable here whose
own verdict is a box or unbox. §3's `<?>` does not substitute — `coerce Unknown τ` is `refl`. The
other verdict such a filter rejects, `widen`, needs a realizer, which no block in this file
installs; §6 of the Verification file covers it. -/

#eval testLaurelResolution (gradualTypes := ({} : Std.HashSet String).insert "Foo") <|
#strata
program Laurel;
composite Foo { var a: int }
procedure boxed() returns (r: Foo, i: int) opaque { r := new Foo; i := 0 };
procedure plain() returns (r: int, i: int) opaque { r := 0; i := 0 };
procedure p3() opaque {
  var x: int; var j: int;
  assign x, j := boxed();
  var y: Foo; var k: int;
  assign y, k := plain();
  assert 1 == 1
};
#end

