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

Both blocks below are `testLaurelResolution` on purpose: the gradual-top verdict here is `inject`
(box the `int` into the dynamic top), which native Laurel has no `realizeCoercion` to realize, so
carrying it into the full pipeline is out of scope for native Laurel. End-to-end coercion is
exercised via `upcast` (the one non-`refl` verdict native Laurel realizes, as identity) in the
Verification file.
-/

import StrataTest.Util.TestLaurel

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
