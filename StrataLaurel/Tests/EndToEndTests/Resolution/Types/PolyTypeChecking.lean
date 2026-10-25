/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Polymorphism did not weaken the type checker

Supporting polymorphic procedures meant adding type-variable arms to the consistency relation:
a `.TVar` is consistent with anything, `.Applied` recurses into its arguments, and a bare
datatype or composite name relates to an instantiation of the same base. Each of those is a
place where the relation says "yes" more often than before, and the failure mode is silent —
a relation that is too permissive makes every accepting test pass MORE easily, so no
accept-side test can detect it.

So this file is entirely reject-side. Each program is type-incorrect and must still be
rejected; if any of them starts translating, the corresponding arm has been over-relaxed.

The cases are ordered from "nothing to do with polymorphism" outward, because the first two
are the control: if the type checker had been broken outright, those would leak first.
-/

/-! ## Controls: ordinary type errors, with no type variable anywhere -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure primitiveMismatch() opaque {
  var x: int := true;
//              ^^^^ error: expected 'int', got 'bool'
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var a: int }
composite Cat { var b: int }

procedure crossCompositeMismatch()
  opaque
  modifies *
{
  var x: Dog := new Cat;
//              ^^^^^^^ error: expected 'Dog', got 'Cat'
  assert 1 == 1
};
#end

/-! ## The recursive `.Applied` arm stays strict at concrete arguments

The arm exists so a `Box<T>` parameter can accept a `Box<int>` argument. Recursing means it
reaches the arguments — and once there, two CONCRETE arguments have to be compared, not waved
through. Assignment and argument passing are both covered, since they consult the relation from
different places. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure appliedArmAssignment()
  opaque
  modifies *
{
  var a: Box<int> := new Box<int>;
  var b: Box<bool> := a;
//                    ^ error: expected 'Box<bool>', got 'Box<int>'
  assert 1 == 1
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }
procedure needsBool(b: Box<bool>) opaque { assert 1 == 1 };

procedure appliedArmArgument()
  opaque
  modifies *
{
  var a: Box<int> := new Box<int>;
  needsBool(a);
//          ^ error: expected 'Box<bool>', got 'Box<int>'
  assert 1 == 1
};
#end

/-! ## The bare-name arm fires only on a MATCHING base

`new Box` without arguments produces the bare name `Box`, which has to relate to `Box<int>` —
that is what makes the legacy allocation form work. The arm must key on the base name, so a
bare `Dog` does not relate to `Box<int>` just by virtue of being bare. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Dog { var a: int }

procedure bareNameWrongBase()
  opaque
  modifies *
{
  var b: Box<int> := new Dog;
//                   ^^^^^^^ error: expected 'Box<int>', got 'Dog'
  assert 1 == 1
};
#end

/-! ## The `.TVar` wildcard does not disable checking inside a polymorphic body

This is the most dangerous of the arms. `T` is consistent with everything, and it is in scope
throughout the procedure — so a wildcard applied too broadly would turn the whole body into an
unchecked region. The error below has nothing to do with `T`; it just happens to be inside a
procedure that has one. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure inPolyBody<T>(x: T) returns (r: T)
  opaque
  ensures r == x
{
  var y: int := true;
//              ^^^^ error: expected 'int', got 'bool'
  r := x
};
#end

/-! ## An ill-typed polymorphic FUNCTION is reported, not thrown

`coerce<A, B>(x: A): B` returns an `A` where a `B` is required. Laurel's own relation lets it
through — `A` and `B` are both type variables, so both are wildcards — and Core is what catches
it. The point of pinning it here is the REPORTING path: the Core type error has to come back as
a diagnostic rather than as a thrown exception, or a front end driving the pipeline gets a crash
instead of a message.

This check belongs in Laurel resolution. Two distinct type variables in a signature are not
interchangeable, and returning an `A` where the signature promises a `B` is decidable from the
signature alone — no Core needed. Because resolution does not check it, the case reports
nothing under `testLaurelResolution` and has to run the full pipeline here. Moving the check
into resolution would let this join the rest of the file on `testLaurelResolution`, and would
report the error in Laurel's vocabulary instead of as a generic Core type error.

No interpreters: the Core path is rejected by Core's type checker, so there is nothing to
run — and the standalone Laurel interpreter never type-checks through Core, so an `entry` on
`main` there would run the program and report nothing, leaving the annotation unfired. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure coerce<A, B>(x: A): B { return x };
//        ^^^^^^ error: ❌ Type checking error.
procedure main() opaque { assert 1 == 1 };
#end
