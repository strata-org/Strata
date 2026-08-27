/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Generic composites through the full pipeline

`UnitTests/GenericCompositeTest.lean` drives generic composites through the corpus
harness, which asserts four counters (`translated`/`numVCs`/`numFailures`/
`numErrorOutcomes`) and — for rejections — a `MessageKind`. It deliberately does not pin
diagnostic LOCATIONS; that file's own `monomorphCollisionIsLocated` helper says so, and
works around it for one case. These tests use the inline-annotation form instead, so a
failure's reported RANGE is part of the expectation and a drift in location fails the
build.

`testLaurelExecution {}`, not `testLaurelExecution { skipCoreInterpreter := false }`: a composite is a heap reference and the concrete
interpreter does not model the heap, so only the verifier path applies here. The
interpreter-covered half of the feature is the value-`T` procedure cases in
`Procedures/PolyProcedure.lean`.

What monomorphization has to get right, and what each case pins:
* one instantiation — the field's declared `T` becomes the concrete type at the clone;
* two instantiations of the SAME composite in one program — the clones must not
  cross-link (a shared field id would make one instantiation's write visible to the other);
* a false twin per shape — so a clone's field read is not left unconstrained, which would
  let a false assertion pass vacuously.

The false twins pin that a clone's field read is constrained: a false assertion fails rather
than passing vacuously (a vacuous pass would show up as no diagnostic at all).
-/

-- Single instantiation: write then read a `T`-typed field at `int`.
#eval testLaurelExecution {}
#strata
program Laurel;
composite Box<T> { var val: T }

procedure oneInstantiation()
  opaque
{
  var b: Box<int> := new Box<int>;
  b#val := 42;
  assert b#val == 42
};
#end

-- SOUNDNESS twin for the read: a FALSE assertion on the instantiated field must fail.
-- If the clone's field type were erased to something unconstrained, this would pass.
#eval testLaurelExecution {}
#strata
program Laurel;
composite Box<T> { var val: T }

procedure oneInstantiationFalse()
  opaque
{
  var b: Box<int> := new Box<int>;
  b#val := 42;
  assert b#val == 43
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- TWO instantiations of one generic composite in a single program. The keystone: each
-- clone must own its own field, so writing through the `int` instance cannot be observed
-- through the `bool` one. Cross-linked clone ids would break this.
#eval testLaurelExecution {}
#strata
program Laurel;
composite Box<T> { var val: T }

procedure twoInstantiations()
  opaque
{
  var bi: Box<int> := new Box<int>;
  var bb: Box<bool> := new Box<bool>;
  bi#val := 7;
  bb#val := true;
  assert bi#val == 7;
  assert bb#val == true
};
#end

-- Independence twin: the two instantiations are distinct allocations, so a false claim
-- about one is caught even though the other's assertion holds.
#eval testLaurelExecution {}
#strata
program Laurel;
composite Box<T> { var val: T }

procedure twoInstantiationsFalse()
  opaque
{
  var bi: Box<int> := new Box<int>;
  var bb: Box<bool> := new Box<bool>;
  bi#val := 7;
  bb#val := true;
  assert bi#val == 7;
  assert bb#val == false
//^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Two type parameters, one field of each — pins that the per-instantiation substitution is
-- positional (a swapped substitution would type `first` as `bool`).
#eval testLaurelExecution {}
#strata
program Laurel;
composite Pair<A, B> { var first: A
 var second: B }

procedure twoTypeParams()
  opaque
{
  var p: Pair<int, bool> := new Pair<int, bool>;
  p#first := 3;
  p#second := false;
  assert p#first == 3;
  assert p#second == false
};
#end

-- A NON-generic composite alongside a generic one: the monomorphizer must leave the
-- ordinary composite completely untouched.
#eval testLaurelExecution {}
#strata
program Laurel;
composite Box<T> { var val: T }
composite Plain { var n: int }

procedure genericAndPlainCoexist()
  opaque
{
  var b: Box<int> := new Box<int>;
  var q: Plain := new Plain;
  b#val := 1;
  q#n := 2;
  assert b#val + q#n == 3
};
#end
