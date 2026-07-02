/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Regression tests for dynamic-reference field access. A datatype marked via
`withDynamicRef` resolves fields cross-scope (a concrete target cannot), and
reads/writes through it verify end-to-end via the readFieldDyn/updateFieldDyn
wrappers. With ref-only heap keying, dynamic-reference values sharing a
reference alias the same field.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-- Mark `Dyn` as the dynamic-reference type for these tests. -/
private def markDyn : Laurel.Program → Laurel.Program :=
  withDynamicRef "Dyn" "Dyn..as_ref!" "from_ref"

/-! ## `meow` (on `Cat`) is not a field of `Dog`, so `d#meow` is rejected -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure test() opaque {
  var d: Dog := new Dog;
  var x: int := d#meow
//                ^^^^ error: Resolution failed: 'meow' is not defined
};
#end

/-! ## Correct field access on the same composites still resolves -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure test() opaque {
  var d: Dog := new Dog;
  var x: int := d#bark
};
#end

/-! ## A dynamic-reference target resolves a field cross-scope (gate TRUE branch) -/

#eval testLaurelResolution (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure test() opaque {
  var a: Dyn := from_ref(0);
  var x: int := a#bark
};
#end

/-! ## A dynamic-reference target accessing a field defined on no composite still errors -/

#eval testLaurelResolution (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure test() opaque {
  var a: Dyn := from_ref(0);
  var x: int := a#nope
//                ^^^^ error: Resolution failed: 'nope' is not defined
};
#end

/-! ## A field name shared by several composites is ambiguous on a dynamic-reference
    target: the runtime type is unknown, so no single owner can be chosen. Rejected
    rather than silently binding the sorted-first owner's (foreign) heap slot. -/

#eval testLaurelResolution (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var value: int }
composite Cat { var value: int }
procedure test() opaque {
  var a: Dyn := from_ref(0);
  var x: int := a#value
//                ^^^^^ error: is ambiguous
};
#end

/-! ## The same shared field name on a CONCRETE target still resolves (only the
    dynamic-reference path is ambiguous; a typed target knows its owner). -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Dog { var value: int }
composite Cat { var value: int }
procedure test() opaque {
  var d: Dog := new Dog;
  var x: int := d#value
};
#end

/-! ## Without the marker, a plain datatype target does NOT resolve cross-scope -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure test() opaque {
  var a: Dyn := from_ref(0);
  var x: int := a#bark
//                ^^^^ error: Resolution failed: 'bark' is not defined
};
#end

/-! ## A field write/read round-trip verifies -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d: Dog := new Dog;
  d#bark := 7;
  assert d#bark == 7;
  d#bark := d#bark + 1;
  assert d#bark == 8
};
#end

/-! ## Two instances have independent fields (no aliasing collapse) -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d1: Dog := new Dog;
  var d2: Dog := new Dog;
  d1#bark := 1;
  d2#bark := 2;
  assert d1#bark == 1;
  assert d2#bark == 2
};
#end

/-! ## A false field assertion is caught by the verifier -/

#eval testLaurel <|
#strata
program Laurel;
composite Dog { var bark: int }
procedure test() opaque {
  var d: Dog := new Dog;
  d#bark := 1;
  assert d#bark == 2
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## A write then read through a dynamic-reference target round-trips.
    Exercises the `updateFieldDyn`/`readFieldDyn` wrappers end-to-end. The
    written object is exempt from the frame because it is freshly allocated and
    aliased into the dynamic-reference value. -/

#eval testLaurel (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure write_read(a: Dyn) opaque modifies * {
  a#bark := 7;
  assert a#bark == 7
};
#end

/-! ## A false assertion through a dynamic-reference target is caught (non-vacuity) -/

#eval testLaurel (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure write_read(a: Dyn) opaque modifies * {
  a#bark := 7;
  assert a#bark == 8
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## Two dynamic-reference targets sharing a reference alias the same field.
    With ref-only heap keying, a write through one is seen through the other. -/

#eval testLaurel (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
procedure alias(a: Dyn, b: Dyn)
  requires Dyn..as_ref!(a) == Dyn..as_ref!(b)
  opaque modifies * {
  a#bark := 5;
  assert b#bark == 5
};
#end

/-! ## Cross-scope resolution picks a field defined on a distinct composite.
    With two composites, a dynamic-reference target resolves `meow` (on `Cat`)
    even though it also sees `Dog`. -/

#eval testLaurelResolution (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure test() opaque {
  var a: Dyn := from_ref(0);
  var x: int := a#meow
};
#end

/-! ## A field write/read through a dynamic-reference target verifies even when
    multiple composites are present (owner tag chosen deterministically). -/

#eval testLaurel (postParse := markDyn) <|
#strata
program Laurel;
datatype Dyn { from_ref(as_ref: int) }
composite Dog { var bark: int }
composite Cat { var meow: int }
procedure write_read(a: Dyn) opaque modifies * {
  a#meow := 4;
  assert a#meow == 4
};
#end

/-! ## Multi-constructor dynamic-reference type.
    A real front-end catch-all (e.g. Python `Any`) has many constructors, so the
    unbox accessor is partial. `MarkedAny` below has a non-reference constructor
    alongside the reference one; the following cases pin that the bridge stays
    sound when the accessor is applied to such a value: an unboxed reference is
    an unconstrained-but-consistent int, so a value round-trips with itself and a
    false assertion is still caught, while two distinct values are not assumed to
    alias. -/

/-- Mark a multi-constructor `MarkedAny` as the dynamic-reference type. -/
private def markAny : Laurel.Program → Laurel.Program :=
  withDynamicRef "MarkedAny" "MarkedAny..as_ref!" "from_ref"

/-! ### A write then read through one multi-constructor dyn value round-trips. -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure roundtrip(a: MarkedAny) opaque modifies * {
  a#bark := 7;
  assert a#bark == 7
};
#end

/-! ### A false assertion through a multi-constructor dyn value is caught. -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure caught(a: MarkedAny) opaque modifies * {
  a#bark := 7;
  assert a#bark == 8
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ### Two distinct multi-constructor dyn values are not assumed to alias:
    a write through one is not provably seen through the other. -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure noalias(a: MarkedAny, b: MarkedAny) opaque modifies * {
  a#bark := 5;
  assert b#bark == 5
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ### Two dyn values with equal references do alias (ref-only identity). -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure alias(a: MarkedAny, b: MarkedAny)
  requires MarkedAny..as_ref!(a) == MarkedAny..as_ref!(b)
  opaque modifies * {
  a#bark := 5;
  assert b#bark == 5
};
#end

/-! ### Composite→dyn boxing round-trips: a composite assigned into a dyn-typed
    slot is boxed via `from_ref(Composite..ref!(..))`, so a field written on the
    composite is read back through the dyn value (they share a reference). -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure box_roundtrip() opaque modifies * {
  var d: Dog := new Dog;
  d#bark := 9;
  var a: MarkedAny := d;
  assert a#bark == 9
};
#end

/-! ### A false assertion through a boxed composite is still caught. -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure box_caught() opaque modifies * {
  var d: Dog := new Dog;
  d#bark := 9;
  var a: MarkedAny := d;
  assert a#bark == 10
//^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ### A composite passed as a call argument to a dyn-typed parameter is boxed
    (`boxCallArgs` path), so the callee reads the caller's field through it. -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
function read_bark(a: MarkedAny): int { a#bark };
procedure box_callarg() opaque modifies * {
  var d: Dog := new Dog;
  d#bark := 9;
  assert read_bark(d) == 9
};
#end

/-! ### Boxing preserves heap identity: mutate the composite after boxing, and
    the new value is seen through the boxed dyn value (shared reference). -/

#eval testLaurel (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
composite Dog { var bark: int }
procedure box_alias() opaque modifies * {
  var d: Dog := new Dog;
  var a: MarkedAny := d;
  d#bark := 5;
  assert a#bark == 5
};
#end

/-! ### A datatype (non-composite) value is NOT accepted into a dyn slot: it has
    no heap reference to box, so it stays a type error rather than leaking. -/

#eval testLaurelResolution (postParse := markAny) <|
#strata
program Laurel;
datatype MarkedAny { from_ref(as_ref: int), from_int(v: int) }
datatype Other { mk(n: int) }
composite Dog { var bark: int }
procedure box_datatype_rejected() opaque {
  var o: Other := mk(3);
  var a: MarkedAny := o
//                    ^ error: expected 'MarkedAny'
};
#end

