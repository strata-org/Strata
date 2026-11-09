/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # What `is` and `as` accept as a target

Both lower by keying off a runtime type tag, and only composites carry one. So the target
has to be a composite, and one the tested value may be — for a generic composite, the
*right* instantiation.
Two separate rules, enforced at resolution, each pinned here with the diagnostic it emits.

Getting either wrong is not a cosmetic problem. A datatype target reaches lowering and dies
as a dangling `downcast$T` internal error; a primitive `is` lowers to a `.Hole`, which the
verifier then discharges silently — so the program would appear to verify while testing
nothing. Rejecting at resolution is what keeps both out of the pipeline.

The positive cases (`is`/`as` against a composite, including a generic instantiation and a
nested one) live with the feature, in `Execution/Types/Composites/GenericComposite.lean`.
-/

/-! ## Rule 1: the target must be a COMPOSITE

Four non-composite targets, one per kind the check has to recognise: a datatype, a
primitive, a constrained type (whose unfolding reaches a primitive base), and a bare type
parameter. The last is the `.TVar` arm — a `T` inside a generic procedure is not a composite
even though it may be instantiated at one. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Wrapper { MkW(v: int) }

procedure asDatatypeTarget()
  opaque
{
  var w: Wrapper := MkW(3);
  var w2: Wrapper := w as Wrapper
//                        ^^^^^^^ error: 'as' is only supported for composite (class) types; 'Wrapper' is not a composite type
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure isPrimitiveTarget()
  opaque
{
  var b: bool := 5 is int;
//                    ^^^ error: 'is' is only supported for composite (class) types; 'int' is not a composite type
  assert b
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0

procedure asConstrainedTarget()
  opaque
{
  var n: nat := 5 as nat;
//                   ^^^ error: 'as' is only supported for composite (class) types; 'nat' is not a composite type
  assert n == 5
};
#end

-- A bare type parameter, for both operators. `T` may be instantiated at a composite, but
-- the test would have to be lowered against a tag that is not known until instantiation.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure asTVarTarget<T>(x: T) returns (r: T)
  opaque
  ensures true
{
  r := x as T
//          ^ error: 'as' is only supported for composite (class) types; 'T' resolves to a type parameter, which has no declared bound and so may be instantiated at a non-composite type
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure isTVarTarget<T>(x: T) returns (r: bool)
  opaque
  ensures true
{
  r := x is T
//          ^ error: 'is' is only supported for composite (class) types; 'T' resolves to a type parameter, which has no declared bound and so may be instantiated at a non-composite type
};
#end

/-! ## Rule 2: the target must be RELATED to the value's type

`Box<int>` and `Box<bool>` are distinct monomorphs with distinct tags, so neither is a
subtype of the other and the test can never hold. Accepting it would produce a test that is
statically false, which is far more useful to reject than to lower. The nested case pins that
the relation is checked through the type ARGUMENTS too, not just the base name — the
diagnostic names both full instantiations. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure isWrongInstantiation()
  opaque
  modifies *
{
  var b: Box<int> := new Box<int>;
  assert b is Box<bool>
//       ^ error: cannot test unrelated type 'Box<int>' against 'Box<bool>'
};
#end

-- The inner arguments are swapped, so the two nested instantiations are unrelated even
-- though the outer base name and arity match.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Pair<A, B> { var a: A
 var b: B }

procedure isWrongNestedInstantiation()
  opaque
  modifies *
{
  var b: Box<Pair<int, bool>> := new Box<Pair<int, bool>>;
  assert b is Box<Pair<bool, int>>
//       ^ error: cannot test unrelated type 'Box<Pair<int, bool>>' against 'Box<Pair<bool, int>>'
};
#end

/-! Under multiple inheritance, a type is also related to one that some non-generic composite
extends together with it (`crossCast` in `Execution/Types/Composites/Inheritance.lean`). A
sibling that none extends together with it is not, and neither is one that only a generic
composite, or a composite extending another instantiation, does. Nor is an instantiation at
a type variable, which some instantiation of the variable leaves unrelated. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal {}
composite Dog extends Animal {}
composite Cat extends Animal {}

procedure siblingCast()
  opaque
{
  var d: Dog := new Dog;
  var c: Cat := d as Cat
//              ^ error: cannot cast unrelated type 'Dog' to 'Cat'
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
composite A {}
composite B {}
composite D<T> extends A, B { var v: T }
composite Box<T> { var val: T }
composite DBox<T> extends Box<T>, B {}
composite IntBoxB extends Box<int>, B {}

procedure onlyGenericDescendant()
  opaque
{
  var a: A := new A;
  assert !(a is B)
//         ^ error: cannot test unrelated type 'A' against 'B'
};

// In a `catch` guard too, where `c` may be a `DBox<bool>`, so the test must not be folded to `false`.
procedure genericDescendantInGuard()
  opaque
{
  var b: Box<bool> := new Box<bool>;
  try {
    throw b
  } catch c when c is B {
//               ^ error: cannot test unrelated type 'Box<bool>' against 'B'
    assert true
  }
};

procedure otherInstantiationDescendant()
  opaque
{
  var x: Box<bool> := new Box<bool>;
  assert !(x is B)
//         ^ error: cannot test unrelated type 'Box<bool>' against 'B'
};

// `x` is a `Box<bool>` when `T` is `bool`, and no non-generic composite extends that and `B`.
procedure typeVariableInstantiationDescendant<T>(x: Box<T>) returns (r: bool)
  opaque
{
  r := x is B
//     ^ error: cannot test unrelated type 'Box<T>' against 'B'
};
#end
