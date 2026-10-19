/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

-- No interpreters: the annotated failure is "could not be proved", which a concrete run cannot produce.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Base {
  var xValue: int
}

composite Base2 {
  var yValue: int
}

composite Extender extends Base, Base2 {
  var zValue: int
}

procedure inheritedFields(a: Extender)
  opaque
  modifies a
{
  a#xValue := 1;
  a#yValue := 2;
  a#zValue := 3;

  assert a#xValue == 1;
  assert a#yValue == 2;
  assert a#zValue == 3
};

procedure typeCheckingAndCasting()
  opaque
{
  var a: Base := new Base;
  assert a is Base;
  assert !(a is Extender);
  var b: Extender := new Extender;
  assert b is Base;
  assert b is Base2;
  assert b is Extender;

  var c: Base := b;
  var d: Extender := c as Extender;
  var e: Extender := a as Extender
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition could not be proved
};

composite Top {
  var tValue: int
}

composite Left extends Top {
  var lValue: int
}
composite Right extends Top {
  var rValue: int
}
composite Bottom extends Left, Right {
  var bValue: int
}

procedure diamondInheritance()
  opaque
{
  var b: Bottom := new Bottom;
  b#lValue := 1;
  b#rValue := 2;
  b#bValue := 3;
  // tValue can not be used

  assert b#lValue == 1;
  assert b#rValue == 2;
  assert b#bValue == 3;

  assert b is Left;
  assert b is Right;
  assert b is Top;
  assert b is Bottom
};

// Currently does not pass. Implementation needs b type invariant mechanism that we have yet to add.
//procedure typedParameter(b: Bottom) opaque {
//  var b: Bottom := b;
//  assert b is Left;
//  assert b is Right;
//  assert b is Top;
//  assert b is Bottom;
//}
#end

-- A front-end-defined hierarchy with two tiers under one root, which is the shape a
-- front end needs for its exception classes: the root carries shared fields, a user
-- type inherits them from two levels up, and a sibling tier is provably outside the
-- catchable one. Only `extends` and `is` are exercised — no `throw`/`try` — so this
-- belongs with inheritance rather than with the exception tests, which rely on it.
-- No Core interpreter: it fails with "assert condition did not reduce to bool" on this program.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;

// Front-end-defined root and its two tiers: a catchable tier and a "fatal" tier
// as separate children of the root.
composite Exception {
  var message: string
}
composite AppException extends Exception {}
composite FatalError extends Exception {}

// A user-defined exception under the catchable tier.
composite MyError extends AppException {
  var code: int
}

procedure rootIsUsable()
  opaque
{
  // The front-end root carries `message` and is usable directly.
  var b: Exception := new Exception;
  b#message := "root";
  assert b#message == "root";
  assert b is Exception
};

procedure userExceptionIsRooted()
  opaque
{
  var e: MyError := new MyError;
  // `message` is inherited from `Exception` two levels up the chain.
  e#message := "boom";
  e#code := 42;
  assert e#message == "boom";
  assert e#code == 42;
  // A user exception is a subtype of its parent tier and of the root.
  assert e is MyError;
  assert e is AppException;
  assert e is Exception
};

procedure fatalTierEscapesCatchAll()
  opaque
{
  // A fatal-tier value, bound at the root `Exception` (as a catch-all
  // binding would be), is provably not in the catchable tier — so a catch-all
  // predicated on `AppException` would not catch it. The escape falls out of
  // the subtype check, needing nothing beyond how the front-end wires `extends`.
  var f: Exception := new FatalError;
  assert f is Exception;
  assert !(f is AppException)
};

procedure runAll() entry
  opaque
  modifies *
{
  rootIsUsable();
  userExceptionIsRooted();
  fatalTierEscapesCatchAll()
};
#end

/-! ## Inheritance where the child, the parent, or both are GENERIC

Monomorphization has to emit the parent's clone BEFORE the child's, because re-resolution
builds the child's inherited-field scope by looking the parent up. Three shapes, by how the
parent's type arguments relate to the child's:

* a CONCRETE parent (`Box<T> extends Base`) — nothing to substitute;
* a generic parent at the child's own argument (`Box<T> extends Base<T>`) — the ordinary
  Java shape, where `Box<int>` needs `Base$int` to exist;
* a REMAP (`P2<A, B> extends Pair<B, A>`) and a CONCRETIZATION
  (`Box<T> extends Base<int>`) — where the parent's arguments are not the child's.

The remap and concretization cases are the ones that catch an unsound upcast: subtyping is
checked through `substitutedAncestors`, so it has to apply the `extends` remap. A check that
compared arguments positionally without substituting would accept the WRONG supertype. Each
case reads a value back THROUGH the parent-typed variable, so the remap has to preserve
values and not merely type-check; the false twins pin that those reads are real.

Every block from here on marks an `entry`, so the substituted ancestor is also EXERCISED: the
read back through the parent-typed variable really happens, and the false twins' assertion
failures are reproduced at runtime as well as proved. The one exception declares an enumerated
`modifies` frame, which the Core interpreter cannot discharge; it says so at the block. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseC { var tag: int }
composite BoxC<T> extends BaseC { var val: T }

procedure genericChildConcreteParent()
  entry
  opaque
  modifies *
{
  var b: BoxC<int> := new BoxC<int>;
  b#tag := 1;
  b#val := 7;
  assert b#tag == 1 && b#val == 7
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseC { var tag: int }
composite BoxC<T> extends BaseC { var val: T }

procedure genericChildConcreteParentFalse()
  entry
  opaque
  modifies *
{
  var b: BoxC<int> := new BoxC<int>;
  b#tag := 1;
  assert b#tag == 2
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Generic parent at the child's own type argument: `BoxG<int>` needs `BaseG$int` emitted
-- first, and the inherited `tag: T` has to become `int` at the clone.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseG<T> { var tag: T }
composite BoxG<T> extends BaseG<T> { var val: T }

procedure genericChildGenericParent()
  entry
  opaque
  modifies *
{
  var b: BoxG<int> := new BoxG<int>;
  b#tag := 1;
  b#val := 7;
  assert b#tag == 1 && b#val == 7
};

// Two instantiations get two distinct parent clones (`BaseG$int`, `BaseG$bool`), so the
// inherited field is typed per instantiation rather than shared.
procedure genericChildGenericParentTwoInstantiations()
  entry
  opaque
  modifies *
{
  var bi: BoxG<int> := new BoxG<int>;
  bi#tag := 9;
  var bb: BoxG<bool> := new BoxG<bool>;
  bb#tag := true;
  assert bi#tag == 9 && bb#tag == true
};

// Same-instantiation upcast: reading the inherited field through the parent-typed variable.
procedure upcastSameInstantiation()
  entry
  opaque
  modifies *
{
  var b: BoxG<int> := new BoxG<int>;
  b#tag := 5;
  var p: BaseG<int> := b;
  assert p#tag == 5
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseG<T> { var tag: T }
composite BoxG<T> extends BaseG<T> { var val: T }

procedure genericChildGenericParentFalse()
  entry
  opaque
  modifies *
{
  var b: BoxG<int> := new BoxG<int>;
  b#tag := 1;
  assert b#tag == 2
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseG<T> { var tag: T }
composite BoxG<T> extends BaseG<T> { var val: T }

procedure upcastSameInstantiationFalse()
  entry
  opaque
  modifies *
{
  var b: BoxG<int> := new BoxG<int>;
  b#tag := 1;
  var base: BaseG<int> := b;
  assert base#tag == 2
//^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### The REMAP: `P2<A, B> extends Pair<B, A>`

`P2<int, bool>`'s parent is `Pair<bool, int>` — so the inherited `fst` is a `bool` and `snd`
an `int`, the opposite of what a positional comparison would give. Both are read back
through the parent-typed variable, which is what makes the substitution observable rather
than merely accepted. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite PairR<A, B> { var fst: A
 var snd: B }
composite P2<A, B> extends PairR<B, A> { var extra: int }

procedure upcastThroughRemap()
  entry
  opaque
  modifies *
{
  var x: P2<int, bool> := new P2<int, bool>;
  x#fst := true;
  x#snd := 9;
  var p: PairR<bool, int> := x;
  assert p#fst == true && p#snd == 9
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite PairR<A, B> { var fst: A
 var snd: B }
composite P2<A, B> extends PairR<B, A> { var extra: int }

procedure upcastThroughRemapFalse()
  entry
  opaque
  modifies *
{
  var x: P2<int, bool> := new P2<int, bool>;
  x#snd := 9;
  var p: PairR<bool, int> := x;
  assert p#snd == 8
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### The CONCRETIZATION: `BoxK<T> extends BaseK<int>`

The parent's argument does not depend on the child's at all, so `BoxK<bool>`'s parent is
`BaseK<int>` — the inherited field is an `int` regardless of how the child is instantiated. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseK<S> { var b: S }
composite BoxK<T> extends BaseK<int> { var v: T }

procedure upcastThroughConcretization()
  entry
  opaque
  modifies *
{
  var x: BoxK<bool> := new BoxK<bool>;
  x#b := 7;
  var p: BaseK<int> := x;
  assert p#b == 7
};
#end

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BaseK<S> { var b: S }
composite BoxK<T> extends BaseK<int> { var v: T }

procedure upcastThroughConcretizationFalse()
  entry
  opaque
  modifies *
{
  var x: BoxK<bool> := new BoxK<bool>;
  x#b := 7;
  var p: BaseK<int> := x;
  assert p#b == 6
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

-- Writing to an inherited field whose type came through the remap. `GHolder<int, bool>`
-- extends `Base<bool, int>`, so the inherited `h: U` is a `bool` — the child's SECOND
-- argument, not its first. A write of `false` is therefore the correct one, and accepting it
-- is what shows the remap is applied to field TYPES and not only to the ancestor list.
-- No Core interpreter: `remappedInheritedFieldWrite` declares an ENUMERATED frame
-- (`modifies g`), and the frame check that lowers to does not reduce concretely — the Core
-- interpreter stops with "assert ... condition did not reduce to bool". The standalone
-- Laurel interpreter runs it, so the write below is still executed.
#eval testLaurelExecution { skipCoreInterpreter := true } <|
#strata
program Laurel;
composite BaseH<U, V> { var h: U }
composite GHolder<A, B> extends BaseH<B, A> { var k: int }

procedure remappedInheritedFieldWrite(g: GHolder<int, bool>)
  opaque
  modifies g
{
  g#h := false
};

// The write above takes a `GHolder<int, bool>` argument, so it needs a driver to be reached
// from an entry point. Allocating and passing one is enough: the remapped field write then
// really executes rather than only being verified.
procedure driveRemappedInheritedFieldWrite()
  entry
  opaque
  modifies *
{
  var g: GHolder<int, bool> := new GHolder<int, bool>;
  remappedInheritedFieldWrite(g)
};
#end

/-! ## A CONCRETE composite extending a generic INSTANTIATION

`IntBox extends BoxI<int>` inverts the earlier shapes: the child is not generic, but its
parent is a monomorph, so the emission order has to put a GENERATED composite before a
user-written one. The transitive case puts the monomorph two levels up
(`Super extends IntBox extends BoxI<int>`), which needs the topological sort to run over the
whole list rather than pairwise.

Each case reads the inherited field back, once on the child directly and once through the
upcast, so an ordering bug shows up as a missing field rather than only as a re-resolution
failure. The wrong-target rejections are in `Resolution/Types/Composites/Inheritance.lean`. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxI<T> { var val: T }
composite IntBox extends BoxI<int> { var w: int }
composite Super extends IntBox { var z: int }

// No upcast here, which is what isolates the EMISSION ORDER from the subtyping check: the
// field is only in scope on `IntBox` if the monomorph parent was emitted before it, so a
// wrong order fails at re-resolution rather than at the assertion.
procedure concreteChildInheritedFieldDirect()
  entry
  opaque
  modifies *
{
  var ib: IntBox := new IntBox;
  ib#val := 5;
  assert ib#val == 5
};

// Upcast to the monomorph parent and read through it.
procedure concreteChildUpcastToMonomorph()
  entry
  opaque
  modifies *
{
  var ib: IntBox := new IntBox;
  ib#val := 5;
  var b: BoxI<int> := ib;
  var got: int := b#val;
  assert got == 5
};

// Three levels, with the monomorph at the top of the chain.
procedure concreteChildUpcastTransitive()
  entry
  opaque
  modifies *
{
  var s: Super := new Super;
  s#val := 9;
  var b: BoxI<int> := s;
  assert b#val == 9
};
#end

-- SOUNDNESS twin: the value read through the upcast is the one written, so a false claim must
-- fail rather than passing on an inherited field left unconstrained by the clone.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite BoxI<T> { var val: T }
composite IntBox extends BoxI<int> { var w: int }

procedure concreteChildUpcastFalse()
  entry
  opaque
  modifies *
{
  var ib: IntBox := new IntBox;
  ib#val := 5;
  var b: BoxI<int> := ib;
  var got: int := b#val;
  assert got == 6
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end
