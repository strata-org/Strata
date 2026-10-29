/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Field resolution for a `#field` access whose OWNER is not a plain variable.

`resolveFieldRef` resolves the field against `holderTy?` — the owner type
synthesized by `Synth.resolveStmtExpr` — and falls back to the string-based
`targetTypeName` only when that is absent or names no composite.
`targetTypeName` types exactly three owner shapes: `.Var (.Local _)`, a
`.Var (.Field _ _)` chain of `.UserDefined` field types, and `.AsType _ _`. So a
call site that omitted `holderTy?` silently supported only those three, and every
other owner — most importantly a datatype DESTRUCTOR application — failed with
`Resolution failed: 'f' is not defined`, naming the field rather than the owner.

Two call sites omitted it: `resolveModifiesEntry` (`modifies o#f`) and
`Synth.compoundAssign` (`o#f op= e`). Both now thread it, so every
`resolveFieldRef` call site in `Resolution.lean` does.

Threading it widens what resolves without rebinding a field that already
resolved:

  * for the three shapes `targetTypeName` already handled, both paths key the
    SAME per-type field map under the same composite name (aliases unfold on
    both sides — `TypeLattice.unfold` on one, `resolveFieldInTypeScope`'s
    `unfoldAlias` on the other), so the field id is unchanged; and
  * for an owner type carrying no name at all (`int`, `bool`, a bare `.TSet`)
    `highBaseName?` is `none`, so the `holderTy?` branch is skipped and the
    fallback runs exactly as before.

The "still resolves" sections below pin the first bullet. The second is pinned
by the non-composite owner case at the end and by `NonCompositeModifies.lean`'s
`fieldTargetOnValueOwner`, whose owner (`Box<int>`) is a NAMED non-composite —
the case where `highBaseName?` does return a name, and the widened lookup must
still find nothing and still report the owner diagnostic.

There is exactly one class of program whose meaning changes, and it is not
covered by either bullet: an owner shape `targetTypeName` cannot type, inside an
instance procedure whose composite declares the same field name. That used to
fall through to `resolveFieldRef`'s *instance type* fallback and bind the wrong
field. It has its own section below.
-/

meta import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `modifies` with a destructor-application owner

`modifies Ptr..target!(p)#x` frames one field of the composite reached through a
datatype destructor. The owner is a `.Call`, which `targetTypeName` cannot type,
so this resolves only via the synthesized owner type. Field granularity then
preserves the pointee's OTHER field across the call — the whole point of naming a
field rather than the object. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Obj {
  var x: int
  var y: int
}
datatype Ptr { Ref(target: Obj) }

procedure setThroughPtr(p: Ptr, v: int)
  opaque
  modifies Ptr..target!(p)#x
{
  Ptr..target!(p)#x := v
};

procedure ptrCaller()
  opaque
{
  var o: Obj := new Obj;
  var p: Ptr := Ref(o);
  var oldX: int := Ptr..target!(p)#x;
  var oldY: int := Ptr..target!(p)#y;
  setThroughPtr(p, 42);
  // The unframed field of the framed object is preserved.
  assert Ptr..target!(p)#y == oldY;
  // Negative control: the framed field may change, so this is NOT provable.
  // Without it the frame could be vacuously preserving everything.
  assert Ptr..target!(p)#x == oldX
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## The `instanceTypeName` fallback no longer shadows the owner

The one place threading `holderTy?` changes the meaning of a program that used to
resolve. `resolveFieldRef`'s third fallback is the ENCLOSING instance type (for
`self.field` on a gradually typed `self`). So inside an instance procedure of a
composite that happens to declare the same field name, an owner shape
`targetTypeName` could not type fell through to that fallback and bound the frame
to the *host's* field — here `modifies Ptr..target!(p)#x` framed `Host`'s `x`, not
the pointee's. The pair was `(Ptr..target!(p), Host#x)`: an object from one type
with a field id from another, which no write can match.

Now the synthesized owner type `Obj` is tried first and wins, so `writePointee`
(which writes exactly the field it frames) verifies, and `writeSelf` is correctly
rejected — the frame does not name `self#x`.

Reaching the old behaviour required all three of: an owner shape `targetTypeName`
cannot type, inside an instance procedure, on a composite declaring the same
field name. Absent the last two the program did not resolve at all, so the
affected population is programs that only resolved by accident, against the wrong
field. No existing test exercised it. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Obj {
  var x: int
  var y: int
}
datatype Ptr { Ref(target: Obj) }
composite Host {
  var x: int
  procedure writePointee(self: Host, p: Ptr)
    opaque
    modifies Ptr..target!(p)#x
  {
    Ptr..target!(p)#x := 1
  };
  procedure writeSelf(self: Host, p: Ptr)
//          ^^^^^^^^^ error: modifies clause does not hold
    opaque
    modifies Ptr..target!(p)#x
  {
    self#x := 1
  };
}
#end

/-! ## `modifies` owner shapes that already resolved

The three `targetTypeName` shapes must keep resolving to the same field. One
program each: chaining several opaque calls in a single caller runs into an
unrelated limitation in how the allocation fact carries across calls, which would
obscure the point being made here. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Inner {
  var a: int
  var b: int
}

// Plain-variable owner.
procedure viaLocal(i: Inner, v: int)
  opaque
  modifies i#a
{
  i#a := v
};

procedure localCaller()
  opaque
{
  var i: Inner := new Inner;
  var oldA: int := i#a;
  var oldB: int := i#b;
  viaLocal(i, 1);
  assert i#b == oldB;
  assert i#a == oldA
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Inner {
  var a: int
  var b: int
}
composite Outer {
  var inner: Inner
}

// Field-chain owner `o#inner`.
procedure viaChain(o: Outer, v: int)
  opaque
  modifies o#inner#a
{
  o#inner#a := v
};

procedure chainCaller()
  opaque
{
  var o: Outer := new Outer;
  o#inner := new Inner;
  var oldA: int := o#inner#a;
  var oldB: int := o#inner#b;
  viaChain(o, 2);
  assert o#inner#b == oldB;
  assert o#inner#a == oldA
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Inner {
  var a: int
  var b: int
}
composite Derived extends Inner {
  var c: int
}

// `as`-cast owner: the cast fixes the static type, and `a` is inherited.
procedure viaCast(d: Derived, v: int)
  opaque
  modifies (d as Inner)#a
{
  d#a := v
};

procedure castCaller()
  opaque
{
  var d: Derived := new Derived;
  var oldB: int := d#b;
  viaCast(d, 3);
  assert d#b == oldB
};
#end

/-! ## Compound assignment through a non-trivial holder

`o#f op= e` resolved `f` against `targetTypeName` only, while its twin rule
`o#f++` (`Synth.incrDecr`) already used the synthesized holder type. The two
therefore disagreed on the SAME expression: `Ptr..target!(p)#x++` resolved and
`Ptr..target!(p)#x += 1` did not. Both forms appear below on each holder shape,
so the pair stays in lockstep.

`w#c#v#x` is the generic-chain case: `Cell<T>`'s field `v` is declared `.TVar T`,
which carries no composite name, so `targetTypeName` drops to `none` there and
only `concretizeFieldType`'s concrete `Obj` recovers `#x`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Obj {
  var x: int
  var y: int
}
datatype Ptr { Ref(target: Obj) }
composite Cell<T> {
  var v: T
}
composite Wrap {
  var c: Cell<Obj>
}

// Destructor-application holder.
procedure bumpThroughPtr(p: Ptr)
  opaque
  modifies Ptr..target!(p)#x
{
  Ptr..target!(p)#x += 1
};

procedure incrThroughPtr(p: Ptr)
  opaque
  modifies Ptr..target!(p)#x
{
  Ptr..target!(p)#x++
};

// Generic-field-chain holder: `w#c#v` synthesizes to the concrete `Obj`.
procedure bumpThroughGenericChain(w: Wrap)
  opaque
  modifies w#c#v#x
{
  w#c#v#x += 1
};

procedure incrThroughGenericChain(w: Wrap)
  opaque
  modifies w#c#v#x
{
  w#c#v#x++
};
#end

/-! ## Non-composite owner behind the same non-trivial shapes

This is the case most at risk from threading `holderTy?`, because
`resolveModifiesEntry` resolves the field BEFORE the heap-relevance gate runs.
An owner reached through a destructor whose type is `int` must still reach the
gate and report "non-composite owner type", exactly as a plain `int` variable
owner does — not resolve `#x` against some unrelated scope and slip through.

Resolution-only, because a modifies entry the gate KEEPS while its field stayed
unresolved goes on to trip a `strata-bug` in a later pass. That is pre-existing
and shape-independent (a plain `modifies o#nosuch` on a composite `o` does it
too), so it is not pinned here. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Obj {
  var x: int
}
datatype Val { Wrap(n: int) }

// `Val..n!(v) : int` — named field, non-composite owner.
procedure nonCompositeOwnerViaDestructor(v: Val, o: Obj)
  opaque
  modifies Val..n!(v)#x
//                    ^ error: Resolution failed: 'x' is not defined
//                    ^ error: modifies clause field target has non-composite owner type 'int'; only a heap object can be framed
  modifies o
{
  o#x := 1
};
#end

/-! The positive shapes, resolution-only: no diagnostics at all. Separate from the
verification programs above so a future verifier change cannot mask a resolution
regression here. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Obj {
  var x: int
  var y: int
}
datatype Ptr { Ref(target: Obj) }
composite Cell<T> {
  var v: T
}
composite Wrap {
  var c: Cell<Obj>
}

procedure allShapesResolve(p: Ptr, w: Wrap, o: Obj)
  opaque
  modifies Ptr..target!(p)#x
  modifies w#c#v#y
  modifies o#x
  modifies (o as Obj)#y
{
  Ptr..target!(p)#x := 1;
  w#c#v#y += 1;
  o#x += 1
};
#end
