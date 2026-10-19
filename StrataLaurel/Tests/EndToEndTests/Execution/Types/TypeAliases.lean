/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Type aliases through the full pipeline

`type Name = Target` and its generic form `type Name<A, B> = Target` are surface sugar: the
alias is expanded, so a program that spells a type through an alias must behave exactly like
one that names the target directly. Two mechanisms have to agree on that expansion —
`TypeAliasElim`, which rewrites the program, and `TypeLattice.unfold`, which the consistency
relation consults when comparing an alias-spelled type against a directly-spelled one. If
they disagreed, a cross-spelling assignment (`var b: Foo<int> := new Box<int>`) would be
rejected even though elimination would have made it well typed.

Every case pairs a use through the alias with a claim about the value, and each shape gets a
false twin — an alias that expanded to something unconstrained would let the true claim pass
vacuously.

Every block but one marks an `entry`, so the expansion is checked by execution as well as by
the verifier: a concrete run observes the expanded program, so an expansion that produced the
wrong target shows up as a runtime failure rather than only as a proof obligation. The one
exception names its reason at the block.

NB: there is no `;` after an alias declaration — the following keyword delimits it.
-/

/-! ## A primitive alias, and a chain of them

`MyInt` really is `int`, so it takes an `int` literal and compares at `int`. The chain pins
that expansion is transitive rather than one level deep. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
type MyInt = int
type A = int
type B = A

procedure primitiveAlias()
  entry
  opaque
{
  var x: MyInt := 5;
  assert x == 5
};

procedure chainedAlias()
  entry
  opaque
{
  var y: B := 7;
  assert y == 7
};
#end

-- SOUNDNESS twin: the alias resolves to a real `int`, so a false claim about the value must
-- fail rather than pass on an unconstrained type.
#eval testLaurelExecution {} <|
#strata
program Laurel;
type MyInt = int

procedure primitiveAliasFalse()
  entry
  opaque
{
  var x: MyInt := 5;
  assert x == 6
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## An alias for a COMPOUND type

`TotalMap int bool` reached through an alias has to keep both of its type arguments, so
`mapConst`/`select` operate at the same key and value types as the direct spelling. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
type IM = TotalMap int bool

procedure mapAlias()
  entry
  opaque
{
  var m: IM := mapConst(false);
  assert select(m, 9) == false
};
#end

/-! ## An alias for a COMPOSITE

A field access through a composite alias needs `resolveFieldInTypeScope` to unfold the alias
before looking the field up — `p#x` is not a field of `P`, only of what `P` expands to. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Pt { var x: int }
type P = Pt

procedure compositeAliasField()
  entry
  opaque
  modifies *
{
  var p: P := new Pt;
  p#x := 3;
  assert p#x == 3
};
#end

-- SOUNDNESS twin: the alias reaches the real `Pt` field, not a fresh unconstrained one.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Pt { var x: int }
type P = Pt

procedure compositeAliasFieldFalse()
  entry
  opaque
  modifies *
{
  var p: P := new Pt;
  p#x := 3;
  assert p#x == 4
//^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## GENERIC aliases: the parameters substitute, in order

`type MyPair<A, B> = TotalMap A B` at `<int, bool>` must expand to `TotalMap int bool`.
`Swapped<A, B> = TotalMap B A` is the discriminating case: it pins that substitution is
positional rather than by-name-order, because at `<int, bool>` it expands to
`TotalMap bool int` — so the `select` below is keyed by a `bool` and yields an `int`. An
implementation that ignored the reordering would type the key as `int` and fail here. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
type MyPair<A, B> = TotalMap A B
type Swapped<A, B> = TotalMap B A

procedure genericAliasSubstitutes()
  entry
  opaque
{
  var m: MyPair<int, bool> := mapConst(false);
  assert select(m, 9) == false
};

procedure genericAliasPreservesOrder()
  entry
  opaque
{
  var s: Swapped<int, bool> := mapConst(5);
  assert select(s, true) == 5
};
#end

-- SOUNDNESS twin: the substituted map is a real `TotalMap int bool`, so a false read fails.
-- Verification-only, and the reason is a wording mismatch rather than anything about aliases:
-- the verifier reports this assert as "could not be proved", while BOTH interpreters render a
-- concretely-failed assert as "does not hold". The annotation can only match one of the two,
-- so an `entry` here would make the interpreter paths fail on an un-fired annotation.
-- (See the "wording must agree across both paths" note on `testLaurelExecution`.)
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
type MyPair<A, B> = TotalMap A B

procedure genericAliasSubstitutesFalse()
  opaque
{
  var m: MyPair<int, bool> := mapConst(false);
  assert select(m, 9) == true
//^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## A generic alias of a generic COMPOSITE, spelled both ways at once

`var b: Foo<int> := new Box<int>` names the type through the alias and the allocation
directly. This is the case where `TypeAliasElim` and `TypeLattice.unfold` have to agree: the
consistency check runs on the un-eliminated program, so it must unfold `Foo<int>` to
`Box<int>` itself rather than relying on the rewrite having happened. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
type Foo<T> = Box<T>

procedure genericAliasOfGenericComposite()
  entry
  opaque
  modifies *
{
  var b: Foo<int> := new Box<int>;
  b#val := 7;
  assert b#val == 7
};
#end

-- SOUNDNESS twin for the cross-spelling: the field is the monomorph's real field.
#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
type Foo<T> = Box<T>

procedure genericAliasOfGenericCompositeFalse()
  entry
  opaque
  modifies *
{
  var b: Foo<int> := new Box<int>;
  b#val := 7;
  assert b#val == 8
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A generic alias of a generic DATATYPE

A datatype constructor synthesizes the BARE datatype type — `Som(5)` has type `Bx`, with no
arguments — so `var o: Foo<int> := Som(5)` reaches the consistency relation as `Bx` against
`Foo<int>`. The alias has to be unfolded to `Bx<int>` and reduced to its base name `Bx`
before the comparison, or a correct program is rejected. -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
datatype Bx<T> { Som(v: T) }
type Foo<T> = Bx<T>

procedure genericAliasOfGenericDatatype()
  entry
  opaque
{
  var o: Foo<int> := Som(5);
  assert Bx..v(o) == 5
};
#end

/-! ## The alias is transparent at a PARAMETER, and through a chain of generic aliases

`take` declares `b: Foo<int>` and is called with a `Box<int>` — the same cross-spelling as
above, but now at an argument rather than an initializer, which is a different place for the
consistency relation to be consulted. The `ensures r == b#val` makes the accept observable:
without it the case would pass merely by resolving.

The chained case pins that a generic alias of a generic alias substitutes at each step,
carrying the argument through both parameter renames (`T` then `U`). -/

#eval testLaurelExecution {} <|
#strata
program Laurel;
composite Box<T> { var val: T }
type Foo<T> = Box<T>
type Chain<U> = Foo<U>
procedure take(b: Foo<int>) returns (r: int) opaque ensures r == b#val { r := b#val };

procedure aliasAtParameter()
  entry
  opaque
  modifies *
{
  var x: Box<int> := new Box<int>;
  x#val := 9;
  var g: int := take(x);
  assert g == 9
};

procedure chainedGenericAlias()
  entry
  opaque
  modifies *
{
  var b: Chain<int> := new Box<int>;
  b#val := 5;
  assert b#val == 5
};
#end
