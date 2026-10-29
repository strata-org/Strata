/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Type arguments are compared, not erased

The consistency relation recurses into type arguments so that a generic slot can be filled —
`TotalMap K V` accepts a `TotalMap int bool`, a `Box<T>` field accepts whatever `T` became at
the instantiation. The risk in a relation that recurses is that it keeps recursing past the
point where both sides are concrete, treating `int` and `bool` as "both leaves, close enough".
That would make every generic spelling a hole.

So each case here is a pair of CONCRETE types that share a base name and arity and differ
only in an argument, in a position where the relation had to recurse to get there:

* a `TotalMap` parameter, reached through the `.TMap` arm;
* an explicit `new C<τ…>` at the wrong arity, where a surplus argument would otherwise be
  dropped by the monomorphizer's `zip`;
* two instantiations of one generic DATATYPE, which are distinct Core sorts;
* a constructor of a DIFFERENT datatype assigned through an alias, where the alias unfold
  must not widen the base-name comparison.

The accepting twins are in `Execution/` with their features; nothing here is expected to
translate.
-/

/-! ## A `TotalMap` parameter stays strict on its concrete arguments

`needsIB` wants `TotalMap int bool`. The `.TMap` arm of the relation recurses into the key
and value, which is what lets a generic `TotalMap K V` parameter accept a concrete map — but
here both sides are concrete, so the recursion has to compare rather than wildcard. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure needsIB(m: TotalMap int bool) opaque { assert 1 == 1 };

procedure concreteMapMismatch()
  opaque
{
  var mm: TotalMap int int;
  needsIB(mm);
//        ^^ error: expected 'TotalMap int bool', got 'TotalMap int int'
  assert 1 == 1
};
#end

/-! ## An explicit `new C<τ…>` must supply the declared number of arguments

`Box<T>` takes one. Two are reported at both the declared type and the allocation, because
each is an independent application of the name — a check that ran only on the declaration
would let the allocation through, and the monomorphizer's `zip` would silently drop the
surplus argument rather than fail. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }

procedure newWrongArity()
  opaque
  modifies *
{
  var b: Box<int, bool> := new Box<int, bool>;
//       ^^^^^^^^^^^^^^ error: 'Box' expects 1 type argument(s) but 2 were provided
//                         ^^^^^^^^^^^^^^^^^^ error: 'Box' expects 1 type argument(s) but 2 were provided
  b#val := 7;
  assert b#val == 7
};
#end

/-! ## Two instantiations of a generic datatype are distinct sorts

Generic datatypes are NOT monomorphized — they lower to one native parametric Core sort —
which makes it tempting to treat `Bx<int>` and `Bx<bool>` as the same Laurel type. They are
not: the type arguments are forwarded to Core, which would reject the confusion there. Doing
it at resolution keeps the error in the user's vocabulary. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Bx<T> { MkBx(v: T) }

procedure crossInstantiationAssignment()
  opaque
{
  var bi: Bx<int> := MkBx(5);
  var bb: Bx<bool> := bi;
//                    ^^ error: expected 'Bx<bool>', got 'Bx<int>'
  assert 1 == 1
};
#end

/-! ## Unfolding an alias does not widen the base-name comparison

A datatype constructor synthesizes the BARE datatype type, so `MkOther(5)` has type `Other`,
with no arguments. Assigning it into a `Foo<int>` variable reaches the arm that unfolds the
alias to `Bx<int>` and compares base names — and `Other` is not `Bx`. The accepting twin,
where the constructor IS one of `Bx`'s, is in `Execution/Types/TypeAliases.lean`; without
this case that twin would also pass on an unfold that accepted any datatype. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Bx<T> { Som(v: T) }
datatype Other<T> { MkOther(v: T) }
type Foo<T> = Bx<T>

procedure aliasUnfoldDoesNotWiden()
  opaque
{
  var o: Foo<int> := MkOther(5);
//                   ^^^^^^^^^^ error: expected 'Foo<int>', got 'Other<int>'
  assert 1 == 1
};
#end
