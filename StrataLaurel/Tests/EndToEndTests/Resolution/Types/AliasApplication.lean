/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Applying a generic type alias

A generic alias is expanded by substituting its parameters into its target, which puts three
obligations on resolution. It has to check the ARITY before expanding — otherwise
`TypeAliasElim` substitutes a short list and leaves a dangling reference to a parameter that
was never bound. It has to TERMINATE on a cycle rather than unfolding forever. And after
expanding it must stay STRICT: unfolding `Foo<int>` to `Box<int>` must not also make
`Box<bool>` acceptable, or the alias would be a hole in the type system rather than a
spelling of it.

The positive side — expansion, transitivity, parameter order, cross-spelling assignment —
lives with the feature in `Execution/Types/TypeAliases.lean`.
-/

/-! ## Arity is checked before expansion

`MyPair<int>` supplies one argument to a two-parameter alias. The arity error comes first; the
two that follow are what the un-substituted target looks like downstream, both naming the `K`
that was left unbound — once as the mismatch against the annotation (`TotalMap K bool`), and
once as the inference failure on the `mapConst` call that had to supply it. All three are
pinned so none can silently change into something else. -/

#eval testLaurelResolution <|
#strata
program Laurel;
type MyPair<A, B> = TotalMap A B

procedure aliasWrongArity()
  opaque
{
  var m: MyPair<int> := mapConst(false);
//       ^^^^^^^^^^^ error: 'MyPair' expects 2 type argument(s) but 1 were provided
//                      ^^^^^^^^^^^^^^^ error: expected 'MyPair<int>', got 'TotalMap K bool'
//                      ^^^^^^^^^^^^^^^ error: cannot infer type argument 'K' of 'mapConst': the expected type does not determine it either; annotate with a concrete instantiation
  assert true
};
#end

/-! ## A cycle terminates instead of unfolding forever

`A<T> = B<T>` and `B<U> = A<U>` have no normal form. The fuel/visited guards in
`resolveAliasType`, `TypeLattice.unfold` and `resolveFieldInTypeScope.unfoldAlias` make the
unfold stop; what is left is a type that never became concrete, so the `0` initializer does
not match it. The test COMPLETING is the real assertion here — a missing guard hangs the
build rather than failing it. -/

#eval testLaurelResolution <|
#strata
program Laurel;
type A<T> = B<T>
type B<U> = A<U>

procedure cyclicAlias()
  opaque
{
  var x: A<int> := 0;
//                 ^ error: expected 'A<int>', got 'int'
  assert true
};
#end

/-! ## Expansion does not widen

`take` declares its parameter as `Foo<int>`, an alias of `Box<int>`. Passing a `Box<bool>`
has to be rejected: the alias is unfolded so the comparison can be made at all, and then the
comparison is the ordinary strict one. If unfolding also relaxed the check, every aliased
parameter would accept every instantiation. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var val: T }
type Foo<T> = Box<T>
procedure take(b: Foo<int>) returns (r: int) opaque { r := 0 };

procedure aliasWrongArgument()
  opaque
  modifies *
{
  var x: Box<bool> := new Box<bool>;
  var g: int := take(x);
//                   ^ error: expected 'Foo<int>', got 'Box<bool>'
  assert g == 0
};
#end
