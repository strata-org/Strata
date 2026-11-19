/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A generic call's undetermined type argument is solved by what surrounds it

Each type parameter of a generic call stands for one not-yet-known type until the call's own
arguments, the call it is an argument of, or the expected type determine it. Only when none does
is it reported, at the call. -/

/-! ## A later sibling argument solves what it can; only what is still open is reported

`three()`, resolved after `two()`, solves its `T`, so only its `U` is reported. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure two<T, U>() returns (r: T) opaque;
procedure three() returns (r: int) opaque;
procedure both<T>(a: T, b: T) opaque;
procedure stillOpen() opaque {
  both(two(), three())
//     ^^^^^ error: cannot infer type argument 'U' of 'two': annotate the variable or output it is assigned to with a concrete type
};
#end

/-! ## An `if` branch's open type argument takes the other branch's type

So the `if` is a `bool`, which disagrees with `3`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<T>() returns (r: T) opaque;
procedure both<T>(a: T, b: T) opaque;
procedure ifJoin(c: bool) opaque {
  both(if c then mk() else true, 3)
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: cannot infer type argument 'T' of 'both': 'bool' and 'int' disagree
};
#end

/-! ## A synthesized argument is checked once the call is solved, on every call path

An `int` binds nothing in a `Set<T>` slot, so the call's own check is what catches it, with the
same message for a constructor and an instance call as for a procedure. -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Bag<T> { MkBag(items: Set<T>) }
procedure takeSet<U>(s: Set<U>) opaque;
composite Holder {
  var n: int
  procedure takeSet<U>(self: Holder, s: Set<U>) opaque;
}
procedure wrongShape(h: Holder) opaque {
  var b: Bag<int> := MkBag(5);
//                         ^ error: cannot pass 'int' as the 'Set<int>' parameter of 'MkBag'
  takeSet(5);
//        ^ error: cannot pass 'int' as the 'Set<U>' parameter of 'takeSet'
  h#takeSet(5)
//          ^ error: cannot pass 'int' as the 'Set<U>' parameter of 'takeSet'
};
#end

/-! ## Outside a procedure too

A global's initializer is a root of inference like a statement: what it leaves open is reported
there. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure zero<T>() returns (r: int) opaque;
var g: int := zero()
//            ^^^^^^ error: cannot infer type argument 'T' of 'zero': the expected type does not determine it either; annotate with a concrete instantiation
procedure p() opaque { };
#end

/-! ## Each open type argument is reported by the call that introduced it, once

`idp`'s `T` is solved to `zero`'s still-open one, which is `zero`'s to report. Next to an
undefined argument the outer call is quiet, and so is the nested call whose variable it took. A
constructor at a slot the hole leaves open is reported like any call, not silenced by the hole. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure zero<T>() returns (r: T) opaque;
procedure idp<T>(x: T) returns (r: T) opaque;
procedure same2<T>(a: Set<T>, b: Set<T>) returns (r: bool) opaque;
datatype Opt<T> { Som(v: T), Non() }
procedure owners() opaque {
  var x := idp(zero());
//             ^^^^^^ error: cannot infer type argument 'T' of 'zero': annotate the variable or output it is assigned to with a concrete type
  var r: bool := same2(nope, setEmpty());
//                     ^^^^ error: Resolution failed: 'nope' is not defined
  assert Non() == <?>
//       ^^^^^ error: cannot infer type argument 'T' of 'Opt': annotate the variable or output it is assigned to with a concrete type
};
#end

/-! ## Beside a hole, an open type argument is reported

With no error reported, a hole excuses nothing: `zero2`'s `T`, which no parameter the hole fills
mentions, and `k4`'s, which its `Opt<T>` does, are reported at their calls, nested in `idp`.
Another argument can still solve them. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure zero2<T, U>(x: U, y: U) returns (r: T) opaque;
procedure idp<T>(x: T) returns (r: T) opaque;
procedure same<T>(a: T, b: T) returns (r: bool) opaque;
procedure p() opaque {
  var x := idp(zero2(<?>, 1));
//             ^^^^^^^^^^^^^ error: cannot infer type argument 'T' of 'zero2': annotate the variable or output it is assigned to with a concrete type
  var b := same(zero2(<?>, 1), 5)
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
datatype Opt<T> { Som(v: T), Non() }
procedure k4<T, U>(x: Opt<T>, y: U) returns (r: T) opaque;
procedure idp<T>(x: T) returns (r: T) opaque;
procedure p() opaque {
  var y := idp(k4(<?>, 1))
//             ^^^^^^^^^^ error: cannot infer type argument 'T' of 'k4': annotate the variable or output it is assigned to with a concrete type
};
#end

/-! ## A call at a non-generic datatype's destructor receiver is solved at that datatype -/

#eval testLaurelResolution <|
#strata
program Laurel;
datatype D { MkD(ref: int) }
procedure mk<T>() returns (r: T) opaque;
procedure p() opaque { var x := D..ref!(mk()) };
#end

/-! ## Overload selection reads a generic candidate's type parameters as open

Each call picks the candidate its second argument fits. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure f<T>(x: T, y: int) opaque;
procedure f<T>(x: T, y: bool) opaque;
procedure p() opaque { f(5, 1); f(5, true) };
#end

/-! ## A datatype destructor is a generic call like any other

Its receiver is checked against the datatype, solves its type arguments, and may itself be solved
by the destructor's parameter. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Rock { var w: int }
datatype Opt<T> { Som(v: T), Non() }
procedure mk<T>() returns (r: T) opaque;
procedure destructors(rk: Rock) opaque {
  var x: int := Opt..v!(rk);
//                      ^^ error: cannot pass 'Rock' as the 'Opt<int>' parameter of 'Opt..v!'
  var y: int := Opt..v!(mk());
  var z: bool := Opt..v!(Som(true))
};
#end

/-! ## Under a type constructor the expected type is evidence, not only a bound

A map's or a datatype's type arguments must equal the expected type's, so the expected type joins
the arguments: `Animal`, which the `Dog` argument fits, rather than `Dog`, which would make the
result unusable. A nested call is handed that instantiation as its slot. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { var age: int }
composite Dog extends Animal { }
datatype Opt<T> { Som(v: T), Non() }
procedure p(d: Dog, a: Animal) opaque {
  var m1: Map<int, Animal> := mapSet(mapEmpty(), 1, d);
  var m2 := mapSet(mapSet(mapEmpty(), 1, d), 2, a);
  var o: Opt<Animal> := Som(d)
};
#end

/-! ## A missing argument leaves its parameter's type argument to the others

The expected type is paired with the result, not with the parameter left without an argument:
`wrap(1)` is a `Box<int>` and `needsBoth(1)`'s `T` stays open. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Box<T> { var v: T }
procedure wrap<T>(a: int, b: T) returns (r: Box<T>) opaque;
procedure needsBoth<T>(a: int, b: T) returns (r: bool) opaque;
procedure p() opaque {
  var x: Box<int> := wrap(1);
  var v: bool := needsBoth(1)
//               ^^^^^^^^^^^^ error: cannot infer type argument 'T' of 'needsBoth': the expected type does not determine it either; annotate with a concrete instantiation
};
#end

/-! ## An expected type that contradicts an argument is reported once, as the mismatch

`Pair<Animal, bool>` fixes `T` for the `Dog` and the `Cat`, but contradicts the `1` at `U`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { var age: int }
composite Dog extends Animal { }
composite Cat extends Animal { }
datatype Pair<A, B> { MkPair(a: A, b: B) }
procedure f<T, U>(a: T, b: T, c: U) returns (r: Pair<T, U>) opaque;
procedure p(dog: Dog, cat: Cat) opaque {
  var x: Pair<Animal, bool> := f(dog, cat, 1)
//                             ^^^^^^^^^^^^^^ error: expected 'Pair<Animal, bool>', got 'Pair<Animal, int>'
};
#end

/-! ## An earlier error's `Unknown` expected type is not reported against

`x`'s type was already reported, so `mk`'s `T` is not; `two`'s `U`, which nothing mentions, still
is. With no error reported, an `Unknown` expected type, as a hole-typed local's, determines nothing. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<T>(tag: int) returns (r: T) opaque;
procedure two<T, U>(x: T, y: T) opaque;
procedure p() opaque {
  var x: Undeclared;
//       ^^^^^^^^^^ error: Resolution failed: 'Undeclared' is not defined
  x := mk(1);
  x := two(1, 2)
//     ^^^^^^^^^ error: cannot infer type argument 'U' of 'two': the expected type does not determine it either; annotate with a concrete instantiation
};
#end

#eval testLaurelResolution <|
#strata
program Laurel;
procedure mk<T>(tag: int) returns (r: T) opaque;
procedure p() opaque {
  var x := <?>;
  x := mk(0)
//     ^^^^^ error: cannot infer type argument 'T' of 'mk': the expected type does not determine it either; annotate with a concrete instantiation
};
#end

/-! ## A declared type variable matches only itself through an ancestor

`Sub<int>` reaches `Base<int>`, which is not `Base<U>` for the caller's own `U`. -/

#eval testLaurelResolution <|
#strata
program Laurel;
composite Base<T> { var v: T }
composite Sub<U> extends Base<U> { }
procedure g<U>(s: Sub<int>) opaque { var b: Base<U> := s };
//                                                     ^ error: expected 'Base<U>', got 'Sub<int>'
#end
