/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # A composite's declared type pins its runtime type tag

`LowerComposite` lowers each composite `C` to a free constrained type over `Composite` whose
constraint is `v is C`. The constraint is assumed wherever a value of the type enters and is
never asserted, so a value declared `C` is known to be a `C` without seeing its allocation. -/

/-! ## Inputs -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Cat extends Animal { var lives: int }

procedure paramIsItsType(d: Dog) opaque { assert d is Dog };
procedure paramIsAncestor(d: Dog) opaque { assert d is Animal };
procedure paramIsNotSibling(d: Dog) opaque { var a: Animal := d; assert !(a is Cat) };
procedure upcastThenDowncast(d: Dog) opaque { var a: Animal := d; var e: Dog := a as Dog };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }

procedure supertypeIsNotSubtype(a: Animal) opaque { assert a is Dog };
//                                                  ^^^^^^^^^^^^^^^ error: assertion does not hold
procedure unguardedDowncast(a: Animal) opaque { var d: Dog := a as Dog };
//                                              ^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
#end

/-! ## Call results, field reads, quantifiers -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Kennel {
  var dog: Dog
  var pet: Animal
}

procedure makeDog() returns (r: Dog) opaque;
procedure callResult() opaque { var d: Dog := makeDog(); assert d is Dog };
procedure fieldRead(k: Kennel) opaque { assert k#dog is Dog };
procedure forallDogs() opaque { assert forall(d: Dog) => d is Animal };
#end

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Kennel {
  var dog: Dog
  var pet: Animal
}

procedure ancestorFieldRead(k: Kennel) opaque { assert k#pet is Dog };
//                                              ^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
#end

/-! ## Throwing procedures -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Err {}

procedure maybeDog(b: bool) returns (r: Dog)
  throws (e: Err)
  opaque;
procedure throwingCallResult()
  throws (e: Err)
  opaque
{
  var d: Dog := maybeDog(true);
  assert d is Dog
};
#end

#eval testLaurelVerification <|
#strata
program Laurel;
constrained nat = x: int where x >= 0 witness 0
composite Err {}

procedure negativeNat(b: bool) returns (r: nat)
//        ^^^^^^^^^^^ error: assertion does not hold
//                                         ^^^ error: postcondition does not hold
  throws (e: Err)
  opaque
{
  if b then { var err: Err := new Err; throw err };
  r := 0 - 3
//^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A heap field shared at different types

`D` is both a `Box<Dog>` and a `Box<Animal>`, so `Box.v` can hold a `Cat` while its `Box<Dog>`
view types it `Dog`. The read is where the declared type stops being a fact, so it is checked
there, as Java's erasure cast is. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { var name: int }
composite Cat extends Animal { var lives: int }
composite Box<T> { var v: T }
composite D extends Box<Dog>, Box<Animal> { }

procedure takeDog(d: Dog) opaque ensures d is Dog { };
procedure catThroughDogView() opaque modifies * {
  var x: D := new D;
  var a: Box<Animal> := x;
  var b: Box<Dog> := x;
  var c: Cat := new Cat;
  a#v := c;
  var t: Dog := b#v;
//                ^ error: the value read from a field that another generic instantiation shares has its declared type does not hold
  takeDog(t);
  assert false
};
#end


#eval testLaurelVerification <|
#strata
program Laurel;
composite «p.Animal» { var legs: int }
composite «p.Dog» extends «p.Animal» { var name: int }
composite «p.Cat» extends «p.Animal» { var lives: int }
composite «p.Box»<T> { var v: T }
composite «p.D» extends «p.Box»<«p.Dog»>, «p.Box»<«p.Animal»> { }

procedure takeDog(d: «p.Dog») opaque ensures d is «p.Dog» { };
procedure catThroughDogViewDotted() opaque modifies * {
  var x: «p.D» := new «p.D»;
  var a: «p.Box»<«p.Animal»> := x;
  var b: «p.Box»<«p.Dog»> := x;
  var c: «p.Cat» := new «p.Cat»;
  a#v := c;
  var t: «p.Dog» := b#v;
//                    ^ error: the value read from a field that another generic instantiation shares has its declared type does not hold
  takeDog(t);
  assert false
};
#end
