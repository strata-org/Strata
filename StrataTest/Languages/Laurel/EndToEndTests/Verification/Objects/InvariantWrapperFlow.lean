/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Exhibiting the flow of type information through a wrapper, when the wrapper type
is *invariant* (no gradual escape, no subtyping between wrappers).

Setup: `Dog` is a strict subtype of `Animal` (`Dog extends Animal`). `AnimalBox`
wraps an `Animal` (`var contents: Animal`); `DogBox` wraps a `Dog`. Because a
composite is a *nominal* type, `DogBox` and `AnimalBox` are unrelated —
`DogBox <: AnimalBox` does NOT hold even though `Dog <: Animal`. This is the
analogue of an invariant `Box<·>`: `Box<Dog>` and `Box<Animal>` are distinct,
with no subtyping between them.

`wrap(animal: Animal) returns (box: AnimalBox)` is the wrapper function. The
information flow is:

1. At the call `wrap(dog)` with `dog : Dog`, the argument is *checked* against
   the declared parameter type `Animal` (Laurel's call rule checks each
   argument against its parameter). `Dog <: Animal`, so the argument is
   accepted — the value is viewed at its supertype `Animal` exactly at the call
   boundary.

2. The call *synthesizes* the strict return type `AnimalBox`. There is no
   `DogBox` to fall back to and no `Box`-to-`Box` subtyping, so `AnimalBox` is
   the only type the result can have. An unannotated `var box := wrap(dog)`
   therefore infers `box : AnimalBox`.

3. Consuming `box` where `DogBox` is expected is rejected — the wrapper is
   invariant, so the `Dog <: Animal` on the *contents* does not lift to the
   wrappers. This is the point at which invariance "bites": it forces the
   result to be used at exactly `AnimalBox`, never silently widened or
   narrowed.
-/

-- Positive: the whole flow type-checks. `wrap(dog)` checks `dog : Dog` against
-- the parameter `Animal`, synthesizes `AnimalBox`, and the unannotated `box`
-- infers `AnimalBox`.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { }
composite Dog extends Animal { }
composite AnimalBox { var contents: Animal }

procedure wrap(animal: Animal) returns (box: AnimalBox)
  opaque
  modifies *
{
  box := new AnimalBox;
  box#contents := animal
};

procedure flows() opaque {
  var dog: Dog := new Dog;
  var box := wrap(dog);                    // arg dog:Dog checked <: Animal; box inferred AnimalBox
  var unwrapped: Animal := box#contents;   // the wrapped value reads back at Animal
  assert unwrapped == box#contents
};
#end

-- Negative: the wrapper is invariant. `wrap(dog)` yields `AnimalBox`, which
-- cannot be stored where `DogBox` is expected, even though `Dog <: Animal`.
-- The `Dog <: Animal` on the contents does not lift to a
-- `DogBox <: AnimalBox` on the wrappers.
#eval testLaurelResolution <|
#strata
program Laurel;
composite Animal { }
composite Dog extends Animal { }
composite AnimalBox { var contents: Animal }
composite DogBox { var contents: Dog }

procedure wrap(animal: Animal) returns (box: AnimalBox)
  opaque
  modifies *
{
  box := new AnimalBox;
  box#contents := animal
};

procedure invariantBites() opaque {
  var dog: Dog := new Dog;
  var box: DogBox := wrap(dog)
//                   ^^^^^^^^^ error: expected 'DogBox', got 'AnimalBox'
};
#end
