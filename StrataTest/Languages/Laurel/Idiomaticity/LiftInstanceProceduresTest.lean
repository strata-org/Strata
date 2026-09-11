/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Before/after tests for the `LiftInstanceProcedures` pass (see
LiftInstanceProcedures.lean). Each `#strata` block is the *source* — instance
procedures declared inside `composite` blocks (the "before"); the `#guard_msgs`
block is the lifted program the pass produces (the "after"), printed as Laurel
source.

The pass lifts every instance procedure to a top-level static procedure and
rewrites `obj#method(args)` call sites to the lifted name (prepending the
receiver). For a method OVERRIDDEN by a strict descendant it additionally
generates dynamic dispatch:

  * the real body is lifted to `<T>$<m>$impl`;
  * the entry `<T>$<m>` becomes a runtime-tag DISPATCHER
    `if self is O1 then O1$m$impl(self as O1, …) else … else T$m$impl(self, …)`
    (most-derived-first), carrying `T`'s own contract as tag-conditioned posts
    (`dispatcherPosts`): owner posts guarded by the fallthrough condition, plus
    each overrider's posts guarded by its tag.

A method overridden nowhere gets the plain static lift `<T>$<m> = body` (no
dispatcher, no `$impl`). The pass needs a resolved program
(`needsResolves := true`), so each test resolves first and drives
`liftInstanceProceduresPass.run`.
-/

import StrataTest.Util.TestLaurel
import Strata.Languages.Laurel.LiftInstanceProcedures
import Strata.Languages.Laurel.Resolution

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Resolve `program`, run `LiftInstanceProcedures`, and print the resulting
    program as Laurel source: the composite types (now with empty
    `instanceProcedures`) then the static procedures (the lifted bodies,
    dispatchers, and `$impl`s), plus any diagnostics. -/
private def printLifted (program : StrataDDM.Program) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
  let (lifted, diags, _) := liftInstanceProceduresPass.run {} result.program result.model
  IO.println "-- types --"
  for ty in lifted.types do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format ty)))
  IO.println "-- procedures --"
  for proc in lifted.staticProcedures do
    IO.println (toString (Std.Format.pretty (Std.ToFormat.format proc)))
  for d in diags do
    IO.println s!"diagnostic: {d.message}"

/-! ## Non-overridden method: plain static lift

A single composite with a method no one overrides. `Box#get` lifts to a plain
static `Box$get(self: Box)`; the `obj#get()` call site is rewritten to
`Box$get(obj)`. No dispatcher, no `$impl`. -/

/--
info: -- types --
composite Box { var v: int }
-- procedures --
procedure u()
  opaque
{
  var b: Box := new Box;
  var x: int := Box$get(b);
  assert 1 == 1
};
procedure Box$get(self: Box)
  returns (r: int)
  opaque
  ensures r == self#v
{
  r := self#v
};
-/
#guard_msgs in
#eval printLifted
#strata
program Laurel;
composite Box { var v: int
  procedure get(self: Box) returns (r: int) opaque ensures r == self#v { r := self#v };
}
procedure u() opaque { var b: Box := new Box; var x: int := b#get(); assert 1 == 1 };
#end

/-! ## Overridden method: dispatcher + `$impl` split

`Animal.speak` is overridden by `Dog.speak`, so the entry `Animal$speak` becomes a
runtime-tag dispatcher (`if self is Dog then Dog$speak$impl(self as Dog) else
Animal$speak$impl(self)`) with tag-conditioned posts, the two real bodies lift to
`Animal$speak$impl` / `Dog$speak$impl`, and `Dog$speak` (no descendants) is a
fallthrough-only dispatcher. -/

/--
info: -- types --
composite Animal { }
composite Dog extends Animal { }
-- procedures --
procedure u()
  opaque
{
  var a: Animal := new Dog;
  var x: int := Animal$speak(a);
  assert 1 == 1
};
procedure Animal$speak$impl(self: Animal)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0
};
procedure Animal$speak(self: Animal)
  returns (r: int)
  opaque
  ensures !(self is Dog) ==> r >= 0
  ensures self is Dog ==> r == 5
if self is Dog
  then {
    var $self$Dog: Dog := self as Dog;
    r := Dog$speak$impl($self$Dog)
  }
  else {
    r := Animal$speak$impl(self)
  };
procedure Dog$speak$impl(self: Dog)
  returns (r: int)
  opaque
  ensures r == 5
{
  r := 5
};
procedure Dog$speak(self: Dog)
  returns (r: int)
  opaque
  ensures r == 5
{
  r := Dog$speak$impl(self)
};
-/
#guard_msgs in
#eval printLifted
#strata
program Laurel;
composite Animal {
  procedure speak(self: Animal) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite Dog extends Animal {
  procedure speak(self: Dog) returns (r: int) opaque ensures r == 5 { r := 5 };
}
procedure u() opaque { var a: Animal := new Dog; var x: int := a#speak(); assert 1 == 1 };
#end

/-! ## Two sibling overriders: nested dispatcher chain + multi-clause posts

`Animal.speak` is overridden by BOTH `Dog` and `Cat`, so `Animal$speak`'s body is a
nested `if self is _ then _ else (if self is _ …)` chain over both overriders, and its
posts carry one tag-guarded clause per overrider plus the fallthrough-guarded owner
post (`!(self is Dog) & !(self is Cat) ==> …`). Pins the multi-overrider shape the
single-child case above does not exercise. -/

/--
info: -- types --
composite Animal { }
composite Dog extends Animal { }
composite Cat extends Animal { }
-- procedures --
procedure u()
  opaque
{
  var a: Animal := new Dog;
  var x: int := Animal$speak(a);
  assert 1 == 1
};
procedure Animal$speak$impl(self: Animal)
  returns (r: int)
  opaque
  ensures r >= 0
{
  r := 0
};
procedure Animal$speak(self: Animal)
  returns (r: int)
  opaque
  ensures !(self is Cat) & !(self is Dog) ==> r >= 0
  ensures self is Cat ==> r == 3
  ensures self is Dog ==> r == 5
if self is Cat
  then {
    var $self$Cat: Cat := self as Cat;
    r := Cat$speak$impl($self$Cat)
  }
  else if self is Dog
    then {
      var $self$Dog: Dog := self as Dog;
      r := Dog$speak$impl($self$Dog)
    }
    else {
      r := Animal$speak$impl(self)
    };
procedure Dog$speak$impl(self: Dog)
  returns (r: int)
  opaque
  ensures r == 5
{
  r := 5
};
procedure Dog$speak(self: Dog)
  returns (r: int)
  opaque
  ensures r == 5
{
  r := Dog$speak$impl(self)
};
procedure Cat$speak$impl(self: Cat)
  returns (r: int)
  opaque
  ensures r == 3
{
  r := 3
};
procedure Cat$speak(self: Cat)
  returns (r: int)
  opaque
  ensures r == 3
{
  r := Cat$speak$impl(self)
};
-/
#guard_msgs in
#eval printLifted
#strata
program Laurel;
composite Animal {
  procedure speak(self: Animal) returns (r: int) opaque ensures r >= 0 { r := 0 };
}
composite Dog extends Animal {
  procedure speak(self: Dog) returns (r: int) opaque ensures r == 5 { r := 5 };
}
composite Cat extends Animal {
  procedure speak(self: Cat) returns (r: int) opaque ensures r == 3 { r := 3 };
}
procedure u() opaque { var a: Animal := new Dog; var x: int := a#speak(); assert 1 == 1 };
#end

end Laurel
