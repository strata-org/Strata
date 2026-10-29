/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # User names that collide with ones a lowering pass generates

Most generated names are in the reserved `$`-namespace, which a user name may not enter — so
they cannot collide, and `DollarNamesRejected.lean` covers that boundary. Two families are
not `$`-prefixed and so genuinely are reserved:

* the heap-model types `Heap`, `Field`, `TypeTag` and `Composite`;
* monomorph names, which have the shape `Box$a1$int` — a `$` appears, but not leading, so
  the name is spellable.

Each has to be reported AT the user's own declaration with a rename hint. Reporting it at the
generated name instead would point at a source range that does not exist, and letting it
through would silently merge the user's type with the generated one.

What makes these worth pinning beyond the message is the CASCADE. A collision makes every
later use of the name ill-typed, so the naive diagnostic set is the real error buried under a
pile of `expected 'Composite', got 'Field'` follow-ons — and, for a monomorph collision, an
internal-error net firing on top. The tests below pin that only the collision itself is
reported, and that with TWO independent collisions BOTH are still reported: the cascade
filter keys off whether an error mentions a colliding name, not off a count.

BUG: these collisions are detected too late. The reserved heap-model names are fixed and the
monomorph name shape is derivable from the generic declarations, so both are knowable at
resolution — yet nothing fires until a lowering pass has generated the colliding name and
re-resolution trips over it. That is why these cases sit here under `testLaurelExecution`
rather than in `Resolution/` under `testLaurelResolution`: the resolver currently reports
nothing for them. Detecting the clash in resolution would let them move.

Neither interpreter runs any of these, and that follows from the BUG above. The Core path is
rejected during lowering, so there is no program left to run. The standalone Laurel
interpreter never runs the lowering passes that generate the colliding name, so an `entry`
there would execute the program happily and report NOTHING — leaving the annotated collision
unfired. Both halves of that go away once the clash is detected in resolution.
-/

/-! ## A monomorph-shaped name

`Box$a1$int` is exactly what `Box<int>` monomorphizes to, so declaring it alongside
`composite Box<T>` collides. The diagnostic is located at the user's declaration — line 4
below, not at the source-less synthetic one — which is the property a bare "some error was
reported" check would miss. -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Box<T> { var val: T }
composite Box$a1$int { var val: bool }
//        ^^^^^^^^^^ error: 'Box$a1$int' collides with a name generated for a generic-composite instantiation; rename it (identifiers with the '$aN$' instantiation-tag shape can clash)

procedure useBox()
  opaque
  modifies *
{
  var bi: Box<int> := new Box<int>;
  bi#val := 7;
  assert bi#val == 7
};
#end

/-! ## A reserved heap-model type name -/

#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Field { var val: int }
//        ^^^^^ error: Duplicate definition 'Field' is already defined in this scope

procedure useField()
  opaque
  modifies *
{
  var b: Field := new Field;
  b#val := 7;
  assert b#val == 7
};
#end

-- TWO independent collisions in one program: both are reported. The cascade filter drops
-- each collision's own type-mismatch follow-ons, so a filter that worked by count — or that
-- stopped at the first collision — would lose the second one here.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
composite Field { var val: int }
//        ^^^^^ error: Duplicate definition 'Field' is already defined in this scope
composite TypeTag { var val: int }
//        ^^^^^^^ error: Duplicate definition 'TypeTag' is already defined in this scope

procedure useBoth()
  opaque
  modifies *
{
  var f: Field := new Field;
  var t: TypeTag := new TypeTag;
  assert f#val == t#val
};
#end
