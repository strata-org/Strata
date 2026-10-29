/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## A hole must not hide a sibling operand's type error

Overload selection runs on argument types, and `Unknown` (an untyped hole `<?>`, an
undefined identifier, …) is a consistent subtype of *every* parameter type. So an
`Unknown` argument can never rule an overload out, and it matches all of them —
which is why `Synth.staticCall` suppresses its "no overload matches" / "ambiguous
call" diagnostics when a hole is involved: the report would either be spurious or
pile on top of an error the argument already reported for itself.

The suppression has to ask whether the hole is *why* selection failed, not merely
whether one is present. A concrete argument that no candidate accepts rules out
every overload on its own, whether or not a hole sits beside it — so `culpritArg`
checks for exactly that, and only a blameless hole silences the report.

`$eq`/`$neq` need matching care in `InferHoleTypes`. `CoreDefinitionsForLaurel`
declares them `procedure $eq<T>(x: T, y: T) : bool external`, so both slots are the
same uninstantiated `T` and neither can type a hole. Their operands must agree,
though, which makes the first non-hole sibling a sound guess — so `calleeParamTypes`
declines for these two names and `unresolvedOperatorArgType` supplies it, letting
`<?> == "hello"` infer `string`. Typing the hole from `T` would leave it with
nothing and report "could not infer type"; the general rule for a generic callee
blanks only the slots whose declared type mentions a type variable (`mentionsTVar`),
which is right where the slots differ, as in `select<K,V>(map: TotalMap K V, key: K)`.
-/

-- Baseline, no hole: the operator reports.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure baseline() opaque {
  var y: int := 1 + "hello"
//              ^^^^^^^^^^^ error: no overload of '$add' matches the argument types
};
#end

-- With a hole beside the offending operand, the operator still reports: `"hello"`
-- is rejected by every overload of `$add` on its own, so the hole is not to blame.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeBesideWrongOperand() opaque {
  var y: int := <?> + "hello"
//              ^^^^^^^^^^^^^ error: no overload of '$add' matches the argument types
};
#end

-- A hole beside a *compatible* operand must stay silent and still select the `int`
-- overload, so `InferHoleTypes` can read its parameter types and type the hole.
-- This is what the suppression exists to protect.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeBesideCompatibleOperand() opaque {
  var y: int := 1 + <?>;
  assert y == y
};
#end

-- A hole compared against a string takes the sibling's type, so this is an
-- unknown *string* rather than an `int`/`string` mismatch reported as a bug.
#eval testLaurelResolution <|
#strata
program Laurel;
procedure holeComparedToString(s: string) opaque {
  assume <?> == s;
  assert true
};
#end

/-! ## A hole in a GENERIC callee's slot

The rule above blanks only the slots whose declared type mentions a type variable, which is
what lets a hole in a *concrete* slot of a partly-generic signature still be typed. Both
halves need pinning, because they fail in opposite directions: blanking every slot turns the
first case into "could not infer type", and blanking none makes the second report Core's
internal `$hole_N$asFunction` instead of a user-level error.

`InferHoleTypes` should be part of Laurel resolution. Typing a hole from its context is a
resolution question, and "this hole has no type to take" is the same question answered
negatively. It is not done there today: `inferHoleTypesPass` runs in the lowering pipeline, so
`resolve` says nothing about holes either way. That is why ALL THREE cases below run the full
pipeline under `testLaurelExecution` — on `testLaurelResolution` none of them can fail, the
rejecting two because their diagnostic is never emitted and the accepting one because the pass
whose output it describes never runs. Moving the pass into resolution would let all three use
`testLaurelResolution` and mean something.

Only the ACCEPTING case runs: it marks an `entry`, so the typed hole is also executed. The
other two are verification-only because they pin a REJECTION — `could not infer type` comes
out of `inferHoleTypesPass` during Laurel→Core, so the Core path stops there, and the
standalone Laurel interpreter never runs that pass at all and so would report nothing while
the annotation waited to fire. -/

-- A hole in the `int` slot of `f<T>(x: int, y: T)`: concrete, so it is typed from the
-- parameter and the program resolves. On the full pipeline, so that blanking every slot in
-- `InferHoleTypes` would actually break it.
#eval testLaurelExecution {} <|
#strata
program Laurel;
procedure f<T>(x: int, y: T) opaque;
procedure holeInConcreteSlotOfGenericCallee() entry opaque {
  var b: bool := true;
  f(<?>, b);
  assert 1 == 1
};
#end

-- A hole in the `T` slot has nothing to take a type from — `T` is uninstantiated at
-- hole-typing time — so it is reported as a user-level inference failure.
-- Verification-only: the annotated rejection comes from `inferHoleTypesPass` (Laurel→Core),
-- which neither interpreter path can report — see the note above.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure f<T>(x: int, y: T) opaque;
procedure holeInGenericSlot() opaque {
  f(1, <?>);
//     ^^^ error: could not infer type
  assert 1 == 1
};
#end

-- The same shape through a built-in: `select<K, V>(map: TotalMap K V, key: K)`'s key slot is
-- a type variable too, even though it is instantiated at `int` by the map argument. This is
-- the case that makes the rule's granularity visible — the slots of `select` differ, unlike
-- `$eq`'s two identical `T`s.
-- Verification-only for the same reason as the case above.
#eval testLaurelExecution { skipCoreInterpreter := true, skipLaurelInterpreter := true } <|
#strata
program Laurel;
procedure holeInMapKeySlot() opaque {
  var m: TotalMap int bool := mapConst(false);
  var b: bool := select(m, <?>);
//                         ^^^ error: could not infer type
  assert b == b
};
#end
