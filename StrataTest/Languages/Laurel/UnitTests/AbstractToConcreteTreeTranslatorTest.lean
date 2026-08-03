/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Laurel AST to DDM concrete syntax tree conversion
(programToStrata) preserves program structure through roundtripping.
-/

import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

private def parseFromStrata (strataProgram : StrataDDM.Program) : IO Program := do
  match Laurel.TransM.run (Strata.Uri.file "test") (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program => pure program

private def laurelToText (prog : Program) : String :=
  -- Trim trailing whitespace per line to avoid whitespace-sensitive test issues
  let text := (formatProgram prog).pretty
  let lines := text.splitOn "\n" |>.map (fun s => (s.trimAsciiEnd).toString)
  "\n".intercalate lines

/-- Roundtrip through the DDM tree: Laurel AST → StrataDDM.Program → Laurel AST → text -/
private def roundtripViaDDM (prog : Program) : IO String := do
  let strataProgram := programToStrata prog
  match Laurel.TransM.run (.file "AbstractToConcreteTreeTranslatorTest.lean")
      (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"DDM roundtrip parse errors: {e}")
  | .ok program2 => pure (laurelToText program2)

/-- Roundtrip a `StrataDDM.Program` (already parsed by `#strata`) through DDM,
    pretty-print, re-parse, and verify convergence. -/
private def roundtrip (strataProgram : StrataDDM.Program) : IO String := do
  let program ← parseFromStrata strataProgram
  let firstPass ← roundtripViaDDM program
  -- Re-parse the output and verify it produces the same text (convergence)
  let inputCtx := StrataDDM.Parser.stringInputContext "test" firstPass
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let reparsedStrata ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let reparsed ← parseFromStrata reparsedStrata
  let secondPass ← roundtripViaDDM reparsed
  if firstPass != secondPass then
    throw (IO.userError s!"Roundtrip does not converge.\nFirst pass:\n{firstPass}\nSecond pass:\n{secondPass}")
  pure firstPass

-- Emit tests: verify the output format

/--
info: procedure foo()
  opaque
{
  assert true;
  assert false
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure foo()
  opaque
{ assert true; assert false };
#end)

/--
info: procedure add(x: int, y: int): int
  opaque
{
  x + y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure add(x: int, y: int): int
  opaque
{ x + y };
#end)

/--
info: procedure aFunction(x: int): int
{
  x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure aFunction(x: int): int
{ x };
#end)

/--
info: composite Point { var x: int var y: int }
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
composite Point {
  var x: int
  var y: int
}
#end)

/--
info: procedure test(x: int): int
  opaque
{
  if x > 0
    then x
    else 0 - x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure test(x: int): int
  opaque
{ if x > 0 then x else 0 - x };
#end)

-- A user parameter named `result` under the short `: T` return form must survive
-- the concrete↔abstract roundtrip unchanged. The short-form auto-output is the
-- reserved `$result` (printed back as `: int`), so the user `result` parameter
-- is never confused with the internal return name: it stays `result`, and the
-- `return result` body still references the parameter.
/--
info: procedure echo(result: int): int
{
  return result
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure echo(result: int): int
{ return result };
#end)

-- A user-named single return output `result` must NOT be collapsed into the
-- short `: T` form: only the reserved `$result` auto-output is (the printer now
-- checks `single.name == resultOutputName`, not the literal `"result"`). So this
-- prints as the explicit `returns (result: int)`, preserving the user's name.
/--
info: procedure foo()
  returns (result: int)
{
  return 42
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure foo() returns (result: int)
{ return 42 };
#end)

-- NOTE: these `divide` roundtrip fixtures put a parameter (`x`) in their
-- `ensures`, not `result`. The short `: T` return form's auto-output is the
-- reserved `$result`, so a bare `result` is just a free identifier now; these
-- tests only exercise `ensures`/`free`/`checked` grammar, so any in-scope name
-- works.
/--
info: procedure divide(x: int, y: int): int
  requires y != 0
  opaque
  ensures x >= 0
{
  x / y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure divide(x: int, y: int): int
  requires y != 0
  opaque
  ensures x >= 0
{ x / y };
#end)

-- The `free`/`checked` condition-mode keywords survive a roundtrip through the
-- DDM concrete tree.
/--
info: procedure divide(x: int, y: int): int
  requires y != 0
  free requires y != 1
  checked requires y != 2
  opaque
  ensures x >= 0
  free ensures x >= 1
  checked ensures x >= 2
{
  x / y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure divide(x: int, y: int): int
  requires y != 0
  free requires y != 1
  checked requires y != 2
  opaque
  ensures x >= 0
  free ensures x >= 1
  checked ensures x >= 2
{ x / y };
#end)

/--
info: procedure test()
  opaque
{
  assert forall(x: int) => x == x;
  assert exists(y: int) => y > 0
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure test()
  opaque
{
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
#end)

/--
info: composite Point { var x: int var y: int }

procedure test(): int
  opaque
{
  var p: Point := new Point;
  p#x := 5;
  p#x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
composite Point {
  var x: int
  var y: int
}
procedure test(): int
  opaque
{
    var p: Point := new Point;
    p#x := 5;
    p#x
};
#end)

/--
info: datatype Color { Red, Green, Blue }
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Color { Red, Green, Blue }
#end)

/--
info: datatype Pair { MkPair(fst: int, snd: bool) }
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Pair { MkPair(fst: int, snd: bool) }
#end)

/--
info: composite Animal { }

composite Dog extends Animal { }

procedure test(a: Animal): bool
  opaque
{
  a is Dog
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
composite Animal {}
composite Dog extends Animal {}
procedure test(a: Animal): bool
  opaque
{ a is Dog };
#end)

-- Additional coverage: while loops

/--
info: procedure test()
  opaque
{
  var x: int := 0;
  while(x < 10)
    invariant x >= 0 {
    x := x + 1
  }
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure test()
  opaque
{
    var x: int := 0;
    while(x < 10)
      invariant x >= 0
    { x := x + 1 }
};
#end)

-- Additional coverage: constrained types

/--
info: constrained Positive = v: int where v > 0 witness 1
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
constrained Positive = v: int where v > 0 witness 1
#end)

-- Additional coverage: modifies clauses

/--
info: composite Container { var value: int }

procedure modify(c: Container)
  opaque
  ensures true
  modifies c
{
  c#value := c#value + 1;
  true
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
composite Container { var value: int }
procedure modify(c: Container)
  opaque
  ensures true
  modifies c
{ c#value := c#value + 1; true };
#end)

-- Additional coverage: nondeterministic holes

/--
info: procedure test(): int
  opaque
{
  <??>
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure test(): int
  opaque
{ <??> };
#end)

-- Valueless return (issue #1353): a bare `return` round-trips as `.Return none`,
-- not as the old `return { }` block hack, and re-parses stably.
/--
info: procedure earlyExit(b: bool)
  opaque
{
  if b
    then {
      return
    };
  assert true
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure earlyExit(b: bool)
  opaque
{ if b then { return }; assert true };
#end)

-- Additional coverage: producer-marked `entry` point (interpreter entry marker)

/--
info: procedure runMe()
  entry
  opaque
{
  assert true
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure runMe()
  entry
  opaque
{ assert true };
#end)

-- Do-while (issue #1358): a `do … while` parses to a post-test `While`
-- (`postTest := true`) and round-trips through the DDM tree via the `doWhile`
-- serialization arm (whose `#[body, cond, invariants]` arg order this
-- exercises), re-parsing stably. The desugaring to a pre-test loop happens
-- later, in the `EliminateDoWhile` pass, not here.
/--
info: procedure loop()
  opaque
{
  var x: int := 0;
  do {
    x := x + 1
  } while(x < 3)
    invariant 0 <= x && x <= 2
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure loop()
  opaque
{
  var x: int := 0;
  do { x := x + 1 } while(x < 3) invariant 0 <= x && x <= 2
};
#end)

-- Generic datatype: the `<T>` type-parameter list survives Abstract→Concrete→Abstract.
/--
info: datatype Option<T> { Nothing, Some(value: T) }
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Option<T> { Nothing, Some(value: T) }
#end)

-- Multiple type parameters: their ORDER (`<A, B>`, not `<B, A>`) is preserved.
/--
info: datatype Either<A, B> { First(a: A), Second(b: B) }
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Either<A, B> { First(a: A), Second(b: B) }
#end)

-- Applied type in a type-annotation position (a procedure parameter): the
-- `Option<int>` annotation uses the new `appliedType` grammar op — distinct from
-- the `<T>` typeParams on the datatype declaration — so this exercises its
-- serialize (`.Applied` → `appliedType`) and deserialize (`appliedType` →
-- `.Applied`) arms, which the datatype-declaration round-trips above do not.
-- The pretty-printer parenthesizes a non-atomic type in a type-argument slot, so
-- `Option<int>` prints as `(Option<int>)`; the `parenType` grammar production
-- makes that re-parse, so the program still converges.
/--
info: datatype Option<T> { Nothing, Some(value: T) }

procedure foo()
  opaque
{
  var o: (Option<int>) := Nothing()
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Option<T> { Nothing, Some(value: T) }
procedure foo() opaque {
  var o: Option<int> := Nothing()
};
#end)

-- Nested applied type as a type argument (`Option<Option<int>>`): exercises the
-- serializer's `args.map highTypeToArg` and deserializer's `mapM translateHighType`
-- recursion, and the `parenType` wrapping the pretty-printer inserts at each
-- nesting level.
-- Only the outer application is parenthesized (the var-type slot); the inner
-- `Option<int>` sits in the `<…>`-delimited argument slot, which needs no parens.
/--
info: datatype Option<T> { Nothing, Some(value: T) }

procedure foo()
  opaque
{
  var o: (Option<Option<int>>) := Nothing()
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
datatype Option<T> { Nothing, Some(value: T) }
procedure foo() opaque {
  var o: Option<Option<int>> := Nothing()
};
#end)

-- Additional coverage: multi-target assignment with an annotated declared target.
-- assignTargetDecl needs @[prec(0)] (like varDecl) or the formatter parenthesizes
-- the trailing Option TypeAnnotation and prints the unparseable `var x(: int)`.

/--
info: procedure twoOut()
  returns (a: int, b: int)
  opaque
{
  a := 1;
  b := 2
};

procedure p()
  opaque
{
  var y: int := 0;
  assign var x: int, y := twoOut();
  assert x == y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure twoOut() returns (a: int, b: int)
  opaque
{ a := 1; b := 2 };
procedure p()
  opaque
{
  var y: int := 0;
  assign var x: int, y := twoOut();
  assert x == y
};
#end)

-- Resolution's Decl-Synth rewrites every unannotated declared target to the
-- annotated form (`some T`), so every resolved program with declared targets
-- prints with `: T` on each one. Build that post-resolution AST shape directly
-- (there is no surface syntax that parses to it here) and check that the
-- printed text parses back and converges.

private def node {t : Type} (v : t) : AstNode t := { val := v, source := default }

private def declTarget (nm : String) (ty : HighType) : AstNode Variable :=
  node (.Declare { name := mkId nm, type := some (node ty) })

private def resolvedMultiAssign : Program :=
  { staticProcedures := [
      { name := mkId "p", inputs := [], outputs := [],
        preconditions := [], decreases := none,
        body := .Opaque []
          (some (node (.Block [
            node (.Assign [declTarget "x" .TInt, declTarget "y" .TBool]
              (node (.StaticCall (mkId "twoOut") [])))
          ] none)))
          [] }
    ],
    staticFields := [], types := [] }

/--
info: procedure p()
  opaque
{
  assign var x: int, var y: bool := twoOut()
};
-/
#guard_msgs in
#eval do
  let text := laurelToText resolvedMultiAssign
  -- The printed text must re-parse; unparseable output is the bug this pins.
  let inputCtx := StrataDDM.Parser.stringInputContext "test" text
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let reparsedStrata ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let reparsed ← parseFromStrata reparsedStrata
  if laurelToText reparsed != text then
    throw (IO.userError s!"multiAssign print does not re-parse to the same text:\n{text}")
  IO.println text

end Strata.Laurel
