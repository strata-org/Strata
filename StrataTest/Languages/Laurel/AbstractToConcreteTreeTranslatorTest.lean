/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

/-
Tests that the Laurel AST to DDM concrete syntax tree conversion
(programToStrata) preserves program structure through roundtripping.
-/

meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
meta import Strata.Languages.Laurel.Grammar.LaurelGrammar
meta import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
meta import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator

meta section

open Strata
open StrataDDM (initDialect)
open StrataDDM.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

private def parseLaurel (input : String) : IO Program := do
  let inputCtx := StrataDDM.Parser.stringInputContext "test" input
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
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
  match Laurel.TransM.run .none (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"DDM roundtrip parse errors: {e}")
  | .ok program2 => pure (laurelToText program2)

/-- Parse text, roundtrip through DDM, print, then re-parse the output and verify convergence -/
private def roundtrip (input : String) : IO String := do
  let program ← parseLaurel input
  let firstPass ← roundtripViaDDM program
  -- Re-parse the output and verify it produces the same text (convergence)
  let reparsed ← parseLaurel firstPass
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
#eval do IO.println (← roundtrip r"procedure foo()
  opaque
{ assert true; assert false };")

/--
info: procedure add(x: int, y: int): int
  opaque
{
  x + y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure add(x: int, y: int): int
  opaque
{ x + y };")

/--
info: function aFunction(x: int): int
{
  x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"function aFunction(x: int): int
{ x };")

/--
info: composite Point { var x: int var y: int }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
composite Point {
  var x: int
  var y: int
}
")

/--
info: procedure test(x: int): int
  opaque
{
  if x > 0 then x else 0 - x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure test(x: int): int
  opaque
{ if x > 0 then x else 0 - x };")

/--
info: procedure divide(x: int, y: int): int
  requires y != 0
  opaque
  ensures result >= 0
{
  x / y
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure divide(x: int, y: int): int
  requires y != 0
  opaque
  ensures result >= 0
{ x / y };
")

/--
info: procedure test()
  opaque
{
  assert forall(x: int) => x == x;
  assert exists(y: int) => y > 0
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure test()
  opaque
{
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
")

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
#eval do IO.println (← roundtrip r"
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
")

/--
info: datatype Color { Red, Green, Blue }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"datatype Color { Red, Green, Blue }")

/--
info: datatype Pair { MkPair(fst: int, snd: bool) }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"datatype Pair { MkPair(fst: int, snd: bool) }")

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
#eval do IO.println (← roundtrip r"
composite Animal {}
composite Dog extends Animal {}
procedure test(a: Animal): bool
  opaque
{ a is Dog };
")

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
#eval do IO.println (← roundtrip r"
procedure test()
  opaque
{
    var x: int := 0;
    while(x < 10)
      invariant x >= 0
    { x := x + 1 }
};
")

-- Additional coverage: constrained types

/--
info: constrained Positive = v: int where v > 0 witness 1
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"constrained Positive = v: int where v > 0 witness 1")

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
#eval do IO.println (← roundtrip r"
composite Container { var value: int }
procedure modify(c: Container)
  opaque
  ensures true
  modifies c
{ c#value := c#value + 1; true };
")

-- Additional coverage: nondeterministic holes

/--
info: procedure test(): int
  opaque
{
  <??>
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure test(): int
  opaque
{ <??> };")

-- Valueless return (issue #1353): a bare `return` round-trips as `.Return none`,
-- not as the old `return { }` block hack, and re-parses stably.
/--
info: procedure earlyExit(b: bool)
  opaque
{
  if b then {
    return
  };
  assert true
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure earlyExit(b: bool)
  opaque
{ if b then { return }; assert true };")

end Strata.Laurel
end
