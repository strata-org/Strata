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
  let text := (formatProgram prog).pretty
  let lines := text.splitOn "\n" |>.map (fun s => (s.trimAsciiEnd).toString)
  "\n".intercalate lines

/-- Roundtrip through the DDM tree: Laurel AST → StrataDDM.Program → Laurel AST → text -/
private def roundtripViaDDM (prog : Program) : IO String := do
  let strataProgram := programToStrata prog
  match Laurel.TransM.run .none (Laurel.parseProgram strataProgram) with
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
info: function aFunction(x: int): int
{
  x
};
-/
#guard_msgs in
#eval do IO.println (← roundtrip
#strata
program Laurel;
function aFunction(x: int): int
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
  if x > 0 then x else 0 - x
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
#eval do IO.println (← roundtrip
#strata
program Laurel;
procedure divide(x: int, y: int): int
  requires y != 0
  opaque
  ensures result >= 0
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

end Strata.Laurel
