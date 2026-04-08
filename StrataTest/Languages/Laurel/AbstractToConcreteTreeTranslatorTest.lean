/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Laurel AST to DDM concrete syntax tree conversion
(programToStrata) preserves program structure through roundtripping.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Languages.Laurel.LaurelFormat

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

private def parseLaurel (input : String) : IO Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
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

/-- Roundtrip through the DDM tree: Laurel AST → Strata.Program → Laurel AST → text -/
private def roundtripViaDDM (prog : Program) : IO String := do
  let strataProgram := programToStrata prog
  match Laurel.TransM.run .none (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"DDM roundtrip parse errors: {e}")
  | .ok program2 => pure (laurelToText program2)

private def roundtrip (input : String) : IO String := do
  let program ← parseLaurel input
  roundtripViaDDM program

private def roundtripConverges (input : String) : IO Unit := do
  let program ← parseLaurel input
  let original := laurelToText program
  let roundtripped ← roundtripViaDDM program
  if original != roundtripped then
    throw (IO.userError s!"Not convergent.\nOriginal:\n{original}\nRoundtripped:\n{roundtripped}")
  IO.println "ok"

-- Emit tests: verify the output format

/--
info: procedure foo() returns
()
deterministic
{ assert true; assert false }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure foo() { assert true; assert false };")

/--
info: procedure add(x: int, y: int) returns
(result: int)
deterministic
{ x + y }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure add(x: int, y: int): int { x + y };")

/--
info: function aFunction(x: int) returns
(result: int)
deterministic
{ x }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"function aFunction(x: int): int { x };")

/--
info: composite Point { var x: int; var y: int }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
composite Point {
  var x: int
  var y: int
}
")

/--
info: procedure test(x: int) returns
(result: int)
deterministic
{ if x > 0 then x else 0 - x }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure test(x: int): int { if x > 0 then x else 0 - x };")

/--
info: procedure divide(x: int, y: int) returns
(result: int)
requires y != 0
deterministic
 ensures result >= 0 := { x / y }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure divide(x: int, y: int): int
  requires y != 0
  ensures result >= 0
{ x / y };
")

/--
info: procedure test() returns
()
deterministic
{ assert forall x: int => x == x; assert exists y: int => y > 0 }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure test() {
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
")

/--
info: composite Point { var x: int; var y: int }

procedure test() returns
(result: int)
deterministic
{ var p: Point := new Point; p#x := 5; p#x }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
composite Point {
  var x: int
  var y: int
}
procedure test(): int {
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
info: composite Animal {  }

composite Dog extends Animal {  }

procedure test(a: Animal) returns
(result: bool)
deterministic
{ a is Dog }
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
composite Animal {}
composite Dog extends Animal {}
procedure test(a: Animal): bool { a is Dog };
")

-- Roundtrip convergence tests: parse → programToStrata → genericToLaurel → formatProgram = formatProgram of original

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"procedure foo() { assert true };"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"function add(x: int, y: int): int { x + y };"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"
procedure test() {
    var x: int := 0;
    while(x < 10)
      invariant x >= 0
    { x := x + 1 }
};
"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"datatype Color { Red, Green, Blue }"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"
composite Point {
  var x: int
  var y: int
}
procedure test(): int {
    var p: Point := new Point;
    p#x := 5;
    p#x
};
"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"
procedure divide(x: int, y: int): int
  requires y != 0
  ensures result >= 0
{ x / y };
"

/-- info: ok -/
#guard_msgs in
#eval roundtripConverges r"
procedure test() {
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
"

end Strata.Laurel
