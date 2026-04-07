/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the Laurel AST to DDM concrete syntax conversion produces
valid Laurel syntax that can be parsed back.
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
  (formatLaurelDDM prog).pretty

private def roundtrip (input : String) : IO String := do
  let program ← parseLaurel input
  pure (laurelToText program)

private def roundtripParse (input : String) : IO Unit := do
  let program ← parseLaurel input
  let text := laurelToText program
  let _ ← parseLaurel text
  IO.println "ok"

-- Emit tests: verify the output format

/--
info: procedure foo()
{ assert true; assert false };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure foo() { assert true; assert false };")

/--
info: procedure add(x: int, y: int): int
{ x + y };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure add(x: int, y: int): int { x + y };")

/--
info: function aFunction(x: int): int
{ x };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"function aFunction(x: int): int { x };")

/--
info: composite Point {
  var x: int
  var y: int
}
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
{ if x > 0 then x else 0 - x };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"procedure test(x: int): int { if x > 0 then x else 0 - x };")

/--
info: procedure divide(x: int, y: int): int
  requires y != 0
  ensures result >= 0
{ x / y };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure divide(x: int, y: int): int
  requires y != 0
  ensures result >= 0
{ x / y };
")

/--
info: procedure test()
{ assert forall(x: int) => x == x; assert exists(y: int) => y > 0 };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
procedure test() {
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
")

/--
info: composite Point {
  var x: int
  var y: int
}

procedure test(): int
{ var p: Point := new Point; p#x := 5; p#x };
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
info: datatype Color {Red, Green, Blue}
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"datatype Color { Red, Green, Blue }")

/--
info: datatype Pair {MkPair(fst: int, snd: bool)}
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"datatype Pair { MkPair(fst: int, snd: bool) }")

/--
info: composite Animal {
}

composite Dog extends Animal {
}

procedure test(a: Animal): bool
{ a is Dog };
-/
#guard_msgs in
#eval do IO.println (← roundtrip r"
composite Animal {}
composite Dog extends Animal {}
procedure test(a: Animal): bool { a is Dog };
")

-- Roundtrip parse tests: parse → emit → parse

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"procedure foo() { assert true };"

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"function add(x: int, y: int): int { x + y };"

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"
procedure test() {
    var x: int := 0;
    while(x < 10)
      invariant x >= 0
    { x := x + 1 }
};
"

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"datatype Color { Red, Green, Blue }"

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"
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
#eval roundtripParse r"
procedure divide(x: int, y: int): int
  requires y != 0
  ensures result >= 0
{ x / y };
"

/-- info: ok -/
#guard_msgs in
#eval roundtripParse r"
procedure test() {
    assert forall(x: int) => x == x;
    assert exists(y: int) => y > 0
};
"

end Strata.Laurel
