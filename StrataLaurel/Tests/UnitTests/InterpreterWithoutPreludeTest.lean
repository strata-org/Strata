/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
The Laurel interpreter reports a partial operation's precondition through the prelude
declaration that carries it. A program run without the prelude, as
`runInternalLaurel` runs one, has nothing to report through, so a division by zero
or an out-of-range sequence read is an error there rather than a silent continuation,
while the same operations inside their precondition still run.
-/

meta import StrataLaurel.Implementation
meta import StrataLaurel.Implementation.Interpreter

meta section

open Strata
open Strata.Laurel

private def run (src : String) : IO Unit := do
  let p ← (Strata.parseLaurelText "<no-prelude>" src : IO Program)
  try
    let (_, failures) ← Strata.Laurel.Interpreter.evalProgram {}
      { entryProcedure := "main", dumpState := false, printAsserts := false } p
    IO.println s!"failures: {failures.size}"
  catch e => IO.println s!"error: {e}"

/-- info: failures: 0
-/
#guard_msgs in
#eval run "
procedure main() opaque {
  var y: int := 4 / 2;
  assert y == 2
};"

/-- info: failures: 0
-/
#guard_msgs in
#eval run "
procedure main() opaque {
  var z: real := 0.0;
  var y: real := 1.0 / z
};"

/-- info: error: '$div' applied outside its precondition, and the program has no prelude declaration to report it
-/
#guard_msgs in
#eval run "
procedure main() opaque {
  var z: int := 0;
  var y: int := 1 / z
};"

/-- info: error: 'seqSelect' applied outside its precondition, and the program has no prelude declaration to report it
-/
#guard_msgs in
#eval run "
procedure main() opaque {
  var s: Sequence<int> := seqEmpty();
  var x: int := seqSelect(s, 0)
};"
