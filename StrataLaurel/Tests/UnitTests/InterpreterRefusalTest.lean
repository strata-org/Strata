/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
A refused call ends the run. The run keeps the failures found so far, the refused
call's own precondition included, and the refusal names the procedures that led to it.
No `finally` runs after it, whether the call is in the `try` body, a handler or a
handler's guard: each `finally` below fails an assertion if it runs. A refusal in a
global's initializer ends the run too.
-/

meta import StrataLaurel.Implementation
meta import StrataLaurel.Implementation.Interpreter

meta section

open Strata
open Strata.Laurel

private def run (src : String) : IO Unit := do
  let p ← (Strata.parseLaurelText "<refusal>" src : IO LaurelProgram)
  let (_, failures, outcome) ← Strata.Laurel.Interpreter.evalProgramWithOutcome {}
    { entryProcedure := "main", dumpState := false, printAsserts := false } p
  let outcome := match outcome with
    | .refused r => s!"refused: {r}"
    | .completed => "completed"
    | .escaped v => s!"escaped {v.display}"
    | .outOfFuel => "out of fuel"
  IO.println s!"failures: {failures.map (·.message)}"
  IO.println outcome

/-- info: failures: #[assertion does not hold, precondition does not hold]
refused: procedure 'positive' has no implementation, so its output 'r' is undetermined
-/
#guard_msgs in
#eval run "
procedure positive(x: int) returns (r: int) requires x > 0 opaque ensures r > 0;
procedure main() opaque { assert 1 == 2; var r: int := positive(0) };"

/-- info: failures: #[]
refused: procedure 'positive' has no implementation, so its output 'r' is undetermined [in helper]
-/
#guard_msgs in
#eval run "
procedure positive() returns (r: int) opaque ensures r > 0;
procedure helper() opaque { var r: int := positive() };
procedure main() opaque { helper() };"

/-- info: failures: #[]
refused: procedure 'positive' has no implementation, so its output 'r' is undetermined
-/
#guard_msgs in
#eval run "
procedure positive() returns (r: int) opaque ensures r > 0;
procedure main() opaque { try { var r: int := positive() } finally { assert false } };"

/-- info: failures: #[]
refused: procedure 'positive' has no implementation, so its output 'r' is undetermined
-/
#guard_msgs in
#eval run "
composite Err {}
procedure positive() returns (r: int) opaque ensures r > 0;
procedure main() opaque {
  try { var x: Err := new Err; throw x }
  catch e { var r: int := positive() }
  finally { assert false }
};"

/-- info: failures: #[]
refused: procedure 'flag' has no implementation, so its output 'b' is undetermined
-/
#guard_msgs in
#eval run "
composite Err {}
procedure flag() returns (b: bool) opaque;
procedure main() opaque {
  try { var x: Err := new Err; throw x }
  catch e when flag() { }
  finally { assert false }
};"

/-- info: failures: #[]
refused: procedure 'positive' has no implementation, so its output 'r' is undetermined
-/
#guard_msgs in
#eval run "
procedure positive() returns (r: int) opaque ensures r > 0;
var g: int := positive()
procedure main() opaque { assert false };"
