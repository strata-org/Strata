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
global's initializer ends the run too. A false `assume` ends the run as infeasible
without evaluating the rest, with no `finally` either, even in a handler's guard; a true
one lets the run carry on. An exception escaping a procedure that does not declare
`throws` is a failed check and ends the run the same way, so an enclosing `catch` in the
caller does not run.
-/

meta import StrataLaurel.Implementation
meta import StrataLaurel.Implementation.Interpreter

meta section

open Strata
open Strata.Laurel

private def run (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<refusal>" src : IO LaurelProgram)
  let p := (resolve parsed).program
  let (_, failures, outcome) ← Strata.Laurel.Interpreter.evalProgramWithOutcome {}
    { entryProcedure := "main", dumpState := false, printAsserts := false } p
  let outcome := match outcome with
    | .refused r => s!"refused: {r}"
    | .completed => "completed"
    | .escaped v => s!"escaped {v.display}"
    | .outOfFuel => "out of fuel"
    | .infeasible => "infeasible"
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

/-- info: failures: #[]
refused: cannot enumerate the values of a quantifier over int
-/
#guard_msgs in
#eval run "
procedure main() opaque { assume forall(i: int) => i == i; assert false };"

/-- info: failures: #[]
refused: cannot enumerate the values of a quantifier over int
-/
#guard_msgs in
#eval run "
procedure main() opaque { assert forall(i: int) => i == i; assert false };"

/-- info: failures: #[]
infeasible
-/
#guard_msgs in
#eval run "
procedure main() opaque { assume false; assert false };"

/-- info: failures: #[assertion does not hold]
completed
-/
#guard_msgs in
#eval run "
procedure main() opaque { assume true; assert false };"

/-- info: failures: #[]
infeasible
-/
#guard_msgs in
#eval run "
composite Err {}
procedure main() opaque {
  try { var x: Err := new Err; throw x }
  catch e when { assume false; true } { }
  finally { assert false }
};"

/-- info: failures: #[exception #0 escapes 'main', which does not declare `throws`]
infeasible
-/
#guard_msgs in
#eval run "
composite Err {}
procedure main() opaque { var x: Err := new Err; throw x };"

/-- info: failures: #[exception #0 escapes 'f', which does not declare `throws`]
infeasible
-/
#guard_msgs in
#eval run "
composite Err {}
procedure f() opaque { var x: Err := new Err; throw x };
procedure main() opaque { var h: bool := false; try { f() } catch e { h := true }; assert h };"
