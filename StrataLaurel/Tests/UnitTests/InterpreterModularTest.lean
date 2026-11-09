/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
With a modular backend, a call checks the callee's preconditions at the call site and
runs the callee muted: the callee's own failed checks are not reported and its
postconditions are not checked. The entry procedure itself is not muted. Without a
modular backend the same program reports the callee's failures too.
-/

meta import StrataLaurel.Implementation
meta import StrataLaurel.Implementation.Interpreter

meta section

open Strata
open Strata.Laurel

private def run (modular : Bool) (src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<modular>" src : IO LaurelProgram)
  let p := (resolve parsed).program
  let (_, failures, outcome) ← Strata.Laurel.Interpreter.evalProgramWithOutcome
    { modular := modular }
    { entryProcedure := "main", dumpState := false, printAsserts := false } p
  let outcome := match outcome with
    | .refused r => s!"refused: {r}"
    | .completed => "completed"
    | .escaped v => s!"escaped {v.display}"
    | .outOfFuel => "out of fuel"
    | .infeasible => "infeasible"
  IO.println s!"failures: {failures.map (·.message)}"
  IO.println outcome

private def staticCalls : String := "
procedure inner(x: int) requires x > 0 opaque ensures false { assert false };
procedure main() opaque { inner(0); inner(1); assert 1 == 2 };"

private def instanceCalls : String := "
composite C {
  procedure m(self: C, x: int) requires x > 0 opaque ensures false { assert false };
}
procedure main() opaque { var c: C := new C; c#m(0); c#m(1); assert 1 == 2 };"

/-- info: failures: #[precondition does not hold, assertion does not hold]
completed
-/
#guard_msgs in
#eval run true staticCalls

/-- info: failures: #[precondition does not hold, assertion does not hold, postcondition does not hold, assertion does not hold, postcondition does not hold, assertion does not hold]
completed
-/
#guard_msgs in
#eval run false staticCalls

/-- info: failures: #[precondition does not hold, assertion does not hold]
completed
-/
#guard_msgs in
#eval run true instanceCalls

/-- info: failures: #[precondition does not hold, assertion does not hold, postcondition does not hold, assertion does not hold, postcondition does not hold, assertion does not hold]
completed
-/
#guard_msgs in
#eval run false instanceCalls
