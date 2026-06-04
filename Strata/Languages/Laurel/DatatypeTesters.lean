/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST

/-!
## Datatype Tester Generation

For each constructor of a datatype, generate an external testing function.
The tester function takes a single argument of the datatype's type and returns
`bool`. Its name is determined by `DatatypeDefinition.testerName`.

This pass runs at the start of the Laurel pipeline, before resolution, so that
the tester functions are available as normal static procedures.
-/

namespace Strata.Laurel

public section

/-- Generate an external tester function for a single constructor of a datatype. -/
private def mkTesterFunction (dt : DatatypeDefinition) (ctor : DatatypeConstructor) : Procedure :=
  let testerName := dt.testerName ctor
  let inputParam : Parameter := {
    name := mkId "value"
    type := { val := .UserDefined dt.name, source := none }
  }
  let outputParam : Parameter := {
    name := mkId "$result"
    type := { val := .TBool, source := none }
  }
  { name := mkId testerName
    inputs := [inputParam]
    outputs := [outputParam]
    preconditions := []
    decreases := none
    isFunctional := true
    body := .External }

/-- Generate external tester functions for all constructors of all datatypes in the program. -/
def generateDatatypeTesters (program : Program) : Program :=
  let testers := program.types.flatMap fun td =>
    match td with
    | .Datatype dt => dt.constructors.map (mkTesterFunction dt)
    | _ => []
  { program with staticProcedures := testers ++ program.staticProcedures }

end -- public section

end Strata.Laurel
