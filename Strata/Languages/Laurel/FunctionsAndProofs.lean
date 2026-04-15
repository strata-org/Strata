/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
## FunctionsAndProofs IR

An intermediate representation that separates Laurel procedures into
functions (pure, used for computation) and proofs (used for verification).

This IR sits between Laurel and CoreWithLaurelTypes in the pipeline:
  Laurel → FunctionsAndProofs → CoreWithLaurelTypes → Core
-/

namespace Strata.Laurel

public section

/--
A program in the FunctionsAndProofs IR. Functions are pure computational
procedures; proofs are verification-only procedures.
Both reuse `Laurel.Procedure` as their representation.
-/
structure FunctionsAndProofsProgram where
  functions : List Procedure
  proofs : List Procedure
  datatypes : List DatatypeDefinition
  constants : List Constant

/--
Temporary translation from Laurel to FunctionsAndProofs.
Maps functional Laurel procedures to functions and
non-functional Laurel procedures to proofs.
-/
def laurelToFunctionsAndProofs (program : Program) : FunctionsAndProofsProgram :=
  let nonExternal := program.staticProcedures.filter (fun p => !p.body.isExternal)
  let (functions, proofs) := nonExternal.partition (·.isFunctional)
  let datatypes := program.types.filterMap fun td => match td with
    | .Datatype dt => some dt
    | _ => none
  { functions, proofs, datatypes, constants := program.constants }

end -- public section
end Strata.Laurel
