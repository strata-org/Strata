/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.DDMTransform.Translate

/-! # Helpers of the interpreter tests on DDM programs

The interpreter tests write their procedures in Core's DDM syntax and run them after DDM
translation. `translationOk` checks that the translation reports no errors, and `procTable`
is the procedure table of the translated program, looked up by procedure name. -/

meta section

public section

namespace Strata.InterpreterTestUtils

open _root_.Core

/-- Whether the DDM translation of `program` reports no errors. -/
def translationOk (program : StrataDDM.Program) : Bool :=
  (Strata.TransM.run default (Strata.translateProgram program)).snd.isEmpty

/-- The procedure table of the DDM translation of `program`: maps a name to the procedure
    of that name, if there is one. The translation runs once per table. -/
def procTable (program : StrataDDM.Program) : String → Option Procedure :=
  let procs := (Strata.TransM.run default (Strata.translateProgram program)).fst.decls.filterMap
    fun | .proc p _ => some p | _ => none
  fun n => procs.find? (·.header.name.name == n)

end Strata.InterpreterTestUtils

end

end
