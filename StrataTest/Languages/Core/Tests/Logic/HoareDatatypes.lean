/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.ProgramProps
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # The functions of a datatype in a procedure's visible factory

`Program.factoryBeforeProcedure` is the factory a procedure's contract triple is stated
over (`Procedure.contractTriple`) and its body runs with. It holds the constructors,
testers and destructors of the datatypes declared before the procedure, so a body or a
contract that mentions them evaluates. A datatype declared after the procedure adds
nothing to it.

## Key results

- `after_factory_has_datatype_functions`: the functions of `IntList` are in the factory
  of a procedure declared after it.
- `before_factory_eq_core`: the factory of a procedure declared before `IntList` is
  Core's own.
-/

open StrataDDM (Program)

namespace Strata.HoareDatatypesTest

open Strata.HoareUtils

private def listPgm : Program :=
#strata
program Core;

procedure Before(out r : int)
spec {
  ensures r == 0;
}
{
  r := 0;
};

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

procedure After(xs : IntList, out r : bool)
spec {
  ensures r == IntList..isNil(xs);
}
{
  r := IntList..isNil(xs);
};
#end

private def listAST : Core.Program := cstToAST listPgm

/-- The constructors, testers and destructors of `IntList`. -/
private def intListFunctions : List String :=
  ["Nil", "Cons", "IntList..isNil", "IntList..isCons", "IntList..hd", "IntList..tl"]

/-- None of them is one of Core's built-in functions. -/
private theorem intListFunctions_new :
    (intListFunctions.all fun n => (Core.Factory[n]?).isNone) = true := by
  native_decide

/-- **The functions of a datatype are visible to a procedure declared after it.** -/
theorem after_factory_has_datatype_functions :
    (intListFunctions.all fun n =>
      ((listAST.factoryBeforeProcedure "After")[n]?).isSome) = true := by
  native_decide

/-- **A datatype declared after a procedure adds nothing to its factory.** -/
theorem before_factory_eq_core :
    listAST.factoryBeforeProcedure "Before" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)

end Strata.HoareDatatypesTest
