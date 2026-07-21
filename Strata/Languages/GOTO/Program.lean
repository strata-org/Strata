/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.GOTO.Instruction

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

public section

/-- A GOTO program; corresponds to
  [`goto_programt`](https://diffblue.github.io/cbmc/classgoto__programt.html) -/
structure Program where
  name : String := "main"
  parameterIdentifiers : Array String := #[]
  instructions : Array Instruction := #[]
  isInternal : Bool := false
  isBodyAvailable : Bool := true
deriving Repr

/--
GOTO programs name symbols in the namespace of the program.
So, e.g., a formal `x` of program `p` appears as `p::x`.
-/
def mkFormalSymbol (pname base : String) : String :=
  pname ++ "::" ++ base

/--
Local variables use `program::<depth>::<var>` notation.
(FIXME): Does `depth` refer to the scope level?
-/
def mkLocalSymbol (pname base : String) (depth : Nat := 1) : String :=
  pname ++ "::" ++ toString depth ++ "::" ++ base

end -- public section
