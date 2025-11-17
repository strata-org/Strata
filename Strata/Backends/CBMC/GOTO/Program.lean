/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Instruction

namespace CProverGOTO
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

/-- A GOTO program; corresponds to
  [`goto_programt`](https://diffblue.github.io/cbmc/classgoto__programt.html) -/
structure Program where
  name : String := "main"
  parameterIdentifiers : Array String := #[]
  instructions : Array Instruction := #[]
  isInternal : Bool := false
  isBodyAvailable : Bool := true
deriving Repr
