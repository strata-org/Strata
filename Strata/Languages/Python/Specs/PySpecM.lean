/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.SourceRange

/-!
# PySpec Monad

This module defines the monad infrastructure for PySpec translation,
including error reporting type class and error structures.
-/

public section
namespace Strata.Python.Specs

/-- An error encountered while processing a PySpec file. -/
structure SpecError where
  file : System.FilePath
  loc : SourceRange
  message : String

/-- Type class for monads that support PySpec error reporting. -/
class PySpecMClass (m : Type → Type) where
  /-- Report an error at a specific source location. -/
  specError (loc : SourceRange) (message : String) : m Unit
  /-- Run an action and check if any new errors were reported. -/
  runChecked {α} (act : m α) : m (Bool × α)

export PySpecMClass (specError runChecked)

end Strata.Python.Specs
end
