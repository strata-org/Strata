/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.SourceRange

/-! # Diagnostic interface for the PySpec parser

`PySpecMClass` abstracts the error/warning reporting capability shared by the
PySpec parsing monads. It lives in its own low-level module (rather than in
`Specs.lean`) so that focused recognizers such as the native decorator surface
(`Specs/Decorators.lean`) can be written generically over `[PySpecMClass m]`
without importing — and creating an import cycle with — the full spec pipeline.

The concrete instances for `PySpecM` and `SpecAssertionM` are defined in
`Specs.lean`, alongside the state types they manipulate. -/

namespace StrataPython.Specs

open StrataDDM (SourceRange)

/-- Type class for monads that support PySpec error and warning reporting. -/
public class PySpecMClass (m : Type → Type) where
  /-- Report an error at a specific source location. -/
  specError (loc : SourceRange) (message : String) : m Unit
  /-- Report a warning at a specific source location. -/
  specWarning (loc : SourceRange) (message : String) : m Unit
  /-- Run an action and check if any new errors were reported. -/
  runChecked {α} (act : m α) : m (Bool × α)
  /-- Run an action and return `true` if no new errors or warnings were reported. -/
  runNoWarn {α} (act : m α) : m (Bool × α)

end StrataPython.Specs
