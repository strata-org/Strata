/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Linter.FlexibleLinter

/-!
# `Strata.Init`

Every leaf module in the `Strata` library transitively `public import`s this module (enforced by
`Scripts/CheckImports.lean`), which is how linters (i.e. `Strata.Linter.FlexibleLinter`) become
active across the whole package.

Because the import is `public`, every `Strata` module re-exports `Strata.Linter.FlexibleLinter`
and, through it, the linter's `public meta import`s (`Lean.Elab.Tactic.Simp`,
`Lean.Server.InfoUtils`, the elaborator machinery, ...). Two consequences follow, and they are
accepted deliberately:

* **Whole-project rebuild on linter edits.** Any change to `FlexibleLinter.lean` (or anything it
  imports) invalidates this module, and therefore every module in the package, so the whole
  library recompiles.
* **Elaborator pulled into utility modules.** A module that otherwise only needs the core library
  now also depends on the tactic elaborator via this import.
-/
