/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Linter.FlexibleLinter
public import Strata.Linter.MaxHeartbeatsLinter

/-!
# `Strata.Init`

Every leaf module in the `Strata` library transitively `public import`s this module (enforced by
`Scripts/CheckImports.lean`), which is how the Strata linters (`Strata.Linter.*`) become active
across the whole package.

Because the import is `public`, every `Strata` module re-exports the linter modules and, through
them, their `public meta import`s (`Lean.Elab.Tactic.Simp`,
`Lean.Server.InfoUtils`, the elaborator machinery, ...). Two consequences follow, and they are
accepted deliberately:

* **Whole-project rebuild on linter edits.** Any change to a linter module (or anything it
  imports) invalidates this module, and therefore every module in the package, so the whole
  library recompiles.
* **Elaborator pulled into utility modules.** A module that otherwise only needs the core library
  now also depends on the tactic elaborator via this import.
-/
