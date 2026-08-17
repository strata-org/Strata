/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.VerifyOptions
public import Strata.Languages.Laurel.LaurelCompilationPipeline

/-! # Laurel verify-options flag parsing

The Laurel half of the CLI verify-options parsing. The Core half lives in
`Strata.Cli.VerifyOptions`; keeping the Laurel-specific parser here means that
module carries no dependency on the Laurel layer. -/

public section

open Strata
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

/-- Build a `LaurelVerifyOptions` from parsed CLI flags. -/
def parseLaurelVerifyOptions (pflags : ParsedFlags)
    (base : LaurelVerifyOptions := default)
    (inputFile : Option String := none) : IO LaurelVerifyOptions := do
  let verifyOptions ← parseVerifyOptions pflags base.verifyOptions (inputFile := inputFile)
  let translateOptions : LaurelTranslateOptions :=
    { base.translateOptions with
      keepAllFilesPrefix := verifyOptions.keepAllFilesPrefix
      overflowChecks := verifyOptions.overflowChecks
      enumeratedModifiesClauses := verifyOptions.useArrayTheory }
  return { translateOptions, verifyOptions }

end -- public section
