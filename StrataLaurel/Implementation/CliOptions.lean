/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Cli.VerifyOptions
public import StrataLaurel.Implementation.LaurelCompilationPipeline
public import StrataLaurel.Implementation.LaurelPipelinePrinter

/-! # Laurel verify-options flag parsing

The Laurel half of the CLI verify-options parsing. The Core half lives in
`Strata.Cli.VerifyOptions`; keeping the Laurel-specific parser here means that
module carries no dependency on the Laurel layer. -/

public section

open Strata
open Laurel (LaurelVerifyOptions LaurelTranslateOptions)

def laurelPassFlags : List Flag :=
  [{ name := "phases",
     help := "Run these Laurel phases, in this order (comma-separated). \
              Without an input file, report whether they compose.",
     takesArg := .arg "names" },
   { name := "skip-phases",
     help := "Run the default Laurel phase order without these phases (comma-separated).",
     takesArg := .arg "names" },
   { name := "display-phases", help := "Print the Laurel phases available and the default order." },
   { name := "display-phase-contracts",
     help := "Print what each Laurel phase creates, removes and does not support." }]

private def laurelPassHint : String := "Use --display-phases to see the available phases."

private def requestedLaurelPasses (pflags : ParsedFlags) : IO (Option (List String)) := do
  match pflags.getString "phases", pflags.getString "skip-phases" with
  | some _, some _ => exitUserError "--phases and --skip-phases cannot be combined."
  | some names, none => pure (some (names.splitToList (· == ',')))
  | none, some names =>
    let skipped := names.splitToList (· == ',')
    for nm in skipped do
      unless Laurel.defaultPassNames.contains nm do
        exitUserError (Laurel.unselectablePassName nm laurelPassHint)
    pure (some (Laurel.defaultPassNames.filter (!skipped.contains ·)))
  | none, none => pure none

def displayLaurelPassesText : String :=
  Strata.Pipeline.displayPhasesText
    { select := "--phases", displayContracts := "--display-phase-contracts" }
    "Laurel phases" "creates, removes and does not support" Laurel.defaultPassNames
    ++ s!"\n\nAlways run, and cannot be named: {", ".intercalate Laurel.structuralPassNames}."

def parseLaurelPasses (pflags : ParsedFlags) : IO (Option (List String)) := do
  match ← requestedLaurelPasses pflags with
  | none => pure none
  | some names =>
    match Laurel.checkPassSelection names laurelPassHint with
    | .ok _ => pure (some names)
    | .error msg => exitUserError msg

private def reportLaurelOrder (names : List String) : IO Unit := do
  match Laurel.resolvePassOrder names laurelPassHint with
  | .ok (run, requirements) =>
    IO.println s!"This order composes: {", ".intercalate run}"
    unless requirements.isEmpty do
      IO.println "\nThe input must not contain these, which is checked before running:"
      for r in requirements do
        IO.println s!"  {r.kind} (phase {r.position} '{r.pass}' does not support it)"
  | .error msg => exitUserError msg

def reportLaurelPasses (pflags : ParsedFlags) (withoutInput : Bool) : IO Bool := do
  if pflags.getBool "display-phases" then
    IO.println displayLaurelPassesText
    return true
  if pflags.getBool "display-phase-contracts" then
    match Laurel.passContractsText (← requestedLaurelPasses pflags) laurelPassHint with
    | .ok text => IO.println text
    | .error msg => exitUserError msg
    return true
  if withoutInput then
    if let some names ← requestedLaurelPasses pflags then
      reportLaurelOrder names
      return true
  return false

def laurelPassReportFlags : List (String × (ParsedFlags → IO Unit)) :=
  ["display-phases", "display-phase-contracts", "phases", "skip-phases"].map fun name =>
    (name, fun pflags => do let _ ← reportLaurelPasses pflags (withoutInput := true))

/-- Build a `LaurelVerifyOptions` from parsed CLI flags. -/
def parseLaurelVerifyOptions (pflags : ParsedFlags)
    (base : LaurelVerifyOptions := default)
    (inputFile : Option String := none) : IO LaurelVerifyOptions := do
  let verifyOptions ← parseVerifyOptions pflags base.verifyOptions (inputFile := inputFile)
  let passes ← parseLaurelPasses pflags
  let translateOptions : LaurelTranslateOptions :=
    { base.translateOptions with
      keepAllFilesPrefix := verifyOptions.keepAllFilesPrefix
      overflowChecks := verifyOptions.overflowChecks
      enumeratedModifiesClauses := verifyOptions.useArrayTheory
      passes := passes.orElse fun _ => base.translateOptions.passes }
  return { translateOptions, verifyOptions }

end -- public section
