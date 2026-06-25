/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Cli

/-- `pyAnalyzeV2` is the V2 pipeline: Resolution → Translation → Elaboration → Core.
    Implementation: alias of `pyAnalyzeLaurel --v2`. -/
public def main (args : List String) : IO Unit :=
  runCommand StrataPython.Cli.pyAnalyzeLaurelCommand ("--v2" :: args)
