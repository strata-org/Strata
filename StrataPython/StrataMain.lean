/-
  Copyright Strata Contributors
  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
-- Minimal strata entrypoint for the incremental hybrid branch.
-- Supports `pyAnalyzeV2` by routing to `pyAnalyzeLaurel --v2`.
import StrataPython.Cli

def main (args : List String) : IO Unit := do
  match args with
  | "pyAnalyzeV2" :: rest =>
    -- Route pyAnalyzeV2 to pyAnalyzeLaurel with --v2 flag
    runCommand StrataPython.Cli.pyAnalyzeLaurelCommand ("--v2" :: rest)
  | _ =>
    IO.println s!"strata: unknown command '{args.headD ""}'"
    IO.Process.exit 1
