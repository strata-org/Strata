/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import StrataPython.Cli

public def main (args : List String) : IO Unit :=
  runCommand StrataPython.Cli.pyAnalyzeToGotoCommand args
