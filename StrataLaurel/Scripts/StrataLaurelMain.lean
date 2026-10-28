/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Implementation.Cli

def main (args : List String) : IO Unit :=
  runCommandMap StrataLaurel.Cli.commandMap StrataLaurel.Cli.commandGroups args
    (progName := "strataLaurel")
