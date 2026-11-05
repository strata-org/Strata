/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataLaurel.Implementation.Cli
import StrataCortex.Implementation.Cli

def frontends : List Strata.Cli.CliFrontend := [StrataLaurel.Cli.laurelFrontend, Cortex.Cli.cortexFrontend]

def main (args : List String) : IO Unit :=
  runCommandMap (Strata.Cli.buildCommandMap [] {} frontends) (Strata.Cli.buildCommandGroups [] {} frontends) args
    (progName := "strataLaurel")
