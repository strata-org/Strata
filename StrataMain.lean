/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataMainLib

def main (args : List String) : IO Unit :=
  runCommandMap commandMap commandGroups args
