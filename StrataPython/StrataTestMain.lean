/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Util.IOTests

def main (args : List String) : IO UInt32 :=
  Strata.Util.IOTests.testMain args (defaultDir := "StrataPythonTestExtra")
