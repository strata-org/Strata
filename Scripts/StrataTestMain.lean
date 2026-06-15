/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import Strata.Util.IOTests

public def main (args : List String) : IO UInt32 :=
  Strata.IOTests.testMain (testDir := "StrataTestExtra") args
