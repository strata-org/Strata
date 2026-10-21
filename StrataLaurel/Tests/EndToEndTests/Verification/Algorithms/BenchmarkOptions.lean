/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataLaurel.Tests.Util.TestLaurel

namespace StrataTest.Util.Algorithms

open StrataTest.Util Strata

def benchmarkRlimit : Nat := 500000

def benchmarkOptions : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    verifyOptions := { defaultLaurelTestOptions.verifyOptions with
      solverTimeout := 300
      solverOptions := #[("rlimit-per", toString benchmarkRlimit)] } }

end StrataTest.Util.Algorithms
