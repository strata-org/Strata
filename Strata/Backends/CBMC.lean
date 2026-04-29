/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Aggregator: re-exports CBMC backend submodules
import Strata.Backends.CBMC.CProver -- shake: keep
import Strata.Backends.CBMC.CollectSymbols -- shake: keep
import Strata.Backends.CBMC.CoreToCBMC -- shake: keep
import Strata.Backends.CBMC.GOTO -- shake: keep
import Strata.Backends.CBMC.StrataToCBMC -- shake: keep
