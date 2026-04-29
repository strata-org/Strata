/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

-- Aggregator: re-exports GOTO submodules
public import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO -- shake: keep
public import Strata.Backends.CBMC.GOTO.CoreToGOTOPipeline -- shake: keep
public import Strata.Backends.CBMC.GOTO.LambdaToCProverGOTO -- shake: keep
