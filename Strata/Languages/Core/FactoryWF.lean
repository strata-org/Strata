/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF

/-! # Factory Wellformedness Proof

  This file contains the proof that the Strata Core Factory is well-formed.
-/

namespace Core

public theorem Factory_wf : Lambda.FactoryWF Factory := by simp [Factory]

end Core
