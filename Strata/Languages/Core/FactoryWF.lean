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
import all Strata.DL.Lambda.FactoryProps
import all Strata.Languages.Core.Factory

/-! # Factory Wellformedness Proof

  This file contains the proof that the Strata Core Factory is well-formed
  (`Factory_wf`) and that none of its functions is a
  constructor producing a Boolean (`Factory_constrsNotBool`).
-/

namespace Core

public theorem Factory_wf : Lambda.FactoryWF Factory := by simp [Factory]

/-- No function of the Core factory is a constructor, so no constructor produces
a Boolean. -/
public theorem Factory_constrsNotBool : Lambda.Factory.ConstrsNotBool Factory := by
  have hall : (WFFactoryArray.toList.all fun w => !w.func.isConstr) = true := by
    simp only [WFFactoryArray, Array.toList_appendList]
    decide +kernel
  intro fn hmem hc
  obtain ⟨w, hw, rfl⟩ := Array.mem_map.mp (Lambda.Factory.ofArray_mem hmem)
  have hw' := List.all_eq_true.mp hall w (Array.mem_toList_iff.mpr hw)
  simp [hc] at hw'

end Core
