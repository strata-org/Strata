/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.Factory
import Strata.DL.Util.Func
public import Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryWF

/-! # Factory Wellformedness Proof

  This file contains the proof that the Strata Core Factory is well-formed.
-/

namespace Core
open Lambda

public section

theorem Factory_wf :
    FactoryWF Factory := by
  constructor
  · -- name_nodup: follows from WFFactory.name_nodup
    simp only [Factory, WFLFactory.toFactory, Array.toList_map, List.map_map]
    exact WFFactory.name_nodup
  · intro lf hlf
    simp only [Factory, WFLFactory.toFactory] at hlf
    rw [Array.mem_map] at hlf
    obtain ⟨wflf, _, rfl⟩ := hlf
    exact wflf.wf
end
end Core
