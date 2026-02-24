/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Factory
import Strata.DL.Lambda.Factory
import Strata.DL.Util.Func
import Strata.DL.Lambda.IntBoolFactory

/-! # Factory Wellformedness Proof

  This file contains the proof that the Strata Core Factory is well-formed.
-/

namespace Core
open Lambda

set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
/--
Wellformedness of Factory
-/
theorem Factory_wf :
    FactoryWF Factory := by
  unfold Factory
  apply FactoryWF.mk
  · decide -- FactoryWF.name_nodup
  · unfold HAppend.hAppend Array.instHAppendList
    simp only []
    unfold Array.appendList
    simp only [List.foldl, Array.push, List.concat]
    intros lf
    rw [← Array.mem_toList_iff]
    simp only []
    intros Hmem
    repeat (
      rcases Hmem with _ | ⟨ a', Hmem ⟩
      · rw [LFuncWF]
        apply Strata.DL.Util.FuncWF.mk
        · decide -- LFuncWF.arg_nodup
        · decide -- LFuncWF.body_freevars
        · -- LFuncWF.concreteEval_argmatch
          simp (config := { ground := true })
          try (
            try unfold unOpCeval
            try unfold binOpCeval
            try unfold cevalIntDiv
            try unfold cevalIntMod
            try unfold cevalIntDivT
            try unfold cevalIntModT
            try unfold bvUnaryOp
            try unfold bvBinaryOp
            try unfold bvShiftOp
            try unfold bvBinaryPred
            intros lf md args res
            repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try grind))
        · decide -- LFuncWF.body_or_concreteEval
        · decide -- LFuncWF.typeArgs_nodup
        · decide -- LFuncWF.inputs_typevars_in_typeArgs
        · decide -- LFuncWF.output_typevars_in_typeArgs
    )
    contradiction

end Core
