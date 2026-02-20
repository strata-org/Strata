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

theorem array_list_happend_toArray:
  ∀ {α:Type} (a:Array α) (b:List α), a ++ b = (a.toList ++ b).toArray
  := by
  unfold HAppend.hAppend Array.instHAppendList Array.appendList
  grind

set_option maxRecDepth 1024 in
set_option maxHeartbeats 400000 in
/--
Wellformedness of Factory
-/
theorem Factory_wf :
    FactoryWF Factory := by
  unfold Factory
  simp only [array_list_happend_toArray, List.cons_append, List.nil_append]
  apply FactoryWF.mk
  · decide -- FactoryWF.name_nodup
  · intros f Hmem
    -- 176 is the number of functions in Factory (#eval Factory.size)
    iterate 176 (any_goals (rcases Hmem with _ | ⟨ a', Hmem ⟩ <;> try contradiction))
    all_goals (
      rw [LFuncWF]
      apply Strata.DL.Util.FuncWF.mk
      · decide -- LFuncWF.arg_nodup
      · decide -- LFuncWF.body_freevars
      · -- LFuncWF.concreteEval_argmatch
        intros lf md args res
        -- Reduce '<func name>.concreteEval'
        conv => lhs; simp (config := { ground := true })
        -- Reduce 'List.length <func name>.inputs'
        conv => rhs; rhs; rhs; whnf
        try (solve | intro h; contradiction)
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
          intro Hlf_def
          rw [← Hlf_def]
          -- Destruct the 'args' list until the goal is discharged.
          repeat (rcases args with _ | ⟨ args0, args ⟩ <;> try (
            conv => lhs; lhs; simp only []
            intros Habsurd
            contradiction))
          -- When the [arg0,arg1,..].length = n exactly matches
          intro _Hdummy; rfl)
      · decide -- LFuncWF.body_or_concreteEval
      · decide -- LFuncWF.typeArgs_nodup
      · decide -- LFuncWF.inputs_typevars_in_typeArgs
      · decide -- LFuncWF.output_typevars_in_typeArgs
    )
end Core
