/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Factory
import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.Semantics
import Strata.DDM.Util.Array
import Strata.DL.Util.Func
import Strata.DL.Util.List
import Strata.DL.Util.ListMap

/-!
## Well-formedness of LFunc and Factory

WF of Func is separately defined in Strata/DL/Util/Func.lean
-/

namespace Lambda

open Std (ToFormat Format format)
open Strata.DL.Util (Func FuncWF TyIdentifier)

variable {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

/-- Well-formedness properties for LFunc - abbreviation of FuncWF with Lambda-specific extractors. -/
abbrev LFuncWF {T : LExprParams} (f : LFunc T) :=
  FuncWF
    (fun id => id.name) -- getName
    (fun e => (LExpr.freeVars e).map (·.1.name)) -- getVarNames
    (fun e => e.freeVars) -- getTyFreeVars
    f

instance LFuncWF.arg_nodup_decidable {T : LExprParams} (f : LFunc T):
    Decidable (List.Nodup (f.inputs.map (·.1.name))) := by
  apply List.nodupDecidable

instance LFuncWF.body_freevars_decidable {T : LExprParams} (f : LFunc T):
    Decidable (∀ b, f.body = .some b →
      (LExpr.freeVars b).map (·.1.name) ⊆ f.inputs.map (·.1.name)) :=
  by exact f.body.decidableForallMem

-- LFuncWF.concreteEval_argmatch is not decidable.

instance LFuncWF.body_or_concreteEval_decidable {T : LExprParams} (f : LFunc T):
    Decidable (¬ (f.concreteEval.isSome ∧ f.body.isSome)) := by
  exact instDecidableNot

instance LFuncWF.typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (List.Nodup f.typeArgs) := by
  apply List.nodupDecidable

instance LFuncWF.inputs_typevars_in_typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (∀ ty, ty ∈ f.inputs.values →
      ty.freeVars ⊆ f.typeArgs) := by
  exact List.decidableBAll (fun x => x.freeVars ⊆ f.typeArgs)
    (ListMap.values f.inputs)

instance LFuncWF.output_typevars_in_typeArgs_decidable {T : LExprParams} (f : LFunc T):
    Decidable (f.output.freeVars ⊆ f.typeArgs) := by
  apply List.instDecidableRelSubsetOfDecidableEq


/--
Well-formedness properties of Factory.
-/
structure FactoryWF (fac:Factory T) where
  name_nodup:
    List.Nodup (fac.toList.map (·.name.name))
  lfuncs_wf:
    ∀ (lf:LFunc T), lf ∈ fac → LFuncWF lf


instance FactoryWF.name_nodup_decidable (fac : Factory T):
    Decidable (List.Nodup (fac.toList.map (·.name.name))) := by
  apply List.nodupDecidable

/--
If Factory.addFactoryFunc succeeds, and the input factory & LFunc were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactoryFunc_wf
  (F : @Factory T) (F_wf: FactoryWF F) (func : LFunc T) (func_wf: LFuncWF func):
  ∀ F', F.addFactoryFunc func = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactoryFunc
  unfold Factory.getFactoryLFunc
  intros F' Hmatch
  split at Hmatch <;> try grind -- Case-analysis on the match condition
  rename_i heq
  cases Hmatch -- F' is Array.push F
  apply FactoryWF.mk
  case name_nodup =>
    have Hnn := F_wf.name_nodup
    grind [Array.toList_push,List]
  case lfuncs_wf =>
    intros lf Hmem
    rw [Array.mem_push] at Hmem
    cases Hmem
    · have Hwf := F_wf.lfuncs_wf
      apply Hwf; assumption
    · grind


/--
If Factory.addFactory succeeds, and the input two factories were already
well-formed, the returned factory is also well-formed.
-/
theorem Factory.addFactory_wf
  (F : @Factory T) (F_wf: FactoryWF F) (newF : @Factory T)
  (newF_wf: FactoryWF newF):
  ∀ F', F.addFactory newF = .ok F' → FactoryWF F' :=
by
  unfold Factory.addFactory
  rw [← Array.foldlM_toList]
  generalize Hl: newF.toList = l
  induction l generalizing newF F
  · rw [Array.toList_eq_nil_iff] at Hl
    rw [List.foldlM_nil]
    unfold Pure.pure Except.instMonad Except.pure
    grind
  · rename_i lf lf_tail tail_ih
    have Hl: newF = (List.toArray [lf]) ++ (List.toArray lf_tail) := by grind
    have Htail_wf: FactoryWF (lf_tail.toArray) := by
      rw [Hl] at newF_wf
      apply FactoryWF.mk
      · have newF_wf_name_nodup := newF_wf.name_nodup
        grind
      · intro lf
        have newF_wf_lfuncs_wf := newF_wf.lfuncs_wf lf
        intro Hmem
        apply newF_wf_lfuncs_wf
        apply Array.mem_append_right
        assumption
    have Hhead_wf: LFuncWF lf := by
      rw [Hl] at newF_wf
      have Hwf := newF_wf.lfuncs_wf
      apply Hwf
      apply Array.mem_append_left
      grind
    intro F'
    simp only [List.foldlM]
    unfold bind
    unfold Except.instMonad
    simp only []
    unfold Except.bind
    intro H
    split at H
    · contradiction
    · rename_i F_interm HaddFacFun
      have HF_interm_wf: FactoryWF F_interm := by
        apply (Factory.addFactoryFunc_wf F F_wf lf) <;> assumption
      simp only [] at H
      apply tail_ih F_interm HF_interm_wf (lf_tail.toArray) <;> grind

end Lambda
