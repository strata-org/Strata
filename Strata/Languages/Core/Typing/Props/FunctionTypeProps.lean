/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import Strata.Util.Tactics
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.TypeSkolem

/-! # Properties of function type checking

Key theorems: `Function.checkNameFresh_ok`, a passing freshness check means the function name is
unused, and `Function.typeCheck_inputs_nodup`, a function that type checks has distinct input
names. -/

public section

namespace Core

open Lambda Imperative

namespace Function

/-- A function-name freshness check that succeeds means the context has no function of that
    name. -/
theorem checkNameFresh_ok {C : Core.Expression.TyContext} {func : Function} {u : Unit}
    (h : checkNameFresh C func = .ok u) : func.name.name ∉ C.functions := by
  intro hmem
  simp only [checkNameFresh, hmem, ite_true] at h
  contradiction

end Function

/-- Renaming type parameters keeps the names of the inputs. -/
private theorem Function.renameReservedTypeArgs_inputs_keys (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (annot : Unit → List LMonoTy) :
    (Function.renameReservedTypeArgs C Env func annot).inputs.keys = func.inputs.keys := by
  unfold Function.renameReservedTypeArgs
  rcases renameReservedWith_cases func.typeArgs
    (fun u => func.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env)
    func.renameTypeArgs func with ⟨heq, -⟩ | heq
  · rw [heq]
  · rw [heq]
    exact Lambda.LFuncDefined.renameTypeArgs_inputs_keys _ _

/-- If `Function.typeCheck` succeeds, the function's inputs have no duplicate names. -/
theorem Function.typeCheck_inputs_nodup (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) (func' : Function) (Env' : Core.Expression.TyEnv) :
    Function.typeCheck C Env func = .ok (func', Env') → func.inputs.keys.Nodup := by
  intro h
  rw [← Function.renameReservedTypeArgs_inputs_keys C Env]
  have hsig : ∃ sig, Function.renameAndResolve C Env func = .ok sig := by
    simp only [Function.typeCheck, bind, Except.bind] at h
    elim_err h with v hIn
    simp only [Function.typeCheckIn, bind, Except.bind] at hIn
    elim_err hIn
    elim_err hIn with sig hsig
    exact ⟨sig, hsig⟩
  obtain ⟨sig, hsig⟩ := hsig
  unfold Function.renameAndResolve Function.resolveSignature at hsig
  simp only [bind, Except.bind, Thunk.get] at hsig
  by_cases hnd : (Function.renameReservedTypeArgs C Env func
      (fun _ => func.annotTys)).inputs.keys.Nodup
  · exact hnd
  · exfalso
    simp only [hnd, decide_false, Bool.not_false, ite_true, reduceCtorEq] at hsig

end Core

end -- public section
