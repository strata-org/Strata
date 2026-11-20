/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.RecFuncBlockType
import Strata.Util.Tactics
import Strata.Util.ExceptProps
import all Strata.Languages.Core.RecFuncBlockType

/-! # Inversion of the recursive function block checker
`RecFuncBlock.typeCheckIn_decompose` splits a successful block check into its per-member
signature and body checks. -/

public section

namespace Core

/-- A successful block check against the set `S` runs the signature check on each member, in
    order. It extends `S` with the signature type names of the stubs registered in the context
    with every stub, and checks the expressions of each checked signature against that context,
    in order, with rigid constants avoiding the extended set and the type names the member
    mentions. It returns the incoming environment and the incoming context extended with the
    checked functions. -/
theorem RecFuncBlock.typeCheckIn_decompose (S S' : Std.HashSet String)
    (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    ∃ sigs : List CheckedSignature,
      List.Rel₂ (fun f sig => RecFuncBlock.checkSignature C Env funcs f = .ok sig) funcs sigs
      ∧ S' = S.insertMany (Factory.tyNamesFrom C.functions.toArray.size
          (RecFuncBlock.stubContext C (sigs.map (·.stub))).functions)
      ∧ List.Rel₂ (fun sig f' => ∃ E,
          Function.checkDefinition (Thunk.pure S')
            (RecFuncBlock.stubContext C (sigs.map (·.stub))) Env sig.func sig.output sig.inputs
            sig.tyNames = .ok (f', E)) sigs funcs'
      ∧ C' = RecFuncBlock.fullContext C funcs'
      ∧ Env' = Env := by
  unfold RecFuncBlock.typeCheckIn at h
  simp only [bind, Except.bind] at h
  elim_err h
  elim_err h with sigs hsigs
  elim_err h with funcs'' hbodies
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  refine ⟨sigs, mapM_except_rel₂ _ funcs sigs hsigs, rfl, ?_, rfl, rfl⟩
  refine (mapM_except_rel₂ _ sigs _ hbodies).imp ?_
  intro sig f' hdef
  simp only [Functor.map, Except.map] at hdef
  split at hdef
  · cases hdef
  · rename_i r hr
    simp only [Except.ok.injEq] at hdef
    subst hdef
    exact ⟨r.2, hr⟩

end Core

end -- public section
