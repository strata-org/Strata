/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeDecl
import all Strata.Languages.Core.TypeDecl
import all Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Util.ListUtilsProps

/-! # Inversion of the Core type declaration checkers
What a successful `TypeConstructor.typeCheck` establishes:
`TypeConstructor.typeCheck_decompose`. -/

namespace Core
public section

open Std (ToFormat Format format)
open Lambda
open Strata (Message)

/-- An opaque type declaration the checker accepted has a name its site does not forbid and,
    inside a body, no synonym binds, and registering it at its arity, with any diagnostic,
    yields the returned context. -/
theorem TypeConstructor.typeCheck_decompose (tc : TypeConstructor) (site : TypeConstructor.Site)
    (C C' : Expression.TyContext) (Env : Expression.TyEnv)
    (h : TypeConstructor.typeCheck tc site C Env = .ok C') :
    (∀ n ∈ site.programNames, n.name ≠ tc.name)
      ∧ (site.isBodyLocal = true → ∀ al ∈ Env.context.aliases, al.name ≠ tc.name)
      ∧ ∀ msg, C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } msg
          = .ok C' := by
  unfold TypeConstructor.typeCheck at h
  simp only [bind, Except.bind] at h
  have hpname : ¬ ((site.programNames.any fun n => n.name == tc.name) = true) := by
    intro hcollide
    rw [ite_eq_left hcollide] at h
    exact absurd h (by simp)
  rw [ite_eq_right hpname] at h
  have hprog : ∀ n ∈ site.programNames, n.name ≠ tc.name :=
    List.names_ne_of_not_any hpname
  have haliasAny : ¬ ((site.isBodyLocal && Env.context.aliases.any fun al => al.name == tc.name)
      = true) := by
    intro hcollide
    rw [ite_eq_left hcollide] at h
    exact absurd h (by simp)
  rw [ite_eq_right haliasAny] at h
  have halias : site.isBodyLocal = true → ∀ al ∈ Env.context.aliases, al.name ≠ tc.name := by
    intro hlocal
    rw [hlocal, Bool.true_and] at haliasAny
    exact List.names_ne_of_not_any haliasAny
  refine ⟨hprog, halias, ?_⟩
  · intro msg
    exact Lambda.addKnownTypeWithError_message_irrel (g := msg) (h := h)

end -- public section
end Core
