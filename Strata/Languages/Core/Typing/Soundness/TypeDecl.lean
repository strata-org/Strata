/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeDecl
import all Strata.Languages.Core.TypeDecl
import all Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.LTyWFCheckSound
import Strata.Util.ListUtilsProps

/-! # Inversion of the Core type declaration checkers
What a successful `TypeSynonym.typeCheck` or `TypeConstructor.typeCheck` establishes:
`TypeSynonym.typeCheck_decompose` and `TypeConstructor.typeCheck_decompose`. -/

namespace Core
public section

open Std (ToFormat Format format)
open Lambda
open Strata (Message)

/-- For a type synonym the checker accepted, adding it as an alias yields the returned
    environment, and the returned synonym carries the body of the newest alias. -/
theorem TypeSynonym.typeCheck_decompose (ts ts' : TypeSynonym) (C : Expression.TyContext)
    (Env Env' : Expression.TyEnv) (h : TypeSynonym.typeCheck ts C Env = .ok (ts', Env')) :
    Lambda.TEnv.addTypeAlias { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C Env
        = .ok Env'
      ∧ ts' = ts.withStoredBody Env'.context.aliases := by
  unfold TypeSynonym.typeCheck at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with Env'' hadd
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨hadd, rfl⟩

/-- A synonym the checker accepted in a context that differs from the declarative one only in its
    identifier table has a valid source body, with every type variable admissible, and is returned
    with its stored body. -/
theorem TypeSynonym.typeCheck_sourceTyWF_withIdents (ts ts' : TypeSynonym)
    (C : Expression.TyContext) (idents : Identifiers Unit) (Env Env' : Expression.TyEnv)
    (h : TypeSynonym.typeCheck ts { C with idents := idents } Env = .ok (ts', Env')) :
    ∃ storedTy,
      SourceTyWF C TyVarAdmissibility.all Env.context.aliases ts.type storedTy
      ∧ Env'.context.aliases
          = { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
              :: Env.context.aliases
      ∧ ts' = { ts with type := storedTy } := by
  obtain ⟨hadd, hts'⟩ :=
    TypeSynonym.typeCheck_decompose ts ts' { C with idents := idents } Env Env' h
  obtain ⟨-, storedTy, hsrc, haliases⟩ :=
    TEnv.addTypeAlias_sourceTyWF
      { typeArgs := ts.typeArgs, name := ts.name, type := ts.type }
      { C with idents := idents } Env Env' hadd
  rw [haliases] at hts'
  exact ⟨storedTy, SourceTyWF.of_knownTypes_eq (C := { C with idents := idents }) rfl hsrc,
    haliases, hts'⟩

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

/-- An accepted opaque type declaration leaves the function table unchanged. -/
theorem TypeConstructor.typeCheck_functions_eq {tc : TypeConstructor} {site : TypeConstructor.Site}
    {C C' : Expression.TyContext} {Env : Expression.TyEnv}
    (h : TypeConstructor.typeCheck tc site C Env = .ok C') : C'.functions = C.functions :=
  addKnownTypeWithError_functions_eq C C' _ _
    ((TypeConstructor.typeCheck_decompose tc site C C' Env h).2.2 default)

end -- public section
end Core
