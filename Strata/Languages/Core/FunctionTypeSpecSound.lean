/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Languages.Core.FunctionTypeSpec
import all Strata.Languages.Core.FunctionType
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprResolveProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Util.Nodup

/-! ## Soundness of the Function Typechecker (clean reconstruction)

Relates the executable `Function.typeCheck` to the declarative typing
specifications `FuncHasTypeA` (annotated / monomorphic) and `FuncHasType`
(polymorphic).  The two top-level deliverables live here; all supporting
lemmas are (re)built below as the plan is executed. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-- **Deliverable A — annotated soundness.**
    If `Function.typeCheck` succeeds, the resulting `func'` satisfies the
    annotated declarative spec for every ambient context `Γ`. -/
theorem Function.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ Γ, FuncHasTypeA C Γ func' := by
  sorry

/-- **Deliverable B — polymorphic soundness.**
    If `Function.typeCheck` succeeds, the *original* `func` satisfies the
    polymorphic declarative spec in the ambient context `Env.context`. -/
theorem Function.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars)
    (h_ambient_mono : ∀ x ty, Env.context.types.find? x = some ty →
      LTy.boundVars ty = [])
    (h_ws_measure : ∀ m, func.measure = some m → WellScoped m Env.context) :
    FuncHasType C Env.context func := by
  sorry

end TypeSpec
end Core
