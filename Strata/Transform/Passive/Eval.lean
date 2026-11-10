/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Passive.ProgramProps
public import Strata.Transform.Passive.LangProps
import Strata.Util.ExceptProps

/-! # Evaluation of renamed expressions

The evaluation of the renamed expressions `ren ρ e` (from `ev_substVars`).

Key theorems: `ev_ren`.
Key definitions: `ren`, `renMap`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident]
  [HasBool P] [HasFvar P] [HasSubstFvar P] [HasFvars P] [HasOps P] [LawfulHasFvar P]

/-- Apply the renaming to the free variables of `e` (only the renamed ones are
    substituted; each replacement is a variable, annotated from `tys`). -/
@[expose] def ren (tys : (Tys P)) (ρ : (Ren P)) (e : P.Expr) : P.Expr :=
  let sm : List (P.Ident × P.Expr) := (exprFV e).filterMap fun x =>
    let y := ρ.get x
    if y == x then none else some (x, HasFvar.mkVar y (tys.get? x))
  HasSubstFvar.substFvars e sm

/-- The substitution `ren` builds. -/
@[expose] def renMap (tys : Tys P) (ρ : Ren P) (e : P.Expr) : List (P.Ident × P.Expr) :=
  (exprFV e).filterMap fun x =>
    let y := ρ.get x
    if y == x then none else some (x, HasFvar.mkVar y (tys.get? x))

/-- **Evaluating a renamed expression** in the obligation store is evaluating the
    original in the loop-free store, when the two agree through the renaming on its free
    variables, those are defined, and the factory satisfies the factory laws
    (`WellFormedSemanticEvalBase`). -/
theorem ev_ren {F : P.Factory} (hF : WellFormedSemanticEvalBase F)
    {σ σ' : SemanticStore P} (hσ' : WellFormedStore σ' F) (hσ : WellFormedStore σ F)
    (tys : Tys P) (ρ : Ren P) (e : P.Expr)
    (hagree : ∀ x ∈ exprFV e, σ x = σ' (ρ.get x))
    (hdef : ∀ x ∈ exprFV e, (σ x).isSome) :
    P.eval F σ' (ren tys ρ e) = P.eval F σ e := by
  refine ev_substVars hF hσ' hσ (renMap tys ρ e) e (fun k v h => ?_) fun x hx h => ?_
  · obtain ⟨z, hz, hfz⟩ := Map.find?_filterMap_some _ _ _ _ h
    obtain ⟨rfl, rfl⟩ : z = k ∧ v = HasFvar.mkVar (ρ.get z) (tys.get? z) := by grind
    exact ⟨_, by cases tys.get? z <;> grind [HasFvar.mkVar], (hagree z hz).symm, hdef z hz⟩
  · have hk := Map.find?_filterMap_none _ (by grind) _ _ (mem_exprFV.2 hx) h
    simpa [show ρ.get x = x by grind] using (hagree x (mem_exprFV.2 hx)).symm

end -- public section

end WP
end Imperative
