/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Counterexample.ModelAnonymous
public import Strata.DL.Lambda.FactoryWF
import Strata.DL.Lambda.FactoryProps
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.Languages.Core.Counterexample.ModelAnonymous
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.Denote.LExprDenote

/-! # Properties of anonymous values

An anonymous value is the Core representation of a solver-invented element of an
uninterpreted sort: the operator `.op default n (some S)` together with the nullary
constructor `anonConstr n S`, which `extendAnon` adds to the factory replay evaluates
with.

Key theorems:
- `extendAnon_wf`: adding anonymous-value constructors keeps a well-formed factory
  well-formed.
- `eql_anon`: the evaluator's equality `LExpr.eql` decides two anonymous values of the
  same sort by identity of their names.
- `eql_anon_denote`: that decision agrees with the denotation under any interpretation
  that gives anonymous values with different names different elements.
-/

namespace Core

open Lambda

public section

/-- The anonymous-value constructor `anonConstr n ty` is a well-formed `LFunc` when its
    sort `ty` is closed (has no free type variables). -/
private theorem anonConstr_wf (n : String) (ty : LMonoTy) (h : LMonoTy.freeVars ty = []) :
    LFuncWF (anonConstr n ty) := by repeat constructor <;> simp! [anonConstr, h]

/-- A function in `pushAnon F x` is either already in `F`, or is the constructor for
    `x` and `x`'s sort is closed. -/
private theorem mem_pushAnon {F : @Lambda.Factory CoreLParams} {x : String × LMonoTy}
    {g : LFunc CoreLParams} (p : g ∈ (pushAnon F x).toArray) :
    g ∈ F.toArray ∨ (g = anonConstr x.1 x.2 ∧ LMonoTy.freeVars x.2 = []) := by
  grind [pushAnon, Factory.mem_pushIfNew]

/-- A function in `F` extended by folding `pushAnon` over `xs` is either already in `F`,
    or is the constructor of some `x ∈ xs` whose sort is closed. -/
private theorem foldl_pushAnon_mem (xs : List (String × LMonoTy)) :
    ∀ (F : @Lambda.Factory CoreLParams) (g : LFunc CoreLParams),
      g ∈ (xs.foldl pushAnon F).toArray →
        g ∈ F.toArray ∨ ∃ x ∈ xs, g = anonConstr x.1 x.2 ∧ LMonoTy.freeVars x.2 = [] :=
  match xs with
  | [] => fun _ _ => .inl
  | _ :: xs => fun _ _ hmem => by grind [foldl_pushAnon_mem xs _ _ hmem, mem_pushAnon]

/-- Extending a well-formed factory with anonymous values keeps it well-formed. -/
theorem extendAnon_wf {F : @Lambda.Factory CoreLParams} (h : FactoryWF F)
    (vals : List (LExpr CoreLParams.mono)) : FactoryWF (extendAnon F vals) :=
  ⟨by grind [foldl_pushAnon_mem, anonConstr_wf, h.lfuncs_wf, extendAnon]⟩

/-- The evaluator's equality decides two anonymous values by identity: the same name
    is equal, two different names are distinct. -/
theorem eql_anon {F : @Lambda.Factory CoreLParams} {n₁ n₂ : String} {ty : LMonoTy}
    (h₁ : F[n₁]? = some (anonConstr n₁ ty)) (h₂ : F[n₂]? = some (anonConstr n₂ ty))
    (m₁ m₂ : CoreExprMetadata) :
    LExpr.eql F (LExpr.op (T := CoreLParams.mono) m₁ (⟨n₁, ()⟩ : CoreIdent) (some ty))
        (LExpr.op (T := CoreLParams.mono) m₂ (⟨n₂, ()⟩ : CoreIdent) (some ty)) =
      some (n₁ == n₂) := by open LExpr in
  simp only [eql, eqModuloMeta, BEq.beq, eraseMetadata, replaceMetadata, Factory.callOfLFunc,
    getLFuncCall, getLFuncCall.go, Bool.false_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    bne_iff_ne]
  grind [anonConstr]

/-- The evaluator's identity decision on two anonymous values of the same sort agrees
    with the denotation, under any interpretation of the operators that gives two
    anonymous values with different names different elements: equal by `eql` means equal
    denotations, distinct by `eql` means distinct denotations. -/
theorem eql_anon_denote {F : @Lambda.Factory CoreLParams} {n₁ n₂ : String} {ty τ : LMonoTy}
    (h₁ : F[n₁]? = some (anonConstr n₁ ty)) (h₂ : F[n₂]? = some (anonConstr n₂ ty))
    (m₁ m₂ : CoreExprMetadata)
    {tcInterp : TyConstrInterp} (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal CoreLParams tcInterp) (vt : TyVarVal)
    (hτ₁ : LExpr.HasTypeA []
      (LExpr.op (T := CoreLParams.mono) m₁ (⟨n₁, ()⟩ : CoreIdent) (some ty)) τ)
    (hτ₂ : LExpr.HasTypeA []
      (LExpr.op (T := CoreLParams.mono) m₂ (⟨n₂, ()⟩ : CoreIdent) (some ty)) τ)
    (hinj : n₁ ≠ n₂ → opInterp n₁ (ty.substTyVars vt) ≠ opInterp n₂ (ty.substTyVars vt)) :
    (LExpr.eql F (LExpr.op (T := CoreLParams.mono) m₁ (⟨n₁, ()⟩ : CoreIdent) (some ty))
        (LExpr.op (T := CoreLParams.mono) m₂ (⟨n₂, ()⟩ : CoreIdent) (some ty)) = some true →
      LExpr.denote tcInterp opInterp fvarVal vt .nil _ τ hτ₁ =
        LExpr.denote tcInterp opInterp fvarVal vt .nil _ τ hτ₂) ∧
    (LExpr.eql F (LExpr.op (T := CoreLParams.mono) m₁ (⟨n₁, ()⟩ : CoreIdent) (some ty))
        (LExpr.op (T := CoreLParams.mono) m₂ (⟨n₂, ()⟩ : CoreIdent) (some ty)) = some false →
      LExpr.denote tcInterp opInterp fvarVal vt .nil _ τ hτ₁ ≠
        LExpr.denote tcInterp opInterp fvarVal vt .nil _ τ hτ₂) := by
  grind [eql_anon, denote_op]

end -- public section

end Core
