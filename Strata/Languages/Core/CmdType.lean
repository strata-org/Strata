/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Expressions
public import Strata.DL.Imperative.TypeContext
public import Strata.DL.Lambda.LExprTypeSpec

namespace Core
open Lambda Imperative LExpr
open Std (ToFormat Format format)
open Strata (DiagnosticModel FileRange)

public section

---------------------------------------------------------------------

namespace CmdType

def isBoolType (ty : LTy) : Bool :=
  match ty with
  | .forAll [] LMonoTy.bool => true
  | _ => false

def lookup (Env : TEnv Unit) (x : CoreIdent) : Option LTy :=
  Env.context.types.find? x

def update (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) : TEnv Unit :=
  Env.addInNewestContext (T := CoreLParams) [(x, ty)]

def freeVars (e : (LExpr CoreLParams.mono)) : List CoreIdent :=
  (LExpr.freeVars e).map (fun (i, _) => i)

/--
Preprocess a user-facing type in Core amounts to converting a poly-type (i.e.,
`LTy`) to a mono-type (i.e., `LMonoTy`) via instantiation. We still return an
`LTy`, with no bound variables.
-/
def preprocess (C: LContext CoreLParams) (Env : TEnv Unit) (ty : LTy) :
    Except DiagnosticModel (LTy × TEnv Unit) := do
  let (mty, Env) ← ty.instantiateWithCheck C Env |>.mapError DiagnosticModel.fromFormat
  return (.forAll [] mty, Env)

def postprocess (_: LContext CoreLParams) (Env: TEnv Unit) (ty : LTy) :
    Except DiagnosticModel (LTy × TEnv Unit) := do
  if h: ty.isMonoType then
    let ty := LMonoTy.subst Env.stateSubstInfo.subst (ty.toMonoType h)
    .ok (.forAll [] ty, Env)
  else
    .error <| DiagnosticModel.fromFormat f!"[postprocess] Expected mono-type; instead got {ty}"

/--
The inferred type of `e` will be an `LMonoTy`, but we return an `LTy` with no
bound variables.
-/
def inferType (C: LContext CoreLParams) (Env: TEnv Unit) (c : Cmd Expression) (e : LExpr CoreLParams.mono) :
    Except DiagnosticModel ((LExpr CoreLParams.mono) × LTy × TEnv Unit) := do
  let _ ← Env.freeVarCheck e f!"[{c}]" |>.mapError DiagnosticModel.fromFormat
  let T := Env
  let (ea, T) ← LExpr.resolve C T e |>.mapError DiagnosticModel.fromFormat
  let ety := ea.toLMonoTy
  return (ea.unresolved, (.forAll [] ety), T)

/--
Type constraints come from functions `inferType` and `preprocess`, both of which
are expected to return `LTy`s with no bound variables which can be safely
converted to `LMonoTy`s.
-/
def canonicalizeConstraints (constraints : List (LTy × LTy)) :
    Except DiagnosticModel Constraints := do
  match constraints with
  | [] => .ok []
  | (t1, t2) :: c_rest =>
    if h: t1.isMonoType && t2.isMonoType then
      let t1 := t1.toMonoType (by simp_all)
      let t2 := t2.toMonoType (by simp at h; simp_all only)
      let c_rest ← canonicalizeConstraints c_rest
      .ok ((t1, t2) :: c_rest)
    else
      .error <| DiagnosticModel.fromFormat f!"[canonicalizeConstraints] Expected to see only mono-types in \
                type constraints, but found the following instead:\n\
                t1: {t1}\nt2: {t2}\n"

def unifyTypes (Env: TEnv Unit) (constraints : List (LTy × LTy)) :
    Except DiagnosticModel (TEnv Unit) := do
  let constraints ← canonicalizeConstraints constraints
  let S ← Constraints.unify constraints Env.stateSubstInfo |> .mapError (fun f => DiagnosticModel.fromFormat (format f))
  let Env := Env.updateSubst S
  return Env

def typeErrorFmt (e : DiagnosticModel) : Format :=
  e.format none

---------------------------------------------------------------------

instance : Imperative.TypeContext Expression (LContext CoreLParams) (TEnv Unit) DiagnosticModel where
  isBoolType   := CmdType.isBoolType
  freeVars     := CmdType.freeVars
  preprocess   := CmdType.preprocess
  postprocess  := CmdType.postprocess
  update       := CmdType.update
  lookup       := CmdType.lookup
  inferType    := CmdType.inferType
  unifyTypes   := CmdType.unifyTypes
  typeErrorFmt := CmdType.typeErrorFmt

/-! ### Soundness helper lemmas -/

/-- `CmdType.freeVars` agrees with `HasVarsPure.getVars` on membership. -/
theorem freeVars_eq_getVars (e : LExpr CoreLParams.mono) (x : CoreIdent) :
    x ∈ CmdType.freeVars e ↔ x ∈ HasVarsPure.getVars (P := Expression) e := by
  simp only [CmdType.freeVars, HasVarsPure.getVars, Imperative.HasVarsPure.getVars]
  have h_eq : (LExpr.freeVars e).map (fun (i, _) => i) = LExpr.getVars e :=
    LExpr.freeVars_map_fst_eq_getVars e
  rw [h_eq]

/-- `CmdType.lookup` returning `none` is equivalent to `find?` on the context. -/
theorem lookup_none_iff_find_none (Env : TEnv Unit) (x : CoreIdent) :
    CmdType.lookup Env x = none ↔ Env.context.types.find? x = none := by
  simp [CmdType.lookup]

/-- `CmdType.lookup` returning `some ty` is equivalent to `find?` on the context. -/
theorem lookup_some_iff_find_some (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    CmdType.lookup Env x = some ty ↔ Env.context.types.find? x = some ty := by
  simp [CmdType.lookup]

/-- `isBoolType` returning `true` implies the type is `forAll [] .bool`. -/
theorem isBoolType_eq (ty : LTy) :
    CmdType.isBoolType ty = true → ty = .forAll [] .bool := by
  unfold CmdType.isBoolType LMonoTy.bool
  intro h
  split at h <;> simp_all

/-- `CmdType.update` does not change the substitution state. -/
theorem update_preserves_subst (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) :
    (CmdType.update Env x ty).stateSubstInfo = Env.stateSubstInfo := by
  simp [CmdType.update]
  exact TEnv.addInNewestContext_stateSubstInfo (T := CoreLParams) Env [(x, ty)]

/-- Substitution on the output context of `update` inserts the substituted type. -/
theorem update_subst_context (Env : TEnv Unit) (x : CoreIdent) (ty : LTy) (S : Subst)
    (h_fresh : Env.context.types.find? x = none) :
    TContext.subst (CmdType.update Env x ty).context S =
      { TContext.subst Env.context S with
        types := (TContext.subst Env.context S).types.insert x (LTy.subst S ty) } := by
  simp [CmdType.update]
  exact TEnv.addInNewestContext_singleton_subst_context (T := CoreLParams) Env x ty S h_fresh

/-- `preprocess` always produces a monomorphic type (`forAll [] mty`). -/
theorem preprocess_mono (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    ∃ mty, ty' = .forAll [] mty := by
  simp [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq, Prod.mk.injEq, pure, Except.pure] at h
    exact ⟨_, h.1.symm⟩

/-- `postprocess` on a mono type applies the current substitution and preserves the environment. -/
theorem postprocess_result (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (mty : LMonoTy) (ty' : LTy)
    (h : CmdType.postprocess C Env (.forAll [] mty) = .ok (ty', Env')) :
    ty' = .forAll [] (LMonoTy.subst Env.stateSubstInfo.subst mty) ∧
    Env' = Env := by
  simp only [CmdType.postprocess, LTy.isMonoType, LTy.toMonoType] at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  · simp at h

/-- After unification, both sides of a mono constraint are equal under the result substitution. -/
theorem unifyTypes_eq (Env Env' : TEnv Unit)
    (xmty emty : LMonoTy)
    (h : CmdType.unifyTypes Env [(.forAll [] xmty, .forAll [] emty)] = .ok Env') :
    LMonoTy.subst Env'.stateSubstInfo.subst xmty =
      LMonoTy.subst Env'.stateSubstInfo.subst emty := by
  simp [CmdType.unifyTypes, CmdType.canonicalizeConstraints, LTy.isMonoType, LTy.boundVars,
    LTy.toMonoType, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i S hS
    simp only [Except.ok.injEq] at h
    subst h
    split at hS <;> try contradiction
    rename_i h_unify
    cases hS
    simp [TEnv.updateSubst]
    exact Constraints.unify_sound [(xmty, emty)] Env.stateSubstInfo S h_unify (xmty, emty) (.head _)

/-- `unifyTypes` does not change the context. -/
theorem unifyTypes_preserves_context (Env Env' : TEnv Unit)
    (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Env'.context = Env.context := by
  simp [CmdType.unifyTypes, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i cs hcs
    split at h
    · simp at h
    · rename_i S hS
      simp only [Except.ok.injEq] at h
      subst h
      simp [TEnv.updateSubst, TEnv.context]

/-- The result substitution of `unifyTypes` absorbs the input substitution. -/
theorem unifyTypes_absorbs (Env Env' : TEnv Unit)
    (constraints : List (LTy × LTy))
    (h : CmdType.unifyTypes Env constraints = .ok Env') :
    Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst := by
  simp [CmdType.unifyTypes, Bind.bind, Except.bind, Except.mapError, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i cs hcs
    split at h
    · simp at h
    · rename_i S hS
      simp only [Except.ok.injEq] at h
      subst h
      simp [TEnv.updateSubst]
      have hS' : Constraints.unify cs Env.stateSubstInfo = .ok S := by
        revert hS; cases Constraints.unify cs Env.stateSubstInfo <;> simp
      exact Constraints.unify_absorbs cs Env.stateSubstInfo S hS'

/--
Decomposition of `inferType` success: if `inferType` returns `.ok`, then
`LExpr.resolve` succeeded on the same `Env` and `e`, and the outputs relate as expected.
-/
theorem inferType_decompose (C : LContext CoreLParams) (Env : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (Env' : TEnv Unit)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    ∃ ea : LExprT CoreLParams.mono,
      LExpr.resolve C Env e = .ok (ea, Env') ∧
      e' = ea.unresolved ∧
      ety = .forAll [] ea.toLMonoTy := by
  simp only [CmdType.inferType, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i v h_resolve
      obtain ⟨ea, Env_r⟩ := v
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨h_e', h_ety, h_env'⟩ := h
      subst h_e' h_ety h_env'
      have h_res : LExpr.resolve C Env e = .ok (ea, Env_r) := by
        revert h_resolve
        cases h_r : LExpr.resolve C Env e <;> simp
      exact ⟨ea, h_res, rfl, rfl⟩

/--
`inferType` success implies all free vars of `e` are in `Env.context.knownVars`.
-/
theorem inferType_fvars_in_knownVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy) (Env' : TEnv Unit)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env')) :
    ∀ x ∈ LExpr.freeVars e, x.1 ∈ TContext.knownVars Env.context := by
  simp only [CmdType.inferType, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · rename_i h_fvc
    have h_fvc_ok : Env.freeVarCheck e (Std.format "[" ++ Std.format c ++ Std.format "]") = .ok () := by
      revert h_fvc
      cases h_r : Env.freeVarCheck e (Std.format "[" ++ Std.format c ++ Std.format "]") with
      | error => simp
      | ok v => simp
    exact TEnv.freeVarCheck_implies_fvars_in_knownVars Env e _ h_fvc_ok

/-- `preprocess` does not change the context. -/
theorem preprocess_preserves_context (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env')) :
    Env'.context = Env.context := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · rename_i v h_iwc
    obtain ⟨mty, Env1⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h2⟩ := h; subst h2
    have h_iwc' : LTy.instantiateWithCheck ty C Env = .ok (mty, Env1) := by
      revert h_iwc; cases LTy.instantiateWithCheck ty C Env <;> simp
    exact LTy_instantiateWithCheck_context' ty C Env mty Env1 h_iwc'

/-- `preprocess` preserves well-formedness of the type environment. -/
theorem preprocess_preserves_TEnvWF (C : LContext CoreLParams) (Env : TEnv Unit)
    (ty : LTy) (ty' : LTy) (Env' : TEnv Unit)
    (h : CmdType.preprocess C Env ty = .ok (ty', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    TEnvWF (T := CoreLParams) Env' := by
  simp only [CmdType.preprocess, Bind.bind, Except.bind, Except.mapError] at h
  split at h
  · simp at h
  · rename_i v h_iwc
    obtain ⟨mty, Env1⟩ := v
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, h2⟩ := h; subst h2
    have h_iwc' : LTy.instantiateWithCheck ty C Env = .ok (mty, Env1) := by
      revert h_iwc; cases LTy.instantiateWithCheck ty C Env <;> simp
    exact LTy_instantiateWithCheck_TEnvWF ty C Env mty Env1 h_iwc' h_wf

/-- `inferType` does not change the context. -/
theorem inferType_preserves_context (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_ne : Env.context.types ≠ [])
    (h_fwf : FactoryWF C.functions) :
    Env'.context = Env.context := by
  obtain ⟨ea, h_resolve, _, _⟩ := inferType_decompose C Env c e e' ety Env' h
  have h_ws : WellScoped e Env.context := inferType_fvars_in_knownVars C Env c e e' ety Env' h
  exact resolve_preserves_context e ea C Env Env' h_resolve h_wf h_ne h_fwf

/--
`inferType` success implies `HasType` holds universally over absorbing substitutions.
-/
theorem inferType_HasType (C : LContext CoreLParams) (Env Env' : TEnv Unit)
    (c : Cmd Expression) (e e' : LExpr CoreLParams.mono) (ety : LTy)
    (h : CmdType.inferType C Env c e = .ok (e', ety, Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions) :
    ∃ mty, ety = .forAll [] mty ∧
      (∀ S, Subst.absorbs S Env'.stateSubstInfo.subst → SubstWF S →
        Subst.polyKeysFresh (T := CoreLParams) S Env.context →
        HasType (T := CoreLParams) C (TContext.subst Env.context S) e
          (.forAll [] (LMonoTy.subst S mty))) := by
  obtain ⟨ea, h_resolve, _, h_ety⟩ := inferType_decompose C Env c e e' ety Env' h
  have h_ws : WellScoped e Env.context := inferType_fvars_in_knownVars C Env c e e' ety Env' h
  have ⟨h_ht, _, _⟩ := resolve_HasType_core e ea C Env Env' h_resolve h_wf h_fwf h_ws
  exact ⟨ea.toLMonoTy, h_ety, h_ht⟩

end CmdType
---------------------------------------------------------------------

end
end Core
