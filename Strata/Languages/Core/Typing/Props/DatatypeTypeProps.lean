/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.FactoryProps
public import Strata.Util.Tactics
public import Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.TypeDecl
import all Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.LExprTypeEnvProps
import Strata.Util.ListMapProps
import Strata.Util.ListUtilsProps

/-! ## Datatype block compatibility

Key theorems: `resolveAliases_MutualBlockTyCompat_poly` (alias resolution gives a block compatible
with its source block) and `MutualBlockTyCompat.generatedFuncNames_eq` (compatible blocks generate
the same function names). -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

public section

/-! ### Alias resolution produces compatible blocks -/

/-- Zipping the same names with a type list and with its alias resolution gives pairs with
    equal names and alias-equivalent types. -/
private theorem resolveTys_zip_forall₂
    (Γ : TContext Unit)
    (tys : List LMonoTy) (Env : Expression.TyEnv) (tys' : List LMonoTy) (Env2 : Expression.TyEnv)
    (names : List (Identifier Unit))
    (h : LMonoTys.resolveAliases tys Env = .ok (tys', Env2))
    (h_aliases : Γ.aliases = Env.context.aliases) :
    List.Rel₂
      (fun (ar a : Identifier Unit × LMonoTy) => ar.1 = a.1 ∧ AliasEquiv Γ.aliases ar.2 a.2)
      (names.zip tys') (names.zip tys) := by
  induction tys generalizing names Env tys' Env2 with
  | nil =>
    simp only [LMonoTys.resolveAliases] at h
    obtain ⟨rfl, _⟩ := h
    simp only [List.zip, List.zipWith]
    exact .nil
  | cons t trest ih =>
    simp only [LMonoTys.resolveAliases, bind, Except.bind] at h
    elim_err h
    rename_i v1 h_hd; obtain ⟨t', Env1⟩ := v1; simp only at h h_hd
    elim_err h
    rename_i v2 h_tl; obtain ⟨trest', Env3⟩ := v2
    simp only at h; obtain ⟨rfl, _⟩ := h
    have h_ae_ht : AliasEquiv Γ.aliases t t' :=
      LExpr.resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Γ) t Env t' Env1 h_hd h_aliases
    have h_ctx : Env1.context = Env.context :=
      LExpr.LMonoTy.resolveAliases_context t Env t' Env1 h_hd
    cases names with
    | nil => simp only [List.zip, List.zipWith]; exact .nil
    | cons n nrest =>
      simp only [List.zip, List.zipWith]
      refine .cons ⟨rfl, LExpr.AliasEquiv.symm h_ae_ht⟩ ?_
      exact ih (names := nrest) (Env := Env1) (tys' := trest') (Env2 := Env2)
        h_tl (by rw [h_aliases, h_ctx])

/-- Resolving aliases in a constructor's argument list keeps every argument name and replaces
    each argument type by an alias-equivalent one. -/
private theorem go_forall₂
    (Γ : TContext Unit) (args : List (Identifier Unit × LMonoTy)) (Env : Expression.TyEnv)
    (args' : List (Identifier Unit × LMonoTy)) (Env2 : Expression.TyEnv)
    (h : LConstrs.resolveAliases.go args Env = .ok (args', Env2))
    (h_aliases : Γ.aliases = Env.context.aliases) :
    List.Rel₂
      (fun (ar a : Identifier Unit × LMonoTy) => ar.1 = a.1 ∧ AliasEquiv Γ.aliases ar.2 a.2)
      args' args := by
  simp only [LConstrs.resolveAliases.go, bind, Except.bind] at h
  elim_err h
  rename_i v h_tys; obtain ⟨tys', Env'⟩ := v; simp only at h h_tys
  obtain ⟨rfl, rfl⟩ := h
  have key := resolveTys_zip_forall₂ Γ (args.map (·.snd)) Env tys' Env2
    (args.map (·.fst)) h_tys h_aliases
  rw [← List.zip_of_prod rfl rfl] at key
  exact key

/-- Resolving aliases in a list of constructors relates each resolved constructor to its
    original: same name and tester name, same argument names, alias-equivalent argument types. -/
private theorem LConstrs_forall₂
    (Γ : TContext Unit) (constrs : List (LConstr Unit)) (Env : Expression.TyEnv)
    (constrs' : List (LConstr Unit)) (Env2 : Expression.TyEnv)
    (h : LConstrs.resolveAliases constrs Env = .ok (constrs', Env2))
    (h_aliases : Γ.aliases = Env.context.aliases) :
    List.Rel₂ (ConstrTyCompat Γ) constrs' constrs := by
  induction constrs generalizing Env constrs' Env2 with
  | nil =>
    simp only [LConstrs.resolveAliases, List.foldrM_nil, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact .nil
  | cons c crest ih =>
    obtain ⟨acc_crest, Env_crest, args', heq, hgo, rfl⟩ := LConstrs.resolveAliases_cons_inv h
    have h_aliases' : Γ.aliases = Env_crest.context.aliases := by
      rw [h_aliases, LConstrs.resolveAliases_env_eq crest Env acc_crest Env_crest heq]
    have hargs := go_forall₂ Γ c.args Env_crest args' Env2 hgo h_aliases'
    refine .cons ⟨rfl, rfl, hargs⟩ ?_
    exact ih (Env := Env) (constrs' := acc_crest) (Env2 := Env_crest) heq h_aliases

/-- Resolving aliases in a mutual datatype block relates each resolved datatype to its
    original: same name and type parameters, and related constructors. -/
private theorem block_forall₂
    (Γ : TContext Unit) (block : List (LDatatype Unit)) (Env : Expression.TyEnv)
    (block_r : List (LDatatype Unit)) (Env2 : Expression.TyEnv)
    (h : MutualDatatype.resolveAliases block Env = .ok (block_r, Env2))
    (h_aliases : Γ.aliases = Env.context.aliases) :
    List.Rel₂ (DatatypeTyCompat Γ) block_r block := by
  induction block generalizing Env block_r Env2 with
  | nil =>
    simp only [MutualDatatype.resolveAliases, List.foldrM_nil, pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact .nil
  | cons d drest ih =>
    obtain ⟨acc_drest, Env_drest, constrs', d_r, heq, hcon, rfl, hname, htypeArgs, hconstrsEq⟩ :=
      MutualDatatype.resolveAliases_cons_inv h
    have h_aliases' : Γ.aliases = Env_drest.context.aliases := by
      rw [h_aliases, MutualDatatype.resolveAliases_env_eq drest acc_drest Env Env_drest heq]
    have hconstrs := LConstrs_forall₂ Γ d.constrs Env_drest constrs' Env2 hcon h_aliases'
    rw [← hconstrsEq] at hconstrs
    refine .cons ⟨hname, htypeArgs, hconstrs⟩ ?_
    exact ih (Env := Env) (block_r := acc_drest) (Env2 := Env_drest) heq h_aliases

/-- Alias resolution relates a resolved mutual datatype block to its source block. -/
theorem resolveAliases_MutualBlockTyCompat_poly
    (block block_r : List (LDatatype Unit)) (Env Env' : Expression.TyEnv)
    (h : MutualDatatype.resolveAliases block Env = .ok (block_r, Env')) :
    MutualBlockTyCompat Env.context block_r block :=
  block_forall₂ Env.context block Env block_r Env' h rfl

/-- Block compatibility carries over to a scope in which every pair of types alias-equivalent
    in the first scope is alias-equivalent in the second. -/
theorem MutualBlockTyCompat.of_aliasEquiv {Γ Ξ : TContext Unit}
    {block_r block : List (LDatatype Unit)}
    (h : ∀ t t', AliasEquiv Γ.aliases t t' → AliasEquiv Ξ.aliases t t')
    (hc : MutualBlockTyCompat Γ block_r block) :
    MutualBlockTyCompat Ξ block_r block :=
  List.Rel₂.imp (fun _ _ ⟨hn, hta, hcs⟩ => ⟨hn, hta, List.Rel₂.imp
    (fun _ _ ⟨hcn, htn, has⟩ => ⟨hcn, htn, List.Rel₂.imp
      (fun _ _ ⟨hk, hty⟩ => ⟨hk, h _ _ hty⟩) has⟩) hcs⟩) hc

/-- A resolved block compatible with a source block generates the same function names. -/
theorem MutualBlockTyCompat.generatedFuncNames_eq
    {Γ : TContext Unit} {block_r block : List (LDatatype Unit)}
    (h : MutualBlockTyCompat Γ block_r block) :
    MutualDatatype.generatedFuncNames block_r = MutualDatatype.generatedFuncNames block := by
  have hblock : ∀ {γ : Type} (f : LDatatype Unit → List γ),
      (∀ d_r d, DatatypeTyCompat Γ d_r d → f d_r = f d) →
      block_r.flatMap f = block.flatMap f := by
    intro γ f hf
    simp only [List.flatMap_def]
    rw [List.Rel₂.map_eq hf h]
  have hconstrs : ∀ {γ : Type} {d_r d : LDatatype Unit} (f : LConstr Unit → List γ),
      DatatypeTyCompat Γ d_r d →
      (∀ c_r c, ConstrTyCompat Γ c_r c → f c_r = f c) →
      d_r.constrs.flatMap f = d.constrs.flatMap f := by
    intro γ d_r d f hd hf
    simp only [List.flatMap_def]
    rw [List.Rel₂.map_eq hf hd.2.2]
  have hargs : ∀ {c_r c : LConstr Unit} (f : Identifier Unit → String),
      ConstrTyCompat Γ c_r c →
      c_r.args.map (fun arg => f arg.1) = c.args.map (fun arg => f arg.1) := by
    intro c_r c f hc
    exact List.Rel₂.map_eq (fun _ _ hp => by rw [hp.1]) hc.2.2
  have helim : block_r.map (fun d => (elimFuncName d).name) =
      block.map (fun d => (elimFuncName d).name) :=
    List.Rel₂.map_eq (fun _ _ hd => by simp only [elimFuncName, hd.1]) h
  have hctor : block_r.flatMap (fun d => d.constrs.map (fun c => c.name.name)) =
      block.flatMap (fun d => d.constrs.map (fun c => c.name.name)) :=
    hblock _ (fun _ _ hd => List.Rel₂.map_eq (fun _ _ hc => by rw [hc.1]) hd.2.2)
  have htester : block_r.flatMap (fun d => d.constrs.map (fun c => c.testerName)) =
      block.flatMap (fun d => d.constrs.map (fun c => c.testerName)) :=
    hblock _ (fun _ _ hd => List.Rel₂.map_eq (fun _ _ hc => hc.2.1) hd.2.2)
  have hdestr : ∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d →
      ∀ n, destructorFuncName d_r n = destructorFuncName d n := by
    intro d_r d hd n
    simp only [destructorFuncName, hd.1]
  have hdes : ∀ g : LDatatype Unit → Identifier Unit → String,
      (∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d → ∀ n, g d_r n = g d n) →
      block_r.flatMap (fun d => d.constrs.flatMap (fun c => c.args.map (fun a => g d a.1))) =
        block.flatMap (fun d => d.constrs.flatMap (fun c => c.args.map (fun a => g d a.1))) := by
    intro g hg
    refine hblock _ (fun d_r d hd => ?_)
    simp only [hg hd]
    exact hconstrs _ hd (fun _ _ hc => hargs _ hc)
  have hunsafe : ∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d →
      ∀ n, unsafeDestructorFuncName d_r n = unsafeDestructorFuncName d n := by
    intro d_r d hd n
    simp only [unsafeDestructorFuncName, hdestr hd]
  unfold MutualDatatype.generatedFuncNames
  rw [helim, hctor, htester, hdes _ hdestr, hdes _ hunsafe]

end -- public section

end TypeSpec
end Core
