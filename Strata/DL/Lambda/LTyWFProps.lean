/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyWF
import all Strata.DL.Lambda.LTyWF
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LTyUnifyProps
import Strata.Util.Tactics
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.Identifiers
import all Strata.DL.Lambda.NamePrefixes

/-! ## Properties of executable Lambda monotype checking

Key theorems: `LMonoTy.knownInstance_wellKinded` and `LMonoTy.wellKinded_knownInstance` (a type
uses only registered constructors at their arities exactly when it is well kinded),
`LMonoTy.resolveAliases_isOk` (alias resolution never fails), `LMonoTy.resolveAliases_subst_comm`
(it commutes with renaming type variables), `knownInstance_of_subst` (a type is registered when
a substitution instance of it is), and `addTypeAlias_decompose` (what declaring an alias does).

The file also holds facts about `LMonoTy.resolveAliases` and `LMonoTy.knownInstance`, which are
defined in `LExprTypeEnv.lean`. -/

namespace Lambda

open Std (ToFormat)

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta]

public section

/-- A list of registered instances is registered. -/
theorem LMonoTys.knownInstances_of_forall {ks : KnownTypes} {tys : LMonoTys}
    (h : ∀ t ∈ tys, LMonoTy.knownInstance t ks = true) :
    LMonoTys.knownInstances tys ks = true := by
  induction tys with
  | nil => rfl
  | cons t rest ih =>
    simp only [LMonoTys.knownInstances, h t List.mem_cons_self, ite_true]
    exact ih (fun u hu => h u (List.mem_cons_of_mem t hu))

/-- A successful source check resolves aliases to a type with admissible free variables and
    only registered constructors, and returns that type and environment. -/
theorem LMonoTy.typeCheckSource_ok_inv
    (ty resolved : LMonoTy) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (admissible : TyVarAdmissibility)
    (h : LMonoTy.typeCheckSource ty C Env admissible = .ok (resolved, Env')) :
    ty.resolveAliases Env = .ok (resolved, Env') ∧ resolved.freeVars.all admissible = true ∧
      resolved.knownInstance C.knownTypes = true := by
  simp only [LMonoTy.typeCheckSource, Bind.bind, Except.bind] at h
  elim_err h with pair hresolve
  obtain ⟨resolved0, Env0⟩ := pair
  elim_err h with checked hcheck
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp only [LMonoTy.typeCheckResolved] at hcheck
  elim_err hcheck with hfree
  elim_err hcheck with hknown
  simp only [Except.ok.injEq] at hcheck
  subst hcheck
  exact ⟨hresolve, by simpa using hfree, hknown⟩

/-- A successful source check returns the result of `LMonoTy.resolveAliases`. -/
theorem LMonoTy.typeCheckSource_resolveAliases
    (ty resolved : LMonoTy) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (admissible : TyVarAdmissibility)
    (h : LMonoTy.typeCheckSource ty C Env admissible = .ok (resolved, Env')) :
    ty.resolveAliases Env = .ok (resolved, Env') :=
  (LMonoTy.typeCheckSource_ok_inv ty resolved C Env Env' admissible h).1

/-- When the policy admits no generator-namespace name, a successful source check agrees with
    instantiating the monotype as a scheme without bound variables. -/
theorem LMonoTy.typeCheckSource_instantiateWithCheck
    (ty resolved : LMonoTy) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (admissible : TyVarAdmissibility)
    (hadmissible : ∀ v, admissible v = true → genTyPrefix.toList.isPrefixOf v.toList = false)
    (h : LMonoTy.typeCheckSource ty C Env admissible = .ok (resolved, Env')) :
    LTy.instantiateWithCheck (.forAll [] ty) C Env = .ok (resolved, Env') := by
  have hresolve := LMonoTy.typeCheckSource_resolveAliases ty resolved C Env Env' admissible h
  obtain ⟨-, hfree, hknown⟩ := LMonoTy.typeCheckSource_ok_inv ty resolved C Env Env' admissible h
  have hcheck : LMonoTy.checkNoFutureGenVars resolved Env'.genEnv.genState = true := by
    simp only [LMonoTy.checkNoFutureGenVars, List.all_eq_true] at hfree ⊢
    intro v hv
    have hpfx := hadmissible v (hfree v hv)
    simp only [TState.isFutureGenVar, TState.tyPrefix, hpfx]
    rfl
  simp only [LTy.instantiateWithCheck, LTy.resolveAliases, LTy.instantiate, bind, Except.bind,
    hresolve, hcheck, isInstanceOfKnownType, hknown]
  rfl

mutual
/-- Alias resolution never fails, and returns the environment it was given. -/
theorem LMonoTy.resolveAliases_isOk {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) :
    ∃ mty', LMonoTy.resolveAliases mty Env = .ok (mty', Env) := by
  match mty with
  | .ftvar x =>
    refine ⟨.ftvar x, ?_⟩
    simp only [LMonoTy.resolveAliases, pure, Except.pure]
  | .bitvec n =>
    refine ⟨.bitvec n, ?_⟩
    simp only [LMonoTy.resolveAliases, pure, Except.pure]
  | .tcons name args =>
    obtain ⟨args', hargs⟩ := LMonoTys.resolveAliases_isOk args Env
    refine ⟨LMonoTy.tconsAliasSimple name args' Env.context.aliases, ?_⟩
    simp only [LMonoTy.resolveAliases, bind, Except.bind, hargs, pure, Except.pure]

/-- Alias resolution of a list never fails, and returns the environment it was given. -/
theorem LMonoTys.resolveAliases_isOk {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) :
    ∃ mtys', LMonoTys.resolveAliases mtys Env = .ok (mtys', Env) := by
  match mtys with
  | [] =>
    refine ⟨[], ?_⟩
    simp only [LMonoTys.resolveAliases, pure, Except.pure]
  | hd :: tl =>
    obtain ⟨hd', hhd⟩ := LMonoTy.resolveAliases_isOk hd Env
    obtain ⟨tl', htl⟩ := LMonoTys.resolveAliases_isOk tl Env
    refine ⟨hd' :: tl', ?_⟩
    simp only [LMonoTys.resolveAliases, bind, Except.bind, hhd, htl, pure, Except.pure]
end

/-- Resolving aliases in a monotype returns the environment it was given. -/
theorem LMonoTy.resolveAliases_env_eq
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mty : LMonoTy) (Env : TEnv IDMeta) (mty' : LMonoTy) (Env' : TEnv IDMeta)
    (h : LMonoTy.resolveAliases mty Env = .ok (mty', Env')) :
    Env' = Env := by
  obtain ⟨m, hm⟩ := LMonoTy.resolveAliases_isOk mty Env
  rw [hm] at h
  cases h
  rfl

/-- Resolving aliases in a list of monotypes returns the environment it was given. -/
theorem LMonoTys.resolveAliases_env_eq
    {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (mtys : LMonoTys) (Env : TEnv IDMeta) (mtys' : LMonoTys) (Env' : TEnv IDMeta)
    (h : LMonoTys.resolveAliases mtys Env = .ok (mtys', Env')) :
    Env' = Env := by
  obtain ⟨m, hm⟩ := LMonoTys.resolveAliases_isOk mtys Env
  rw [hm] at h
  cases h
  rfl

mutual
/-- A type that is a `knownInstance` is `WellKinded` under the known-types arities. -/
theorem LMonoTy.knownInstance_wellKinded (ty : LMonoTy) (ks : KnownTypes)
    (h : LMonoTy.knownInstance ty ks = true) :
    LMonoTy.WellKinded (fun n => ks[n]?) ty := by
  match ty with
  | .ftvar _ => intro ref n hmem; simp [getTypeConsArities] at hmem
  | .bitvec _ => intro ref n hmem; simp [getTypeConsArities] at hmem
  | .tcons name args =>
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h
    obtain ⟨hc, hargs⟩ := h
    intro ref n hmem
    simp only [getTypeConsArities, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      show ks[ref]? = some args.length
      simp only [KnownTypes.contains, Identifiers.contains, KnownType.arity] at hc
      elim_err hc with i hlk
      simp only [beq_iff_eq] at hc
      rw [hlk, hc]
    · rw [List.mem_flatMap] at hmem
      obtain ⟨arg, harg_mem, hmem'⟩ := hmem
      exact LMonoTys.knownInstances_wellKinded args ks hargs arg harg_mem ref n hmem'

/-- Every element of a `knownInstances` list is `WellKinded`. -/
private theorem LMonoTys.knownInstances_wellKinded (tys : LMonoTys) (ks : KnownTypes)
    (h : LMonoTys.knownInstances tys ks = true) :
    ∀ ty ∈ tys, LMonoTy.WellKinded (fun n => ks[n]?) ty := by
  match tys with
  | [] => intro ty hmem; simp at hmem
  | t :: rest =>
    simp only [LMonoTys.knownInstances] at h
    elim_err h with ht
    intro ty hmem
    rcases List.mem_cons.mp hmem with heq | hmem
    · rw [heq]; exact LMonoTy.knownInstance_wellKinded t ks ht
    · exact LMonoTys.knownInstances_wellKinded rest ks h ty hmem
end

mutual
/-- A monotype that is well kinded under the known-types arities uses only registered
    constructors at their arities, so it is a `knownInstance`. -/
theorem LMonoTy.wellKinded_knownInstance (ty : LMonoTy) (ks : KnownTypes)
    (h : LMonoTy.WellKinded (fun n => ks[n]?) ty) :
    LMonoTy.knownInstance ty ks = true := by
  match ty with
  | .ftvar _ => simp [LMonoTy.knownInstance]
  | .bitvec _ => simp [LMonoTy.knownInstance]
  | .tcons name args =>
    have hhead : (name, args.length) ∈ getTypeConsArities (.tcons name args) := by
      simp [getTypeConsArities]
    have hk : ks[name]? = some args.length := h name args.length hhead
    have hc : ks.contains { name := name, metadata := args.length } = true := by
      simp [KnownTypes.contains, Identifiers.contains, KnownType.arity, hk]
    have hargs : ∀ t ∈ args, LMonoTy.WellKinded (fun n => ks[n]?) t := by
      intro t ht ref n hm
      have hmem : (ref, n) ∈ getTypeConsArities (.tcons name args) := by
        simp only [getTypeConsArities, List.mem_cons, List.mem_flatMap]
        exact Or.inr ⟨t, ht, hm⟩
      exact h ref n hmem
    simp only [LMonoTy.knownInstance, hc, Bool.true_and]
    exact LMonoTys.wellKinded_knownInstances args ks hargs

/-- A list of monotypes that are all well kinded under the known-types arities is a list of
    `knownInstance`s. -/
private theorem LMonoTys.wellKinded_knownInstances (tys : LMonoTys) (ks : KnownTypes)
    (h : ∀ ty ∈ tys, LMonoTy.WellKinded (fun n => ks[n]?) ty) :
    LMonoTys.knownInstances tys ks = true := by
  match tys with
  | [] => simp [LMonoTys.knownInstances]
  | t :: rest =>
    have hhead := LMonoTy.wellKinded_knownInstance t ks (h t List.mem_cons_self)
    have htail : ∀ ty ∈ rest, LMonoTy.WellKinded (fun n => ks[n]?) ty :=
      fun ty hty => h ty (List.mem_cons_of_mem t hty)
    simp only [LMonoTys.knownInstances, hhead, ite_true]
    exact LMonoTys.wellKinded_knownInstances rest ks htail
end

mutual
/-- Alias resolution commutes with a variable-to-variable substitution when aliases are well
    formed. -/
theorem LMonoTy.resolveAliases_subst_comm {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (S : Subst) (mty : LMonoTy) (Env : TEnv IDMeta)
    (mtyR mtySR : LMonoTy) (EnvR EnvSR : TEnv IDMeta)
    (haWF : TContext.AliasesWF Env.context)
    (hSftvar : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y)
    (hR : LMonoTy.resolveAliases mty Env = .ok (mtyR, EnvR))
    (hSR : LMonoTy.resolveAliases (LMonoTy.subst S mty) Env = .ok (mtySR, EnvSR)) :
    mtySR = LMonoTy.subst S mtyR := by
  match mty with
  | .ftvar x =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hR
    rw [← hR.1]
    obtain ⟨y, hy⟩ := hSftvar x
    rw [hy] at hSR
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hSR
    rw [← hSR.1, hy]
  | .bitvec n =>
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hR
    rw [LMonoTy.subst_bitvec] at hSR
    simp only [LMonoTy.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hSR
    rw [← hR.1, ← hSR.1, LMonoTy.subst_bitvec]
  | .tcons name args =>
    simp only [LMonoTy.subst_unfold] at hSR
    simp only [LMonoTy.resolveAliases, bind, Except.bind] at hR hSR
    elim_err hR
    rename_i vR hargsR
    obtain ⟨argsR, EnvRMid⟩ := vR
    elim_err hSR
    rename_i vSR hargsSR
    obtain ⟨argsSR, EnvSRMid⟩ := vSR
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hR hSR
    have hEnvRMid : EnvRMid = Env :=
      LMonoTys.resolveAliases_env_eq args Env argsR EnvRMid hargsR
    have hEnvSRMid : EnvSRMid = Env :=
      LMonoTys.resolveAliases_env_eq _ Env argsSR EnvSRMid hargsSR
    rw [hEnvRMid] at hargsR hR
    rw [hEnvSRMid] at hargsSR hSR
    rw [← hR.1, ← hSR.1]
    have hargsEq : argsSR = argsR.map (LMonoTy.subst S) :=
      LMonoTys.resolveAliases_subst_comm S args Env argsR argsSR Env Env haWF hSftvar
        hargsR hargsSR
    rw [hargsEq]
    have hlen : (argsR.map (LMonoTy.subst S)).length = argsR.length := List.length_map _
    rcases hfind : Env.context.aliases.find?
        (fun a => a.name == name && a.typeArgs.length == argsR.length) with _ | al
    · simp only [LMonoTy.tconsAliasSimple, hlen, hfind, LMonoTy.subst_unfold]
    · have hpred := List.find?_some hfind
      simp only [Bool.and_eq_true, beq_iff_eq] at hpred
      have halWF : TypeAlias.WF al := haWF al (List.mem_of_find?_eq_some hfind)
      simp only [LMonoTy.tconsAliasSimple, hlen, hfind, TypeAlias.expand]
      exact (LExpr.subst_openVars_comm S al.typeArgs argsR al.type halWF.fvs_closed hpred.2).symm

/-- Alias resolution of a list commutes with a variable-to-variable substitution when aliases
    are well formed. -/
theorem LMonoTys.resolveAliases_subst_comm {IDMeta : Type}
    [DecidableEq IDMeta] [Hashable IDMeta] [ToFormat IDMeta]
    (S : Subst) (mtys : LMonoTys) (Env : TEnv IDMeta)
    (mtysR mtysSR : LMonoTys) (EnvR EnvSR : TEnv IDMeta)
    (haWF : TContext.AliasesWF Env.context)
    (hSftvar : ∀ x : TyIdentifier, ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y)
    (hR : LMonoTys.resolveAliases mtys Env = .ok (mtysR, EnvR))
    (hSR : LMonoTys.resolveAliases (mtys.map (LMonoTy.subst S)) Env = .ok (mtysSR, EnvSR)) :
    mtysSR = mtysR.map (LMonoTy.subst S) := by
  match mtys with
  | [] =>
    simp only [List.map_nil, LMonoTys.resolveAliases, pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at hR hSR
    rw [← hR.1, ← hSR.1, List.map_nil]
  | mty :: mrest =>
    simp only [List.map_cons] at hSR
    simp only [LMonoTys.resolveAliases, bind, Except.bind] at hR hSR
    elim_err hR
    rename_i vRHd hhdR
    obtain ⟨mtyR, EnvRHd⟩ := vRHd
    elim_err hR
    rename_i vRTl htlR
    obtain ⟨mrestR, EnvRTl⟩ := vRTl
    elim_err hSR
    rename_i vSRHd hhdSR
    obtain ⟨mtySR, EnvSRHd⟩ := vSRHd
    elim_err hSR
    rename_i vSRTl htlSR
    obtain ⟨mrestSR, EnvSRTl⟩ := vSRTl
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hR hSR
    have hEnvRHd : EnvRHd = Env :=
      LMonoTy.resolveAliases_env_eq mty Env mtyR EnvRHd hhdR
    have hEnvSRHd : EnvSRHd = Env :=
      LMonoTy.resolveAliases_env_eq _ Env mtySR EnvSRHd hhdSR
    rw [hEnvRHd] at hhdR htlR
    rw [hEnvSRHd] at hhdSR htlSR
    rw [← hR.1, ← hSR.1, List.map_cons]
    rw [LMonoTy.resolveAliases_subst_comm S mty Env mtyR mtySR Env Env haWF hSftvar hhdR hhdSR,
        LMonoTys.resolveAliases_subst_comm S mrest Env mrestR mrestSR EnvRTl EnvSRTl haWF
          hSftvar htlR htlSR]
end

mutual
/-- If a substituted monotype mentions only registered type constructors, so does the monotype. -/
theorem knownInstance_of_subst (ks : KnownTypes) (S : Subst) (mty : LMonoTy)
    (h : LMonoTy.knownInstance (LMonoTy.subst S mty) ks = true) :
    LMonoTy.knownInstance mty ks = true := by
  match mty with
  | .ftvar _ => simp only [LMonoTy.knownInstance]
  | .bitvec _ => simp only [LMonoTy.knownInstance]
  | .tcons name args =>
    simp only [LMonoTy.subst_unfold, LMonoTy.knownInstance, List.length_map,
      Bool.and_eq_true] at h
    simp only [LMonoTy.knownInstance, Bool.and_eq_true]
    exact ⟨h.1, knownInstances_of_subst ks S args h.2⟩

/-- If a substituted list mentions only registered type constructors, so does the list. -/
private theorem knownInstances_of_subst (ks : KnownTypes) (S : Subst) (mtys : LMonoTys)
    (h : LMonoTys.knownInstances (mtys.map (LMonoTy.subst S)) ks = true) :
    LMonoTys.knownInstances mtys ks = true := by
  match mtys with
  | [] => simp only [LMonoTys.knownInstances]
  | mty :: mrest =>
    simp only [List.map_cons, LMonoTys.knownInstances] at h
    simp only [LMonoTys.knownInstances]
    elim_err h with hhd
    rw [ite_eq_left (knownInstance_of_subst ks S mty hhd)]
    exact knownInstances_of_subst ks S mrest h
end

/-- A successful `addTypeAlias` checks the alias and only prepends it with its resolved body. -/
theorem addTypeAlias_decompose {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (a : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : TEnv.addTypeAlias a C Env = .ok Env') :
    a.typeArgs.Nodup
    ∧ (∀ v, v ∈ LMonoTy.freeVars a.type → v ∈ a.typeArgs)
    ∧ (∀ v, v ∈ a.typeArgs → v ∈ LMonoTy.freeVars a.type)
    ∧ ¬ C.knownTypes.containsName a.name
    ∧ (∀ b ∈ Env.context.aliases, b.name ≠ a.name)
    ∧ ∃ storedTy Env_ra, LMonoTy.resolveAliases a.type Env = .ok (storedTy, Env_ra)
        ∧ Env'.context.aliases
            = { typeArgs := a.typeArgs, name := a.name, type := storedTy } :: Env.context.aliases
        ∧ Env'.context.types = Env.context.types
        ∧ Env'.stateSubstInfo = Env.stateSubstInfo
        ∧ Env'.genEnv.genState = Env.genEnv.genState
        ∧ LMonoTy.typeCheckSource a.type C Env TyVarAdmissibility.all = .ok (storedTy, Env_ra) := by
  unfold TEnv.addTypeAlias at h
  simp only [bind, Except.bind] at h
  elim_err h
  elim_err h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hnodup hfv _ hphantom hknown hfresh
        split at h
        · simp at h
        · rename_i rares hsource
          obtain ⟨storedTy, Env_ra⟩ := rares
          simp only [Except.ok.injEq] at h
          subst Env'
          have hra : LMonoTy.resolveAliases a.type Env = .ok (storedTy, Env_ra) :=
            LMonoTy.typeCheckSource_resolveAliases
              a.type storedTy C Env Env_ra TyVarAdmissibility.all hsource
          have hEnvRa : Env_ra = Env :=
            LMonoTy.resolveAliases_env_eq a.type Env storedTy Env_ra hra
          have hctx : Env_ra.genEnv.context = Env.genEnv.context := by rw [hEnvRa]
          refine ⟨?_, ?_, ?_, ?_, ?_, storedTy, Env_ra, hra, ?_, ?_, ?_, ?_, hsource⟩
          · simpa using hnodup
          · intro v hv
            rcases Decidable.em (v ∈ a.typeArgs) with hin | hnin
            · exact hin
            · exfalso
              apply hfv
              have hd : decide (a.type.freeVars ⊆ a.typeArgs) = false :=
                decide_eq_false (fun hsub => hnin (hsub hv))
              simp [hd]
          · intro v hv
            rcases Decidable.em (v ∈ a.type.freeVars) with hin | hnin
            · exact hin
            · exfalso
              have hp : (fun w => decide (¬ w ∈ a.type.freeVars)) v = true := by
                simp only [decide_eq_true_eq]; exact hnin
              have hnn :
                  List.find? (fun w => decide (¬ w ∈ a.type.freeVars)) a.typeArgs ≠ none := by
                intro hnone
                rw [List.find?_eq_none] at hnone
                exact hnone v hv hp
              rcases hc : List.find? (fun w => decide (¬ w ∈ a.type.freeVars)) a.typeArgs
                with _ | b
              · exact hnn hc
              · exact hphantom b hc
          · simpa using hknown
          · intro b hb
            have hany : Env.context.aliases.any (fun c => c.name == a.name) = false := by
              simpa using hfresh
            rw [List.any_eq_false] at hany
            simpa using hany b hb
          · simp only [TEnv.updateContext, TEnv.context, hctx]
          · simp only [TEnv.updateContext, TEnv.context, hctx]
          · rw [hEnvRa]
            rfl
          · rw [hEnvRa]
            rfl

/-- Declaring a type alias keeps every existing alias. -/
theorem TEnv.addTypeAlias_aliases_subset {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (a : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : TEnv.addTypeAlias a C Env = .ok Env') :
    Env.context.aliases ⊆ Env'.context.aliases := by
  obtain ⟨-, -, -, -, -, storedTy, Env_ra, -, haliases, -⟩ := addTypeAlias_decompose a C Env Env' h
  rw [haliases]
  exact List.subset_cons_self _ _

/-- Declaring a type alias keeps the substitution. -/
theorem TEnv.addTypeAlias_stateSubstInfo {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (a : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : TEnv.addTypeAlias a C Env = .ok Env') :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  obtain ⟨-, -, -, -, -, _, _, -, -, -, hstate, -⟩ := addTypeAlias_decompose a C Env Env' h
  exact hstate

/-- Declaring a type alias keeps the generator state. -/
theorem TEnv.addTypeAlias_genState {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [ToFormat T.IDMeta]
    (a : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : TEnv.addTypeAlias a C Env = .ok Env') :
    Env'.genEnv.genState = Env.genEnv.genState := by
  obtain ⟨-, -, -, -, -, _, _, -, -, -, -, hgen, -⟩ := addTypeAlias_decompose a C Env Env' h
  exact hgen

end

end Lambda
