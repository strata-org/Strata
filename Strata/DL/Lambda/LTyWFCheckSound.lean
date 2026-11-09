/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyWFProps
import all Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyWF
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.Util.Tactics

/-! ## Soundness of Lambda monotype checking

Key theorems: `LMonoTy.typeCheckResolved_sound` (resolved checking yields `ResolvedTyWF`),
`LMonoTy.typeCheckSource_sound` (source checking yields `SourceTyWF`),
`LMonoTy.typeCheckSource_complete` (source checking accepts every valid source type, returns
its resolution and leaves the environment unchanged),
`SourceTyResolves.exists` and `SourceTyResolves.unique` (every source type has exactly one alias
resolution), `SourceTyResolves.aliasEquiv` (a type is `AliasEquiv` to its resolution),
`ResolvedTyWF.wellKinded` and `ResolvedTyWF.of_wellKinded` (a resolved type is well formed exactly
when it is well kinded with admissible variables), and `SourceTyWF.of_subst` (validity is
reflected through a substitution).

Result-level theorems: `LMonoTy.instantiateWithCheck_sourceTyWF` (a type accepted by
`instantiateWithCheck` is a valid source type) and `TEnv.addTypeAlias_sourceTyWF` (a
registered alias is well formed with a valid body, and its stored body is that body's
resolution). -/

namespace Lambda

open LExpr

variable {T : LExprParams} [DecidableEq T.IDMeta] [Hashable T.IDMeta]
  [Std.ToFormat T.IDMeta]

public section

mutual
/-- The resolved judgment implies the executable registered-constructor predicate. -/
theorem ResolvedTyWF.knownInstance (h : ResolvedTyWF C admissible ty) :
    ty.knownInstance C.knownTypes = true := by
  cases h with
  | ftvar => simp [LMonoTy.knownInstance]
  | bitvec => simp [LMonoTy.knownInstance]
  | tcons hknown hargs =>
      simp only [LMonoTy.knownInstance, hknown, Bool.true_and]
      exact hargs.knownInstances

/-- The resolved list judgment implies the executable predicate for every member. -/
theorem ResolvedTysWF.knownInstances (h : ResolvedTysWF C admissible tys) :
    tys.knownInstances C.knownTypes = true := by
  cases h with
  | nil => simp [LMonoTys.knownInstances]
  | cons hhead htail =>
      simp only [LMonoTys.knownInstances, hhead.knownInstance, ite_true]
      exact htail.knownInstances
end

/-- A type valid under the resolved judgment is well kinded. -/
theorem ResolvedTyWF.wellKinded (h : ResolvedTyWF C admissible ty) :
    C.WellKindedTy ty :=
  LMonoTy.knownInstance_wellKinded ty C.knownTypes h.knownInstance

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
mutual
/-- A monotype with only admissible free variables, whose constructors are all registered at
    their arities, is valid under the resolved judgment. -/
private theorem ResolvedTyWF.of_knownInstance_admissible {C : LContext T}
    {admissible : TyVarAdmissibility} {ty : LMonoTy}
    (hknown : ty.knownInstance C.knownTypes = true)
    (hfree : ty.freeVars.all admissible = true) : ResolvedTyWF C admissible ty := by
  cases ty with
  | ftvar v =>
      simp only [LMonoTy.freeVars, List.all_cons, List.all_nil, Bool.and_true] at hfree
      exact ResolvedTyWF.ftvar hfree
  | bitvec n => exact ResolvedTyWF.bitvec
  | tcons name args =>
      simp only [LMonoTy.knownInstance, Bool.and_eq_true] at hknown
      simp only [LMonoTy.freeVars] at hfree
      exact ResolvedTyWF.tcons hknown.1
        (ResolvedTysWF.of_knownInstances_admissible hknown.2 hfree)

/-- A list of monotypes with only admissible free variables, whose constructors are all
    registered at their arities, is valid under the resolved list judgment. -/
private theorem ResolvedTysWF.of_knownInstances_admissible {C : LContext T}
    {admissible : TyVarAdmissibility} {tys : LMonoTys}
    (hknown : tys.knownInstances C.knownTypes = true)
    (hfree : (LMonoTys.freeVars tys).all admissible = true) :
    ResolvedTysWF C admissible tys := by
  cases tys with
  | nil => exact ResolvedTysWF.nil
  | cons head tail =>
      simp only [LMonoTys.knownInstances] at hknown
      simp only [LMonoTys.freeVars, List.all_append, Bool.and_eq_true] at hfree
      split at hknown
      · rename_i hhead
        exact ResolvedTysWF.cons
          (ResolvedTyWF.of_knownInstance_admissible hhead hfree.1)
          (ResolvedTysWF.of_knownInstances_admissible hknown hfree.2)
      · exact absurd hknown Bool.false_ne_true
end

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- With unrestricted variable admissibility, a monotype whose constructors are all registered at
    their arities is valid under the resolved judgment. -/
theorem ResolvedTyWF.of_knownInstance {C : LContext T} {ty : LMonoTy}
    (h : ty.knownInstance C.knownTypes = true) : ResolvedTyWF C TyVarAdmissibility.all ty := by
  have hfree : ty.freeVars.all TyVarAdmissibility.all = true := by
    simp only [TyVarAdmissibility.all, List.all_eq_true, implies_true]
  exact ResolvedTyWF.of_knownInstance_admissible h hfree

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- A well-kinded monotype whose free variables are all admissible is a well-formed resolved
    type: each constructor's registered arity is the one it is applied at. -/
theorem ResolvedTyWF.of_wellKinded {C : LContext T} {admissible : TyVarAdmissibility}
    {ty : LMonoTy} (hwk : C.WellKindedTy ty) (hfree : ∀ v ∈ ty.freeVars, admissible v = true) :
    ResolvedTyWF C admissible ty := by
  have hknown := LMonoTy.wellKinded_knownInstance ty C.knownTypes hwk
  have hfreeAll : ty.freeVars.all admissible = true := List.all_eq_true.mpr hfree
  exact ResolvedTyWF.of_knownInstance_admissible hknown hfreeAll

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
mutual
/-- Every free variable of a well-formed resolved type is admissible. -/
theorem ResolvedTyWF.admissible {C : LContext T} {admissible : TyVarAdmissibility}
    {ty : LMonoTy} (h : ResolvedTyWF C admissible ty) :
    ∀ v ∈ ty.freeVars, admissible v = true := by
  cases h with
  | ftvar hv =>
    intro v hmem
    simp only [LMonoTy.freeVars, List.mem_singleton] at hmem
    subst hmem
    exact hv
  | bitvec => intro v hmem; simp [LMonoTy.freeVars] at hmem
  | tcons _ hargs =>
    intro v hmem
    simp only [LMonoTy.freeVars] at hmem
    exact hargs.admissible v hmem

/-- Every free variable of a list of well-formed resolved types is admissible. -/
private theorem ResolvedTysWF.admissible {C : LContext T} {admissible : TyVarAdmissibility}
    {tys : LMonoTys} (h : ResolvedTysWF C admissible tys) :
    ∀ v ∈ LMonoTys.freeVars tys, admissible v = true := by
  cases h with
  | nil => intro v hmem; simp [LMonoTys.freeVars] at hmem
  | cons hh ht =>
    intro v hmem
    simp only [LMonoTys.freeVars, List.mem_append] at hmem
    rcases hmem with hm | hm
    · exact hh.admissible v hm
    · exact ht.admissible v hm
end

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- A successful resolved check yields a well-formed resolved type, whatever written type and
    aliases are passed for error reporting. -/
theorem LMonoTy.typeCheckResolved_sound
    (ty result : LMonoTy) (C : LContext T) (admissible : TyVarAdmissibility)
    (source : LMonoTy) (aliases : List TypeAlias)
    (h : LMonoTy.typeCheckResolved ty C admissible source aliases = .ok result) :
    ResolvedTyWF C admissible result := by
  simp only [LMonoTy.typeCheckResolved] at h
  elim_err h with hfree
  elim_err h with hknown
  simp only [Except.ok.injEq] at h
  subst result
  have hfree' : ty.freeVars.all admissible = true := by simpa using hfree
  exact ResolvedTyWF.of_knownInstance_admissible hknown hfree'

mutual
/-- The executable resolver produces the corresponding declarative source resolution. -/
theorem LMonoTy.resolveAliases_sourceTyResolves
    (ty : LMonoTy) (Env : TEnv T.IDMeta) (resolved : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : ty.resolveAliases Env = .ok (resolved, Env')) :
    SourceTyResolves Env.context.aliases ty resolved := by
  cases ty with
  | ftvar v =>
      simp only [LMonoTy.resolveAliases] at h
      obtain ⟨rfl, rfl⟩ := h
      exact SourceTyResolves.ftvar
  | bitvec n =>
      simp only [LMonoTy.resolveAliases] at h
      obtain ⟨rfl, rfl⟩ := h
      exact SourceTyResolves.bitvec
  | tcons name args =>
      simp only [LMonoTy.resolveAliases, bind, Except.bind] at h
      elim_err h
      rename_i pair hargs
      obtain ⟨resolvedArgs, EnvArgs⟩ := pair
      dsimp only at h hargs
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hEnv : EnvArgs = Env :=
        LMonoTys.resolveAliases_env_eq args Env resolvedArgs EnvArgs hargs
      subst EnvArgs
      have hargs' := LMonoTys.resolveAliases_sourceTysResolve args Env resolvedArgs Env hargs
      simp only [LMonoTy.tconsAliasSimple]
      split
      · rename_i hfind
        exact SourceTyResolves.tcons hargs' hfind
      · rename_i alias hfind
        exact SourceTyResolves.alias hargs' hfind

/-- The executable list resolver produces pointwise declarative source resolution. -/
theorem LMonoTys.resolveAliases_sourceTysResolve
    (tys : LMonoTys) (Env : TEnv T.IDMeta) (resolved : LMonoTys) (Env' : TEnv T.IDMeta)
    (h : tys.resolveAliases Env = .ok (resolved, Env')) :
    SourceTysResolve Env.context.aliases tys resolved := by
  cases tys with
  | nil =>
      simp only [LMonoTys.resolveAliases] at h
      obtain ⟨rfl, rfl⟩ := h
      exact SourceTysResolve.nil
  | cons head tail =>
      simp only [LMonoTys.resolveAliases, bind, Except.bind] at h
      elim_err h
      rename_i headPair hhead
      obtain ⟨resolvedHead, EnvHead⟩ := headPair
      dsimp only at h hhead
      elim_err h
      rename_i tailPair htail
      obtain ⟨resolvedTail, EnvTail⟩ := tailPair
      dsimp only at h htail
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hheadResolve := LMonoTy.resolveAliases_sourceTyResolves
        head Env resolvedHead EnvHead hhead
      have htailResolve := LMonoTys.resolveAliases_sourceTysResolve
        tail EnvHead resolvedTail EnvTail htail
      have hEnvHead := LMonoTy.resolveAliases_env_eq head Env resolvedHead EnvHead hhead
      rw [hEnvHead] at htailResolve
      exact SourceTysResolve.cons hheadResolve htailResolve
end

/-- A successful source check yields a well-formed source type whose resolution is the checked
    result. -/
theorem LMonoTy.typeCheckSource_sound
    (ty resolved : LMonoTy) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (admissible : TyVarAdmissibility)
    (h : LMonoTy.typeCheckSource ty C Env admissible = .ok (resolved, Env')) :
    SourceTyWF C admissible Env.context.aliases ty resolved := by
  obtain ⟨hresolve, hfree, hknown⟩ :=
    LMonoTy.typeCheckSource_ok_inv ty resolved C Env Env' admissible h
  have htype := ResolvedTyWF.of_knownInstance_admissible hknown hfree
  have hresolves := LMonoTy.resolveAliases_sourceTyResolves
    ty Env resolved Env' hresolve
  exact ⟨hresolves, htype⟩

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
mutual
/-- A type valid under the resolved judgment stays valid in a context registering at least the
    same constructors, at the same arities. -/
theorem ResolvedTyWF.of_knownTypes_contains {C C' : LContext T}
    {admissible : TyVarAdmissibility} {ty : LMonoTy}
    (hk : ∀ k, C.knownTypes.contains k = true → C'.knownTypes.contains k = true)
    (h : ResolvedTyWF C admissible ty) : ResolvedTyWF C' admissible ty := by
  cases h with
  | ftvar hadm => exact ResolvedTyWF.ftvar hadm
  | bitvec => exact ResolvedTyWF.bitvec
  | tcons hknown hargs =>
      exact ResolvedTyWF.tcons (hk _ hknown)
        (ResolvedTysWF.of_knownTypes_contains hk hargs)

/-- Types valid under the resolved judgment stay valid in a context registering at least the
    same constructors, at the same arities. -/
theorem ResolvedTysWF.of_knownTypes_contains {C C' : LContext T}
    {admissible : TyVarAdmissibility} {tys : LMonoTys}
    (hk : ∀ k, C.knownTypes.contains k = true → C'.knownTypes.contains k = true)
    (h : ResolvedTysWF C admissible tys) : ResolvedTysWF C' admissible tys := by
  cases h with
  | nil => exact ResolvedTysWF.nil
  | cons hhead htail =>
      exact ResolvedTysWF.cons (ResolvedTyWF.of_knownTypes_contains hk hhead)
        (ResolvedTysWF.of_knownTypes_contains hk htail)
end

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- A valid source type stays valid, with the same resolution, in a context registering at least
    the same constructors, at the same arities. -/
theorem SourceTyWF.of_knownTypes_contains {C C' : LContext T}
    {admissible : TyVarAdmissibility} {aliases : List TypeAlias} {ty resolved : LMonoTy}
    (hk : ∀ k, C.knownTypes.contains k = true → C'.knownTypes.contains k = true)
    (h : SourceTyWF C admissible aliases ty resolved) :
    SourceTyWF C' admissible aliases ty resolved :=
  ⟨h.hresolve, ResolvedTyWF.of_knownTypes_contains hk h.htype⟩

omit [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- A valid source type stays valid, with the same resolution, in a context with the same
    registered types. -/
theorem SourceTyWF.of_knownTypes_eq {C C' : LContext T} {admissible : TyVarAdmissibility}
    {aliases : List TypeAlias} {ty resolved : LMonoTy} (hk : C'.knownTypes = C.knownTypes)
    (h : SourceTyWF C admissible aliases ty resolved) :
    SourceTyWF C' admissible aliases ty resolved :=
  SourceTyWF.of_knownTypes_contains (fun _ hc => hk ▸ hc) h

mutual
/-- If a substituted type has only registered constructors, so does the substitution's image of
    each free type variable of the original type. -/
theorem knownInstance_subst_ftvar_of_mem (ks : KnownTypes) (S : Subst) (t : LMonoTy)
    (h : LMonoTy.knownInstance (LMonoTy.subst S t) ks = true) :
    ∀ v ∈ LMonoTy.freeVars t,
      LMonoTy.knownInstance (LMonoTy.subst S (.ftvar v)) ks = true := by
  match t with
  | .ftvar x =>
    intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    exact h
  | .bitvec _ =>
    intro v hv
    simp only [LMonoTy.freeVars, List.not_mem_nil] at hv
  | .tcons name args =>
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map] at h
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h
    intro v hv
    simp only [LMonoTy.freeVars] at hv
    exact knownInstances_subst_ftvar_of_mem ks S args h.2 v hv
termination_by sizeOf t

/-- If every substituted entry has only registered constructors, so does the substitution's
    image of each free type variable of the entries. -/
private theorem knownInstances_subst_ftvar_of_mem (ks : KnownTypes) (S : Subst) (ts : LMonoTys)
    (h : LMonoTys.knownInstances (ts.map (LMonoTy.subst S)) ks = true) :
    ∀ v ∈ LMonoTys.freeVars ts,
      LMonoTy.knownInstance (LMonoTy.subst S (.ftvar v)) ks = true := by
  match ts with
  | [] =>
    intro v hv
    simp only [LMonoTys.freeVars, List.not_mem_nil] at hv
  | t :: rest =>
    simp only [List.map_cons, LMonoTys.knownInstances] at h
    elim_err h with ht
    intro v hv
    rw [LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with hv | hv
    · exact knownInstance_subst_ftvar_of_mem ks S t ht v hv
    · exact knownInstances_subst_ftvar_of_mem ks S rest h v hv
termination_by sizeOf ts
end

mutual
/-- Every source monotype has an alias resolution. -/
theorem SourceTyResolves.exists (aliases : List TypeAlias) :
    ∀ t : LMonoTy, ∃ r, SourceTyResolves aliases t r
  | .ftvar _ => ⟨_, SourceTyResolves.ftvar⟩
  | .bitvec _ => ⟨_, SourceTyResolves.bitvec⟩
  | .tcons name args => by
    obtain ⟨rs, hrs⟩ := SourceTysResolve.exists aliases args
    cases hfind : aliases.find? (fun a => a.name == name && a.typeArgs.length == rs.length) with
    | none => exact ⟨_, SourceTyResolves.tcons hrs hfind⟩
    | some al => exact ⟨_, SourceTyResolves.alias hrs hfind⟩
termination_by t => sizeOf t

/-- Every list of source monotypes has an alias resolution. -/
theorem SourceTysResolve.exists (aliases : List TypeAlias) :
    ∀ ts : LMonoTys, ∃ rs, SourceTysResolve aliases ts rs
  | [] => ⟨[], SourceTysResolve.nil⟩
  | t :: ts => by
    obtain ⟨r, hr⟩ := SourceTyResolves.exists aliases t
    obtain ⟨rs, hrs⟩ := SourceTysResolve.exists aliases ts
    exact ⟨r :: rs, SourceTysResolve.cons hr hrs⟩
termination_by ts => sizeOf ts
end

mutual
/-- Alias resolution is deterministic: a source monotype has at most one resolution. -/
theorem SourceTyResolves.unique {aliases : List TypeAlias} {t r r' : LMonoTy}
    (h : SourceTyResolves aliases t r) (h' : SourceTyResolves aliases t r') : r = r' := by
  match h, h' with
  | .ftvar, .ftvar => rfl
  | .bitvec, .bitvec => rfl
  | .tcons hargs _, .tcons hargs' _ => rw [SourceTysResolve.unique hargs hargs']
  | .tcons hargs hfind, .alias hargs' hfind' =>
    rw [SourceTysResolve.unique hargs hargs', hfind'] at hfind
    cases hfind
  | .alias hargs hfind, .tcons hargs' hfind' =>
    rw [SourceTysResolve.unique hargs hargs', hfind'] at hfind
    cases hfind
  | .alias hargs hfind, .alias hargs' hfind' =>
    have hrs := SourceTysResolve.unique hargs hargs'
    subst hrs
    rw [hfind] at hfind'
    cases hfind'
    rfl

/-- Alias resolution of a monotype list is deterministic. -/
theorem SourceTysResolve.unique {aliases : List TypeAlias} {ts rs rs' : LMonoTys}
    (h : SourceTysResolve aliases ts rs) (h' : SourceTysResolve aliases ts rs') : rs = rs' := by
  match h, h' with
  | .nil, .nil => rfl
  | .cons hhead htail, .cons hhead' htail' =>
    rw [SourceTyResolves.unique hhead hhead', SourceTysResolve.unique htail htail']
end

mutual
/-- A source type is alias-equivalent to its resolution: the declarative resolution, which
    expands the first matching alias, is one of the rewritings `AliasEquiv` allows. -/
theorem SourceTyResolves.aliasEquiv {aliases : List TypeAlias} {t r : LMonoTy}
    (h : SourceTyResolves aliases t r) : AliasEquiv aliases t r := by
  cases h with
  | ftvar => exact AliasEquiv.refl
  | bitvec => exact AliasEquiv.refl
  | tcons hargs _ => exact AliasEquiv.cong_tcons hargs.aliasEquiv
  | alias hargs hfind =>
    rename_i name args resolvedArgs al
    have hmem := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact AliasEquiv.trans (AliasEquiv.cong_tcons hargs.aliasEquiv)
      (AliasEquiv.expand ⟨al, hmem, hp.1, hp.2, rfl⟩)

/-- Each member of a source type list is alias-equivalent to its resolution. -/
theorem SourceTysResolve.aliasEquiv {aliases : List TypeAlias} {ts rs : LMonoTys}
    (h : SourceTysResolve aliases ts rs) : AliasEquivList aliases ts rs := by
  cases h with
  | nil => exact AliasEquivList.nil
  | cons hh ht => exact AliasEquivList.cons hh.aliasEquiv ht.aliasEquiv
end

/-- The source checker accepts every valid source type: if `ty` is a valid source type with
    resolution `r` under the aliases of `Env`, then checking it returns `r` and leaves `Env`
    unchanged. -/
theorem LMonoTy.typeCheckSource_complete {C : LContext T} {Env : TEnv T.IDMeta}
    {admissible : TyVarAdmissibility} {ty r : LMonoTy}
    (h : SourceTyWF C admissible Env.context.aliases ty r) :
    LMonoTy.typeCheckSource ty C Env admissible = .ok (r, Env) := by
  obtain ⟨r', hres⟩ := LMonoTy.resolveAliases_isOk ty Env
  have hr : r' = r := SourceTyResolves.unique
    (LMonoTy.resolveAliases_sourceTyResolves ty Env r' Env hres) h.hresolve
  subst hr
  have hfree : r'.freeVars.all admissible = true := List.all_eq_true.mpr h.htype.admissible
  simp only [LMonoTy.typeCheckSource, LMonoTy.typeCheckResolved, bind, Except.bind, hres,
    hfree, h.htype.knownInstance, Bool.not_true]
  rfl

mutual
/-- Alias resolution commutes with substitution: if `t` resolves to `r` and `S` sends each free
    variable of `t` to a type resolving to its `τ`-image, then `S t` resolves to `τ r`. -/
theorem SourceTyResolves.subst₂ {aliases : List TypeAlias}
    (hclosed : ∀ al ∈ aliases, ∀ tv ∈ LMonoTy.freeVars al.type, tv ∈ al.typeArgs)
    (S τ : Subst) {t r : LMonoTy} (h : SourceTyResolves aliases t r)
    (hS : ∀ v ∈ LMonoTy.freeVars t,
      SourceTyResolves aliases (LMonoTy.subst S (.ftvar v)) (LMonoTy.subst τ (.ftvar v))) :
    SourceTyResolves aliases (LMonoTy.subst S t) (LMonoTy.subst τ r) := by
  match h with
  | .ftvar (v := v) =>
    exact hS v (by simp only [LMonoTy.freeVars, List.mem_singleton])
  | .bitvec (n := n) =>
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
    exact SourceTyResolves.bitvec
  | .tcons (name := name) (args := args) (resolvedArgs := resolvedArgs) hargs hfind =>
    rw [LMonoTy.subst_tcons, LMonoTy.subst_tcons, LMonoTys.subst_eq_map, LMonoTys.subst_eq_map]
    refine SourceTyResolves.tcons (SourceTysResolve.subst₂ hclosed S τ hargs ?_) ?_
    · intro v hv
      exact hS v (by simpa only [LMonoTy.freeVars] using hv)
    · rw [List.length_map]
      exact hfind
  | .alias (name := name) (args := args) (resolvedArgs := resolvedArgs) (alias := al)
      hargs hfind =>
    have hmem : al ∈ aliases := List.mem_of_find?_eq_some hfind
    have hsel := List.find?_some hfind
    simp only [Bool.and_eq_true, beq_iff_eq] at hsel
    have hexpand : LMonoTy.subst τ (al.expand resolvedArgs) =
        al.expand (resolvedArgs.map (LMonoTy.subst τ)) := by
      simp only [TypeAlias.expand]
      exact LExpr.subst_openVars_comm τ al.typeArgs resolvedArgs al.type (hclosed al hmem) hsel.2
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map, hexpand]
    refine SourceTyResolves.alias (SourceTysResolve.subst₂ hclosed S τ hargs ?_) ?_
    · intro v hv
      exact hS v (by simpa only [LMonoTy.freeVars] using hv)
    · rw [List.length_map]
      exact hfind

/-- If `S` sends each free variable of a monotype list to a type resolving to its `τ`-image, `S`
    of the list resolves to `τ` of its resolution. -/
theorem SourceTysResolve.subst₂ {aliases : List TypeAlias}
    (hclosed : ∀ al ∈ aliases, ∀ tv ∈ LMonoTy.freeVars al.type, tv ∈ al.typeArgs)
    (S τ : Subst) {ts rs : LMonoTys} (h : SourceTysResolve aliases ts rs)
    (hS : ∀ v ∈ LMonoTys.freeVars ts,
      SourceTyResolves aliases (LMonoTy.subst S (.ftvar v)) (LMonoTy.subst τ (.ftvar v))) :
    SourceTysResolve aliases (ts.map (LMonoTy.subst S)) (rs.map (LMonoTy.subst τ)) := by
  match h with
  | .nil => exact SourceTysResolve.nil
  | .cons (head := head) (tail := tail) hhead htail =>
    refine SourceTysResolve.cons (SourceTyResolves.subst₂ hclosed S τ hhead ?_)
      (SourceTysResolve.subst₂ hclosed S τ htail ?_)
    · intro v hv
      exact hS v (by rw [LMonoTys.freeVars_of_cons]; exact List.mem_append_left _ hv)
    · intro v hv
      exact hS v (by rw [LMonoTys.freeVars_of_cons]; exact List.mem_append_right _ hv)
end

/-- Alias resolution commutes with a substitution sending each free variable of the source type
    to a type that resolves to itself. -/
theorem SourceTyResolves.subst {aliases : List TypeAlias}
    (hclosed : ∀ al ∈ aliases, ∀ tv ∈ LMonoTy.freeVars al.type, tv ∈ al.typeArgs)
    (S : Subst) {t r : LMonoTy} (h : SourceTyResolves aliases t r)
    (hS : ∀ v ∈ LMonoTy.freeVars t,
      SourceTyResolves aliases (LMonoTy.subst S (.ftvar v)) (LMonoTy.subst S (.ftvar v))) :
    SourceTyResolves aliases (LMonoTy.subst S t) (LMonoTy.subst S r) :=
  SourceTyResolves.subst₂ hclosed S S h hS

/-- If each entry of the first list is valid under the resolved judgment whenever the
    corresponding entry of the second is, then the first list is valid whenever the second is. -/
private theorem ResolvedTysWF.of_zip {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} :
    ∀ {as bs : LMonoTys}, as.length = bs.length →
      (∀ p ∈ List.zip as bs, ResolvedTyWF C adm p.2 → ResolvedTyWF C adm p.1) →
      ResolvedTysWF C adm bs → ResolvedTysWF C adm as
  | [], _, _, _, _ => ResolvedTysWF.nil
  | _ :: _, [], hlen, _, _ => absurd hlen (by simp)
  | a :: as, b :: bs, hlen, hab, h => by
    cases h with
    | cons hhead htail =>
      exact ResolvedTysWF.cons (hab (a, b) List.mem_cons_self hhead)
        (ResolvedTysWF.of_zip
          (by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hlen)
          (fun p hp => hab p (List.mem_cons_of_mem _ hp)) htail)

mutual
/-- If each value is valid under the resolved judgment whenever its counterpart in a second list
    is, opening a type with the first list gives a valid type whenever the second does. -/
private theorem ResolvedTyWF.openVars_of_zip {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} (vars : List TyIdentifier) {vals vals' : LMonoTys}
    (hlen : vals.length = vals'.length)
    (hvals : ∀ p ∈ List.zip vals vals', ResolvedTyWF C adm p.2 → ResolvedTyWF C adm p.1)
    (t : LMonoTy) (h : ResolvedTyWF C adm (LMonoTy.openVars vars vals' t)) :
    ResolvedTyWF C adm (LMonoTy.openVars vars vals t) := by
  match t with
  | .ftvar x => exact LMonoTy.openVars_ftvar_of_zip (ResolvedTyWF C adm) x vars hlen hvals h
  | .bitvec _ =>
    simp only [LMonoTy.openVars_bitvec]
    exact ResolvedTyWF.bitvec
  | .tcons name args =>
    rw [LMonoTy.openVars_tcons] at h ⊢
    cases h with
    | tcons hknown hargs =>
      refine ResolvedTyWF.tcons ?_
        (ResolvedTysWF.openVars_of_zip vars hlen hvals args hargs)
      simpa only [openVars_length] using hknown
termination_by sizeOf t

/-- If each value is valid under the resolved judgment whenever its counterpart in a second list
    is, opening a type list with the first list gives valid types whenever the second does. -/
private theorem ResolvedTysWF.openVars_of_zip {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} (vars : List TyIdentifier) {vals vals' : LMonoTys}
    (hlen : vals.length = vals'.length)
    (hvals : ∀ p ∈ List.zip vals vals', ResolvedTyWF C adm p.2 → ResolvedTyWF C adm p.1)
    (ts : LMonoTys) (h : ResolvedTysWF C adm (LMonoTys.openVars vars vals' ts)) :
    ResolvedTysWF C adm (LMonoTys.openVars vars vals ts) := by
  match ts with
  | [] =>
    simp only [LMonoTys.openVars]
    exact ResolvedTysWF.nil
  | t :: rest =>
    simp only [LMonoTys.openVars] at h ⊢
    cases h with
    | cons hhead htail =>
      exact ResolvedTysWF.cons (ResolvedTyWF.openVars_of_zip vars hlen hvals t hhead)
        (ResolvedTysWF.openVars_of_zip vars hlen hvals rest htail)
termination_by sizeOf ts
end

mutual
/-- A type resolves whenever its image under `S` does, with a valid resolution whenever the
    image's is, provided each of its variables is admissible or renamed by `S` to a variable whose
    admissibility implies its own. -/
theorem SourceTyResolves.of_renaming {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} {aliases : List TypeAlias} (S : Subst) (t : LMonoTy) {r' : LMonoTy}
    (hS : ∀ v ∈ LMonoTy.freeVars t, adm v = true ∨
      ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true))
    (h : SourceTyResolves aliases (LMonoTy.subst S t) r') :
    ∃ r, SourceTyResolves aliases t r ∧
      (ResolvedTyWF C adm r' → ResolvedTyWF C adm r) := by
  match t with
  | .ftvar v =>
    rcases hS v (by simp only [LMonoTy.freeVars, List.mem_singleton]) with hadm | ⟨w, hw, hadm⟩
    · exact ⟨.ftvar v, SourceTyResolves.ftvar, fun _ => ResolvedTyWF.ftvar hadm⟩
    rw [hw] at h
    cases h
    refine ⟨.ftvar v, SourceTyResolves.ftvar, fun hr => ?_⟩
    cases hr with
    | ftvar hw' => exact ResolvedTyWF.ftvar (hadm hw')
  | .bitvec n => exact ⟨.bitvec n, SourceTyResolves.bitvec, fun _ => ResolvedTyWF.bitvec⟩
  | .tcons name args =>
    have hSargs : ∀ v ∈ LMonoTys.freeVars args, adm v = true ∨
        ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true) := by
      intro v hv
      exact hS v (by simpa only [LMonoTy.freeVars] using hv)
    rw [LMonoTy.subst_tcons, LMonoTys.subst_eq_map] at h
    cases h with
    | tcons hargs hfind =>
      obtain ⟨rs, hrs, hlen, hrel⟩ := SourceTysResolve.of_renaming (C := C) S args hSargs hargs
      refine ⟨.tcons name rs, SourceTyResolves.tcons hrs ?_, ?_⟩
      · rw [hlen]
        exact hfind
      · intro hr
        cases hr with
        | tcons hknown hargsTy =>
          refine ResolvedTyWF.tcons ?_ (ResolvedTysWF.of_zip hlen hrel hargsTy)
          rw [hlen]
          exact hknown
    | alias hargs hfind =>
      rename_i resolvedArgs al
      obtain ⟨rs, hrs, hlen, hrel⟩ := SourceTysResolve.of_renaming (C := C) S args hSargs hargs
      refine ⟨al.expand rs, SourceTyResolves.alias hrs ?_, ?_⟩
      · rw [hlen]
        exact hfind
      · intro hr
        exact ResolvedTyWF.openVars_of_zip al.typeArgs hlen hrel al.type hr
termination_by sizeOf t

/-- List form of `SourceTyResolves.of_renaming`: the resolutions have the image's length and are
    valid pointwise whenever the image's are. -/
theorem SourceTysResolve.of_renaming {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} {aliases : List TypeAlias} (S : Subst) (ts : LMonoTys)
    {rs' : LMonoTys}
    (hS : ∀ v ∈ LMonoTys.freeVars ts, adm v = true ∨
      ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true))
    (h : SourceTysResolve aliases (ts.map (LMonoTy.subst S)) rs') :
    ∃ rs, SourceTysResolve aliases ts rs ∧ rs.length = rs'.length ∧
      ∀ p ∈ List.zip rs rs', ResolvedTyWF C adm p.2 → ResolvedTyWF C adm p.1 := by
  match ts with
  | [] =>
    cases h
    exact ⟨[], SourceTysResolve.nil, rfl, fun p hp => absurd hp (by simp)⟩
  | t :: rest =>
    rw [List.map_cons] at h
    cases h with
    | cons hhead htail =>
      have hSt : ∀ v ∈ LMonoTy.freeVars t, adm v = true ∨
          ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true) := by
        intro v hv
        exact hS v (by simp only [LMonoTys.freeVars, List.mem_append]; exact Or.inl hv)
      have hSrest : ∀ v ∈ LMonoTys.freeVars rest, adm v = true ∨
          ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true) := by
        intro v hv
        exact hS v (by simp only [LMonoTys.freeVars, List.mem_append]; exact Or.inr hv)
      obtain ⟨r, hr, hk⟩ := SourceTyResolves.of_renaming (C := C) S t hSt hhead
      obtain ⟨rs, hrs, hlen, hrel⟩ := SourceTysResolve.of_renaming (C := C) S rest hSrest htail
      refine ⟨r :: rs, SourceTysResolve.cons hr hrs, by simp only [List.length_cons, hlen], ?_⟩
      intro p hp
      rw [List.zip_cons_cons, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hk
      · exact hrel p hp
termination_by sizeOf ts
end

/-- A type is a valid source type whenever its image under `S` is, provided each of its type
    variables is admissible or renamed by `S` to a variable whose admissibility implies its own. -/
theorem SourceTyWF.of_renaming {T : LExprParams} {C : LContext T}
    {adm : TyVarAdmissibility} {aliases : List TypeAlias} (S : Subst) {t r' : LMonoTy}
    (hS : ∀ v ∈ LMonoTy.freeVars t, adm v = true ∨
      ∃ w, LMonoTy.subst S (.ftvar v) = .ftvar w ∧ (adm w = true → adm v = true))
    (h : SourceTyWF C adm aliases (LMonoTy.subst S t) r') :
    ∃ r, SourceTyWF C adm aliases t r := by
  obtain ⟨r, hr, hk⟩ := SourceTyResolves.of_renaming (C := C) S t hS h.hresolve
  exact ⟨r, hr, hk h.htype⟩

/-- Under the unrestricted variable policy, a type is a valid source type whenever its image under
    a substitution is. -/
theorem SourceTyWF.of_subst {T : LExprParams} {C : LContext T} {aliases : List TypeAlias}
    (S : Subst) {t r' : LMonoTy}
    (h : SourceTyWF C TyVarAdmissibility.all aliases (LMonoTy.subst S t) r') :
    ∃ r, SourceTyWF C TyVarAdmissibility.all aliases t r :=
  SourceTyWF.of_renaming S (fun _ _ => Or.inl rfl) h

mutual
/-- Opening a type with only registered constructors by values with only registered constructors
    gives a type with only registered constructors. -/
private theorem knownInstance_openVars_of_known {ks : KnownTypes} (vars : List TyIdentifier)
    {vals : LMonoTys} (hvals : ∀ v ∈ vals, LMonoTy.knownInstance v ks = true)
    (t : LMonoTy) (h : LMonoTy.knownInstance t ks = true) :
    LMonoTy.knownInstance (LMonoTy.openVars vars vals t) ks = true := by
  match t with
  | .ftvar x =>
    rw [LMonoTy.openVars_ftvar]
    split
    · rename_i p v hfind
      exact hvals v (List.of_mem_zip (List.mem_of_find?_eq_some hfind)).2
    · simp only [LMonoTy.knownInstance]
  | .bitvec _ => simp only [LMonoTy.openVars_bitvec, LMonoTy.knownInstance]
  | .tcons name args =>
    rw [LMonoTy.openVars_tcons]
    simp only [LMonoTy.knownInstance, Bool.and_eq_true, openVars_length] at h ⊢
    exact ⟨h.1, knownInstances_openVars_of_known vars hvals args h.2⟩
termination_by sizeOf t

/-- Opening a list of types with only registered constructors by values with only registered
    constructors gives types with only registered constructors. -/
private theorem knownInstances_openVars_of_known {ks : KnownTypes} (vars : List TyIdentifier)
    {vals : LMonoTys} (hvals : ∀ v ∈ vals, LMonoTy.knownInstance v ks = true)
    (ts : LMonoTys) (h : LMonoTys.knownInstances ts ks = true) :
    LMonoTys.knownInstances (LMonoTys.openVars vars vals ts) ks = true := by
  match ts with
  | [] => simp only [LMonoTys.openVars, LMonoTys.knownInstances]
  | t :: rest =>
    simp only [LMonoTys.openVars, LMonoTys.knownInstances] at h ⊢
    elim_err h with ht
    rw [ite_eq_left (knownInstance_openVars_of_known vars hvals t ht)]
    exact knownInstances_openVars_of_known vars hvals rest h
termination_by sizeOf ts
end

mutual
/-- A type with only registered constructors resolves, against aliases whose bodies have only
    registered constructors, to a type with only registered constructors. -/
private theorem SourceTyResolves.exists_knownInstance {aliases : List TypeAlias} {ks : KnownTypes}
    (hbodies : ∀ al ∈ aliases, LMonoTy.knownInstance al.type ks = true)
    (t : LMonoTy) (h : LMonoTy.knownInstance t ks = true) :
    ∃ r, SourceTyResolves aliases t r ∧ LMonoTy.knownInstance r ks = true := by
  match t with
  | .ftvar v => exact ⟨.ftvar v, SourceTyResolves.ftvar, rfl⟩
  | .bitvec n => exact ⟨.bitvec n, SourceTyResolves.bitvec, rfl⟩
  | .tcons name args =>
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h
    obtain ⟨rs, hrs, hlen, hknown⟩ := SourceTysResolve.exists_knownInstance hbodies args h.2
    cases hfind : aliases.find? (fun a => a.name == name && a.typeArgs.length == rs.length) with
    | none =>
      refine ⟨.tcons name rs, SourceTyResolves.tcons hrs hfind, ?_⟩
      simp only [LMonoTy.knownInstance, Bool.and_eq_true]
      exact ⟨by rw [hlen]; exact h.1, LMonoTys.knownInstances_of_forall hknown⟩
    | some al =>
      refine ⟨al.expand rs, SourceTyResolves.alias hrs hfind, ?_⟩
      exact knownInstance_openVars_of_known al.typeArgs hknown al.type
        (hbodies al (List.mem_of_find?_eq_some hfind))
termination_by sizeOf t

/-- Types with only registered constructors resolve, against aliases whose bodies have only
    registered constructors, to types with only registered constructors. -/
private theorem SourceTysResolve.exists_knownInstance {aliases : List TypeAlias} {ks : KnownTypes}
    (hbodies : ∀ al ∈ aliases, LMonoTy.knownInstance al.type ks = true)
    (ts : LMonoTys) (h : LMonoTys.knownInstances ts ks = true) :
    ∃ rs, SourceTysResolve aliases ts rs ∧ rs.length = ts.length ∧
      ∀ r ∈ rs, LMonoTy.knownInstance r ks = true := by
  match ts with
  | [] => exact ⟨[], SourceTysResolve.nil, rfl, fun r hr => absurd hr (by simp)⟩
  | t :: rest =>
    simp only [LMonoTys.knownInstances] at h
    elim_err h with ht
    obtain ⟨r, hr, hk⟩ := SourceTyResolves.exists_knownInstance hbodies t ht
    obtain ⟨rs, hrs, hlen, hks⟩ := SourceTysResolve.exists_knownInstance hbodies rest h
    refine ⟨r :: rs, SourceTysResolve.cons hr hrs, by simp only [List.length_cons, hlen], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hk
    · exact hks x hx
termination_by sizeOf ts
end

/-- A successful monotype `instantiateWithCheck` keeps the substitution and returns a type whose
    constructors are all registered at their arities. -/
theorem LMonoTy_instantiateWithCheck_subst_knownInstance
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (r : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (r, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo ∧ LMonoTy.knownInstance r C.knownTypes = true := by
  simp only [LMonoTy.instantiateWithCheck] at h
  elim_err h with instTypes Env1 h_inst
  simp only [Bind.bind, Except.bind] at h
  elim_err h with v2 h_res
  obtain ⟨mtyi, Env2⟩ := v2
  dsimp only [Bool.not_eq_eq_eq_not, Bool.not_true] at h
  elim_err h
  elim_err h with h_known
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have h_subst_eq : Env1.stateSubstInfo = Env.stateSubstInfo := by
    simp only [LMonoTys.instantiateEnv] at h_inst
    elim_err h_inst
    simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
    obtain ⟨_, h_env⟩ := h_inst
    rw [← h_env]
  refine ⟨?_, ?_⟩
  · rw [← h2, ← h_subst_eq, LMonoTy.resolveAliases_env_eq _ Env1 mtyi Env2 h_res]
  · rw [← h1]
    simpa [isInstanceOfKnownType] using h_known

/-- Resolving the aliases of a type scheme keeps the substitution. -/
private theorem LTy_resolveAliases_subst_eq
    (ty : LTy) (Env : TEnv T.IDMeta) (mty : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LTy.resolveAliases ty Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo := by
  simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h with v1 h_inst
  obtain ⟨mty0, genEnv1⟩ := v1
  dsimp only at h
  rw [LMonoTy.resolveAliases_env_eq mty0 _ mty Env' h]

/-- A successful type-scheme `instantiateWithCheck` keeps the substitution and
    returns a type whose constructors are all registered at their arities. -/
theorem LTy_instantiateWithCheck_subst_knownInstance
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (mty : LMonoTy)
    (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (mty, Env')) :
    Env'.stateSubstInfo = Env.stateSubstInfo ∧
      LMonoTy.knownInstance mty C.knownTypes = true := by
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h with v1 h_res
  obtain ⟨mty0, Env1⟩ := v1
  dsimp only [Bool.not_eq_eq_eq_not, Bool.not_true, pure, Except.pure] at h
  elim_err h
  elim_err h with h_known
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩
  · rw [← h2]
    exact LTy_resolveAliases_subst_eq ty Env mty0 Env1 h_res
  · rw [← h1]
    simpa [isInstanceOfKnownType] using h_known

/-- A successful checked scheme instantiation is a registered instance. -/
theorem LTy_instantiateWithCheck_knownInstance
    (ty : LTy) (C : LContext T) (Env : TEnv T.IDMeta) (r : LMonoTy)
    (Env' : TEnv T.IDMeta)
    (h : LTy.instantiateWithCheck ty C Env = .ok (r, Env')) :
    LMonoTy.knownInstance r C.knownTypes = true :=
  (LTy_instantiateWithCheck_subst_knownInstance ty C Env r Env' h).2

/-- Instantiating a monotype returns a type whose constructors are all registered at their
    arities. -/
theorem LMonoTy_instantiateWithCheck_knownInstance
    (mty_in : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (r : LMonoTy) (Env' : TEnv T.IDMeta)
    (h : LMonoTy.instantiateWithCheck mty_in C Env = .ok (r, Env')) :
    LMonoTy.knownInstance r C.knownTypes = true :=
  (LMonoTy_instantiateWithCheck_subst_knownInstance mty_in C Env r Env' h).2

/-- A monotype accepted by `instantiateWithCheck` is a valid source type under the unrestricted
    variable policy. Proved by commuting alias resolution with the check's variable renaming. -/
theorem LMonoTy.instantiateWithCheck_sourceTyWF
    (t : LMonoTy) (C : LContext T) (Env : TEnv T.IDMeta) (r : LMonoTy) (Env' : TEnv T.IDMeta)
    (haWF : TContext.AliasesWF Env.context)
    (h : LMonoTy.instantiateWithCheck t C Env = .ok (r, Env')) :
    ∃ r0, SourceTyWF C TyVarAdmissibility.all Env.context.aliases t r0 := by
  have hknown := LMonoTy_instantiateWithCheck_knownInstance t C Env r Env' h
  obtain ⟨tI, EnvI, EnvR, hI, hR⟩ := LMonoTy.instantiateWithCheck_decompose t C Env r Env' h
  obtain ⟨S, hSftvar, hmtys, hctx⟩ := LMonoTys.instantiateEnv_subst _ [t] Env [tI] EnvI hI
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmtys
  obtain ⟨r0, hr0⟩ := LMonoTy.resolveAliases_isOk t EnvI
  have haWF' : TContext.AliasesWF EnvI.context := by rw [hctx]; exact haWF
  rw [hmtys] at hR
  have hcomm : r = LMonoTy.subst S r0 :=
    LMonoTy.resolveAliases_subst_comm S t EnvI r0 r EnvI EnvR haWF' hSftvar hr0 hR
  have hk0 : r0.knownInstance C.knownTypes = true := by
    have hk : (LMonoTy.subst S r0).knownInstance C.knownTypes = true := by
      rw [← hcomm]; exact hknown
    exact knownInstance_of_subst C.knownTypes S r0 hk
  have hres := LMonoTy.resolveAliases_sourceTyResolves t EnvI r0 EnvI hr0
  rw [hctx] at hres
  exact ⟨r0, hres, ResolvedTyWF.of_knownInstance hk0⟩

/-- Registering an alias requires a well-formed alias (distinct parameters that are exactly the
    free variables of its body) whose body is a valid source type, and stores the body's
    resolution. -/
theorem TEnv.addTypeAlias_sourceTyWF {T : LExprParams}
    [DecidableEq T.IDMeta] [Hashable T.IDMeta] [Std.ToFormat T.IDMeta]
    (al : TypeAlias) (C : LContext T) (Env Env' : TEnv T.IDMeta)
    (h : TEnv.addTypeAlias al C Env = .ok Env') :
    al.WF ∧
    ∃ storedTy,
      SourceTyWF C TyVarAdmissibility.all Env.context.aliases al.type storedTy ∧
      Env'.context.aliases
        = { typeArgs := al.typeArgs, name := al.name, type := storedTy } ::
            Env.context.aliases := by
  obtain ⟨hnodup, hclosed, hused, -, -, storedTy, EnvA, -, haliases, -, -, -, hsource⟩ :=
    addTypeAlias_decompose al C Env Env' h
  have hwf : al.WF := ⟨fun v => ⟨hclosed v, hused v⟩, hnodup⟩
  exact ⟨hwf, storedTy, LMonoTy.typeCheckSource_sound
    al.type storedTy C Env EnvA TyVarAdmissibility.all hsource, haliases⟩

end

end Lambda
