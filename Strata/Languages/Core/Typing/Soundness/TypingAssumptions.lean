/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Identifiers
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
public import Strata.Languages.Core.Typing.Props.ProcSigAgreementProps
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Denote.LExprAnnotatedProps
import Strata.DL.Lambda.FactoryProps
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.DL.Lambda.LExprTypeSpec

/-! ## Assumptions used by Core typechecker soundness
The Core environment conditions the soundness theorems state, with lemmas that carry them across
context changes. Key definitions: `NoSkolemAmbient`, `AliasBodiesKnown`, `AmbientTypesKnown`,
`AliasRegistryCoherent`, `ProcSigsDeclared`, `ConstTysFixed` and `ScopeRigid`. -/

public section

namespace Core

open Lambda Imperative

/-- Deskolemizing by `σ` fixes every alias body of `aliases` and keeps every alias head. -/
def AliasesNoSkolem (σ : RigidNames) (aliases : List TypeAlias) : Prop :=
  ∀ al ∈ aliases, deskolemizeTy σ al.type = al.type ∧
    ∀ args, deskolemizeTy σ (.tcons al.name args)
      = .tcons al.name (args.map (deskolemizeTy σ))

/-- The visible variable schemes, aliases, and function signatures are unchanged by
    deskolemization under the rigid-name mapping `σ`. -/
structure NoSkolemAmbient (C : Expression.TyContext) (Γ : TContext Unit)
    (σ : RigidNames) : Prop where
  ctxTypes : ∀ z ty, Γ.types.find? z = some ty → mapLTyTys (deskolemizeTy σ) ty = ty
  /-- Every alias body and alias application is unchanged by deskolemization. -/
  aliases : AliasesNoSkolem σ Γ.aliases
  functions : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
    C.functions[nm]? = some f → f.type = .ok ty → mapLTyTys (deskolemizeTy σ) ty = ty

/-- Every stored alias body is an instance of the context's registered types. -/
def AliasBodiesKnown (C : Expression.TyContext) (Γ : TContext Unit) : Prop :=
  ∀ al ∈ Γ.aliases, LMonoTy.knownInstance al.type C.knownTypes = true

/-- A step that keeps the alias list and only grows the registered-type table keeps every alias
    body an instance of a registered type. -/
theorem AliasBodiesKnown.of_extends (C C' : Expression.TyContext) (Γ Ξ : TContext Unit)
    (hal : Ξ.aliases = Γ.aliases)
    (hext : KnownTypesExtends C.knownTypes C'.knownTypes)
    (hbodies : AliasBodiesKnown C Γ) : AliasBodiesKnown C' Ξ := by
  intro al hmem
  rw [hal] at hmem
  exact Lambda.knownInstance_mono al.type C.knownTypes C'.knownTypes hext (hbodies al hmem)

/-- Alias bodies that are registered instances mention no alias when no alias name is
    registered. -/
theorem AliasBodiesKnown.aliasesResolved {C : Expression.TyContext} {Γ : TContext Unit}
    (hfresh : ∀ al ∈ Γ.aliases, C.knownTypes.containsName al.name = false)
    (hbodies : AliasBodiesKnown C Γ) : TContext.AliasesResolved Γ :=
  fun al hal => aliasFree_of_knownInstance C.knownTypes Γ.aliases hfresh al.type (hbodies al hal)

/-- Every ambient variable's type, with its aliases resolved, is an instance of registered types. -/
def AmbientTypesKnown (ks : Lambda.KnownTypes) (Env : Expression.TyEnv) : Prop :=
  ∀ x vs mty, Env.context.types.find? x = some (.forAll vs mty) →
    LMonoTy.knownInstance (Env.context.resolveTy mty) ks = true

/-- Registered ambient types stay registered in a lookup-equal scope and a larger table. -/
theorem AmbientTypesKnown.of_findEq {ks ks' : Lambda.KnownTypes} {Env Env2 : Expression.TyEnv}
    (hfe : TContext.FindEq (T := CoreLParams) Env2.context Env.context)
    (hext : KnownTypesExtends ks ks') (h : AmbientTypesKnown ks Env) :
    AmbientTypesKnown ks' Env2 := by
  intro x vs mty hx
  rw [hfe.find? x] at hx
  rw [TContext.resolveTy_congr (T := CoreLParams) hfe.2]
  exact knownInstance_mono _ ks ks' hext (h x vs mty hx)

/-- Registered ambient types stay registered when the aliases are freshly extended by names the
    table does not register, keeping the types. -/
theorem AmbientTypesKnown.of_FreshExtension {ks : Lambda.KnownTypes} {Env Env2 : Expression.TyEnv}
    (htypes : Env2.context.types = Env.context.types)
    (hext : TypeAlias.FreshExtension Env.context.aliases Env2.context.aliases)
    (hnew : ∀ al ∈ Env2.context.aliases, al ∉ Env.context.aliases →
      KnownTypes.containsName ks al.name = false)
    (h : AmbientTypesKnown ks Env) : AmbientTypesKnown ks Env2 := by
  intro x vs mty hx
  rw [htypes] at hx
  rw [TContext.resolveTy_eq_of_FreshExtension (T := CoreLParams) hext hnew (h x vs mty hx)]
  exact h x vs mty hx

/-- Environments with the same type scope have the same registered ambient types. -/
theorem AmbientTypesKnown.of_context_eq {ks : Lambda.KnownTypes} {Env Env' : Expression.TyEnv}
    (h : Env'.context = Env.context) (hk : AmbientTypesKnown ks Env) :
    AmbientTypesKnown ks Env' := by
  unfold AmbientTypesKnown
  rw [h]
  exact hk

/-- Every stored alias is present in the declared-name registry and absent from the registered
    type constructors. -/
structure AliasRegistryCoherent (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) : Prop where
  declared : ∀ al ∈ Env.context.aliases, al.name ∈ i
  freshForKnownTypes : ∀ al ∈ Env.context.aliases, al.name ∉ C.knownTypes

/-- If every alias is in a declared-name registry and none is a registered type constructor, the
    same holds for any registry containing that one. -/
theorem AliasRegistryCoherent.of_idents_mem
    {C : Expression.TyContext} {Env : Expression.TyEnv} {i j : Identifiers Unit}
    (h : ∀ n : String, n ∈ i → n ∈ j)
    (hc : AliasRegistryCoherent C Env i) : AliasRegistryCoherent C Env j :=
  ⟨fun al hal => h al.name (hc.declared al hal), hc.freshForKnownTypes⟩

/-- If every alias is in a declared-name registry and none is a registered type constructor, the
    same holds for any context with the same registered types. -/
theorem AliasRegistryCoherent.of_knownTypes_eq
    {C D : Expression.TyContext} {Env : Expression.TyEnv} {i : Identifiers Unit}
    (h : D.knownTypes = C.knownTypes)
    (hc : AliasRegistryCoherent C Env i) : AliasRegistryCoherent D Env i :=
  ⟨hc.declared, fun al hal => by rw [h]; exact hc.freshForKnownTypes al hal⟩

/-- Replacing a context's own identifier registry keeps every alias declared in `i` and out of
    the registered type constructors. -/
theorem AliasRegistryCoherent.setIdents {C : Expression.TyContext} {Env : Expression.TyEnv}
    {i : Identifiers Unit} (j : Identifiers Unit)
    (hc : AliasRegistryCoherent C Env i) :
    AliasRegistryCoherent { C with idents := j } Env i :=
  AliasRegistryCoherent.of_knownTypes_eq (C := C) (D := { C with idents := j }) rfl hc

/-- If every alias of an environment is in a declared-name registry and none is a registered
    type constructor, the same holds for any environment with the same alias list. -/
theorem AliasRegistryCoherent.of_aliases_eq
    {C : Expression.TyContext} {Env Env2 : Expression.TyEnv} {i : Identifiers Unit}
    (h : Env2.context.aliases = Env.context.aliases)
    (hc : AliasRegistryCoherent C Env i) : AliasRegistryCoherent C Env2 i :=
  ⟨fun al hal => hc.declared al (h ▸ hal), fun al hal => hc.freshForKnownTypes al (h ▸ hal)⟩

/-- The free type variables of every procedure signature in `P` are among its type parameters. -/
@[expose] def ProcSigsDeclared (P : Program) : Prop :=
  ∀ nm proc, Program.Procedure.find? P nm = some proc → proc.header.SigDeclared

/-! ## Procedure signatures resolved against aliases -/

/-- `q` with its parameter types alias-resolved against `Γ`. -/
@[expose] def Procedure.resolveSig (Γ : TContext Unit) (q : Procedure) : Procedure :=
  { q with header := { q.header with
      inputs := Γ.resolveSig q.header.inputs, outputs := Γ.resolveSig q.header.outputs } }

/-- `d` with its parameter types alias-resolved against `Γ` when it declares a procedure. -/
@[expose] def Decl.resolveSig (Γ : TContext Unit) : Decl → Decl
  | .proc q md => .proc (q.resolveSig Γ) md
  | d => d

/-- `P` with the parameter types of every procedure alias-resolved against `aliases`. -/
@[expose] def Program.resolveSigs (aliases : List TypeAlias) (P : Program) : Program :=
  { P with decls := P.decls.map (Decl.resolveSig { aliases := aliases }) }

/-- Resolving a procedure's signature resolves its inputs. -/
theorem Procedure.resolveSig_inputs (Γ : TContext Unit) (q : Procedure) :
    (q.resolveSig Γ).header.inputs = Γ.resolveSig q.header.inputs := rfl

/-- Resolving a procedure's signature resolves its outputs. -/
theorem Procedure.resolveSig_outputs (Γ : TContext Unit) (q : Procedure) :
    (q.resolveSig Γ).header.outputs = Γ.resolveSig q.header.outputs := rfl

/-- Resolving a declaration's signature keeps its kind. -/
theorem Decl.resolveSig_kind (Γ : TContext Unit) (d : Decl) :
    (d.resolveSig Γ).kind = d.kind := by
  cases d <;> rfl

/-- Resolving a declaration's signature keeps its name. -/
theorem Decl.resolveSig_name (Γ : TContext Unit) (d : Decl) :
    (d.resolveSig Γ).name = d.name := by
  cases d <;> rfl

/-- Resolving a declaration's signature keeps the names it declares. -/
private theorem Decl.resolveSig_names (Γ : TContext Unit) (d : Decl) :
    (d.resolveSig Γ).names = d.names := by
  cases d <;> rfl

/-- Resolving a program's procedure signatures keeps its declaration names. -/
theorem Program.resolveSigs_getNames (A : List TypeAlias) (P : Program) :
    (P.resolveSigs A).getNames = P.getNames := by
  simp only [Program.resolveSigs, Program.getNames, Program.getNames.go, List.flatMap_map,
    Decl.resolveSig_names]

/-- Every rigid constant of `σ` starts with `skolemPrefix`. -/
def RigidNamesPrefixed (σ : RigidNames) : Prop :=
  ∀ p ∈ σ, ∃ s, p.2 = skolemPrefix ++ s

/-- No rigid constant of `σ` is a type name registered in `known`. -/
def RigidNamesFresh (known : Lambda.KnownTypes) (σ : RigidNames) : Prop :=
  ∀ p ∈ σ, p.2 ∉ known

/-- No literal of `e` has a type that names a rigid constant of `σ`, so deskolemization by `σ`
    leaves every literal's type unchanged. -/
def ConstTysFixed (σ : RigidNames) (e : LExpr CoreLParams.mono) : Prop :=
  ∀ c ∈ LExpr.getConsts e, deskolemizeTy σ c.ty = c.ty

/-- `σ` is a rigid renaming of the type parameters `typeArgs` of a definition checked in `C` and
    `Env`: it names exactly `typeArgs`, in order, with distinct rigid-prefixed constants that are
    not registered types, not type names in scope and not among `extra`. -/
structure ScopeRigid (C : Expression.TyContext) (Env : Expression.TyEnv) (extra : List String)
    (typeArgs : List String) (σ : RigidNames) : Prop where
  prefixed : RigidNamesPrefixed σ
  nodup : (σ.map Prod.snd).Nodup
  fresh : RigidNamesFresh C.knownTypes σ
  map_fst : σ.map Prod.fst = typeArgs
  not_scope : ∀ p ∈ σ, p.2 ∉ scopeTyNames C Env
  not_extra : ∀ p ∈ σ, p.2 ∉ extra

end Core

end -- public section
