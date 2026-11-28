/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ProgramType
public import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
public import Strata.Languages.Core.ProgramWF
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.RecFuncBlock
public import Strata.Languages.Core.Typing.Soundness.Procedure
public import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
public import Strata.Languages.Core.Typing.Props.DatatypeTypeProps
public import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
public import Strata.Languages.Core.Typing.Props.ProgramTypeProps
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.TypeFactoryProps
public import Strata.DL.Lambda.TypeFactoryWFProps
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.DL.Lambda.LExprAliasFree
public import Strata.DL.Lambda.LTyWFCheckSound
public import Strata.Util.ExceptProps
public import Strata.Util.ListUtilsProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
import Strata.Languages.Core.CallWFProps
import Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.Typing.Soundness.TypeDecl
import Strata.Languages.Core.Typing.Props.NamesWFProps
import Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.AxiomType
import all Strata.Languages.Core.LemmaType
import all Strata.Languages.Core.DistinctType
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import all Strata.Languages.Core.ProgramWF
import Strata.Languages.Core.FunctionType
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.IdentifiersProps
import Strata.Languages.Core.CmdType
import Strata.Languages.Core.Typing.Props.TypeSkolemProps
import all Strata.Languages.Core.Typing.Props.SourceExprResolveProps
import Strata.Languages.Core.Typing.Props.SkolemScopeProps
import Strata.Languages.Core.Typing.Props.SkolemizerProps
import all Strata.Languages.Core.Typing.Spec.NamesWF

/-! # Soundness of `Program.typeCheck`

Key theorems:
* `Program.typeCheckIn_sound`, `Program.typeCheck_sound`: an accepted program satisfies the
  typechecker spec.
* `Program.typeCheckIn_sound_output`, `Program.typeCheck_sound_output`: the returned program is
  well typed with valid names.
* `Program.typeCheck.go_sound`, `go_sound_output`: the same for the declaration walk. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Strata.Util (HMap HMaps)

/-! ### Registered-type conditions -/

/-- Registered-type conditions on a context and an environment's substitution. -/
structure KnownTypesReady (C : Expression.TyContext) (Env : Expression.TyEnv) : Prop where
  arrow : C.knownTypes["arrow"]? = some 2
  bool : C.knownTypes["bool"]? = some 0
  /-- Every primitive literal's type is registered at its arity. -/
  literals : ∀ c : Lambda.LConst, c.isPrimitive = true →
    LMonoTy.knownInstance c.ty C.knownTypes = true
  /-- Every type in the substitution's range is registered. -/
  substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes

/-- The registered-type conditions survive extending the table, given that the new substitution's
    range is registered in the old table. -/
private theorem KnownTypesReady.mono (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (hext : KnownTypesExtends C.knownTypes C'.knownTypes)
    (hS : Lambda.Subst.RangeKnown Env'.stateSubstInfo.subst C.knownTypes)
    (h : KnownTypesReady C Env) : KnownTypesReady C' Env' where
  arrow := hext "arrow" 2 h.arrow
  bool := hext "bool" 0 h.bool
  literals := fun c hp =>
    Lambda.knownInstance_mono c.ty C.knownTypes C'.knownTypes hext (h.literals c hp)
  substRange := Lambda.Subst.RangeKnown_mono C.knownTypes C'.knownTypes _ hext hS

/-! ### The walk's substitution binds nothing between declarations -/

/-- The environment's substitution binds nothing. -/
def AmbientClear (Env : Expression.TyEnv) : Prop := SubstClear Env.stateSubstInfo.subst

/-- The environment the program walk starts from has a substitution that binds nothing. -/
theorem AmbientClear.start (Env : Expression.TyEnv) :
    AmbientClear (Program.typeCheck.startEnv Env) :=
  SubstClear.nil.push_empty

/-- Starting the program walk replaces only the substitution, so the context is unchanged. -/
private theorem Program.typeCheck.startEnv_context (Env : Expression.TyEnv) :
    (Program.typeCheck.startEnv Env).context = Env.context :=
  TEnv.updateSubst_context Env _

/-- A procedure step keeps the substitution clear. -/
private theorem AmbientClear.proc_step {sc ps : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env2 : Expression.TyEnv}
    {p : Program} {proc proc' : Procedure} {md : MetaData Expression}
    (htc : Procedure.typeCheckIn sc ps C Env.pushEmptySubstScope p proc md = .ok (proc', Env2))
    (h : AmbientClear Env) : AmbientClear Env2.popSubstScope := by
  rw [(Procedure.typeCheckIn_env_eq_and_name_eq sc ps C _ _ p proc proc' md htc).1]
  exact h

/-- Adding a type alias keeps the substitution clear. -/
private theorem AmbientClear.type_syn_step {a : TypeAlias} {C : Expression.TyContext}
    {Env v : Expression.TyEnv} (hadd : TEnv.addTypeAlias a C Env = .ok v)
    (h : AmbientClear Env) : AmbientClear v := by
  unfold AmbientClear
  rw [TEnv.addTypeAlias_stateSubstInfo a C Env v hadd]
  exact h

/-- An axiom or lemma step, resolved and unified at `bool` in a pushed substitution scope that is
    then popped, keeps the substitution clear. -/
private theorem AmbientClear.prop_step {C : Expression.TyContext} {Env EnvR : Expression.TyEnv}
    {e : Expression.Expr} {et : LExprT CoreLParams.mono} {S : SubstInfo}
    (hres : SourceExpr.resolve C Env.pushEmptySubstScope e = .ok (et, EnvR))
    (hunify : Constraints.unify [(et.toLMonoTy, LMonoTy.bool)] EnvR.stateSubstInfo = .ok S)
    (h : AmbientClear Env) : AmbientClear (EnvR.updateSubst S).popSubstScope :=
  Constraints.unify_tailClear hunify
    (SourceExpr.resolve_tailClear C _ EnvR e et hres
      (TailClear.push h _))

/-! ### The loop invariants for input and output soundness -/

/-- A factory property that gives well-formed signatures and survives adding a well-formed
    function and registering a datatype block. -/
class WalkFactoryClosed (Q : Lambda.Factory CoreLParams → Prop) : Prop where
  sigWF : ∀ fac, Q fac → FactorySigWF fac
  addFunction : ∀ (C : Expression.TyContext) (fn : LFunc CoreLParams),
    Q C.functions → LFuncWF fn → Q (C.addFactoryFunction fn).functions
  addMutualBlock : ∀ (C C' : Expression.TyContext) (block : MutualDatatype Unit),
    Q C.functions → C.addMutualBlock block = .ok C' → Q C'.functions

/-- Signature well-formedness survives the factory extensions of the declaration walk. -/
instance WalkFactoryClosed.factorySigWF : WalkFactoryClosed FactorySigWF where
  sigWF _ h := h
  addFunction C fn hC hfn := factorySigWF_addFactoryFunction C fn hC hfn.toSig
  addMutualBlock C C' block hC h := addMutualBlock_preserves_FactorySigWF C C' block hC h

/-- A factory property kept by adding one well-formed function is kept by folding in a list of
    well-formed functions. -/
private theorem WalkFactoryClosed.foldl_addFactoryFunction {α : Type}
    {Q : Lambda.Factory CoreLParams → Prop} [hQ : WalkFactoryClosed Q] (l : List α)
    (g : α → LFunc CoreLParams) :
    ∀ (C : Expression.TyContext), Q C.functions → (∀ a ∈ l, LFuncWF (g a)) →
      Q (l.foldl (fun C a => C.addFactoryFunction (g a)) C).functions := by
  induction l with
  | nil => intro C hC _; exact hC
  | cons a rest ih =>
    intro C hC hg
    exact ih _ (hQ.addFunction C (g a) hC (hg a (List.mem_cons_self ..)))
      (fun b hb => hg b (List.mem_cons_of_mem a hb))

variable {Q : Lambda.Factory CoreLParams → Prop}

/-- The conditions on the context and type environment that the declaration walk keeps between
    declarations while proving that the accepted program satisfies the typechecker spec. -/
structure TypeCheckLoopInvariant (Q : Lambda.Factory CoreLParams → Prop)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (i : Identifiers Unit) : Prop where
  envWF : LExpr.TEnvWF (T := CoreLParams) Env
  factory : Q C.functions
  ctxClosed : LExpr.checkContextTypesClosed (T := CoreLParams) Env
  aliasBodies : AliasBodiesKnown C Env.context
  mono : MonoScope Env.context
  /-- No alias is a registered type, and aliases agree with the identifier registry `i`. -/
  coherent : AliasRegistryCoherent C Env i
  clear : AmbientClear Env

/-- If no alias name of `Γ` is a registered type of `C`, the table of `C` contains no alias
    name. -/
private theorem AliasNamesFresh.containsName_eq_false {C : Expression.TyContext} {Γ : TContext Unit}
    (h : AliasNamesFresh C Γ) : ∀ al ∈ Γ.aliases, C.knownTypes.containsName al.name = false :=
  fun al hal => Bool.eq_false_iff.mpr fun htrue =>
    h al hal ((KnownTypes.containsName_eq_true_iff_mem _ _).mp htrue)

/-- If no alias name is a registered type and every alias body is a registered instance, no
    alias body mentions an alias. -/
private theorem AliasRegistryCoherent.aliasesResolved {C : Expression.TyContext}
    {Env : Expression.TyEnv}
    {i : Identifiers Unit} (hcoh : AliasRegistryCoherent C Env i)
    (hbodies : AliasBodiesKnown C Env.context) : TContext.AliasesResolved Env.context :=
  hbodies.aliasesResolved (AliasNamesFresh.containsName_eq_false hcoh.freshForKnownTypes)

/-- Under the input loop invariant, no alias body mentions an alias. -/
private theorem AliasesResolved_of_invariant {C : Expression.TyContext} {Env : Expression.TyEnv}
    {i : Identifiers Unit} (hinv : TypeCheckLoopInvariant Q C Env i) :
    TContext.AliasesResolved Env.context :=
  hinv.coherent.aliasesResolved hinv.aliasBodies

/-- The conditions on the context and type environment that the declaration walk keeps between
    declarations while proving that the returned program is well typed with valid names: the
    input conditions, and that the types the typechecker relies on are registered. -/
structure TypeCheckLoopInvariantOutput (Q : Lambda.Factory CoreLParams → Prop)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (i : Identifiers Unit) : Prop
    extends TypeCheckLoopInvariant Q C Env i where
  /-- `arrow`, `bool`, the primitive literal types and the substitution's range are registered. -/
  ready : KnownTypesReady C Env

/-- The registered-type conditions survive a procedure step. -/
private theorem KnownTypesReady.proc_step (sc ps : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env2 : Expression.TyEnv)
    (idents : Identifiers Unit) (program : Program) (proc proc' : Procedure)
    (md : MetaData Expression)
    (htc : Procedure.typeCheckIn sc ps { C with idents := idents } Env.pushEmptySubstScope program
            proc md = .ok (proc', Env2))
    (h : KnownTypesReady C Env) : KnownTypesReady C Env2.popSubstScope := by
  refine KnownTypesReady.mono _ _ _ _ (KnownTypesExtends.refl _) ?_ h
  refine Lambda.TEnv.RangeKnown_popSubstScope Env2 C.knownTypes ?_
  exact Procedure.typeCheckIn_RangeKnown sc ps { C with idents := idents } Env.pushEmptySubstScope
    Env2 program proc proc' md C.knownTypes htc
    (Lambda.TEnv.RangeKnown_pushEmptySubstScope Env C.knownTypes h.substRange)

/-! ### Ambient-scope invariants -/

/-- Under the input loop invariant, the ambient scope stores only monotypes. -/
private theorem MonoScope_of_invariant (C : Expression.TyContext) (Env : Expression.TyEnv)
    {i : Identifiers Unit} (hinv : TypeCheckLoopInvariant Q C Env i) :
    MonoScope (Env.pushEmptySubstScope).context := by
  rw [TEnv.pushEmptySubstScope_context_eq Env]
  exact hinv.mono

/-- Closed stored types and monotype-only storage transfer to an environment with the same type
    scope. -/
private theorem scopeFacts_of_context_eq {Env Env2 : Expression.TyEnv}
    (hctx : Env2.context = Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    LExpr.checkContextTypesClosed (T := CoreLParams) Env2 ∧ MonoScope Env2.context := by
  rw [LExpr.checkContextTypesClosed_of_context_eq (T := CoreLParams) Env2 Env hctx, hctx]
  exact ⟨h_closed, h_mono⟩

/-! ### Datatype-block names, and unchanged alias lists -/

/-- Every datatype of an alias-resolved block is named by a declared name of the block
    declaration. -/
private theorem names_mem_of_resolveAliases (block block_r : List (LDatatype Unit))
    (md : MetaData Expression) (Env Env_r : Expression.TyEnv)
    (hres : MutualDatatype.resolveAliases block Env = .ok (block_r, Env_r)) :
    ∀ d ∈ block_r, ∃ x ∈ (Decl.type (.data block) md).names, x.name = d.name := by
  intro d hd
  have hmap : block_r.map (·.name) = block.map (·.name) :=
    MutualDatatype.resolveAliases_names_map block block_r Env Env_r hres
  have hmemn : d.name ∈ block.map (·.name) := by
    rw [← hmap]; exact List.mem_map_of_mem hd
  obtain ⟨d', hd', hdn⟩ := List.mem_map.mp hmemn
  refine ⟨((d'.name : String) : Expression.Ident), ?_, hdn⟩
  simp only [Decl.names, TypeDecl.names]
  exact List.mem_map_of_mem hd'

/-! ### Keeping alias names unregistered -/

/-- Alias-name freshness depends only on the registered types and the alias list. -/
private theorem AliasNamesFresh.of_eq {C C' : Expression.TyContext} {Γ Γ' : TContext Unit}
    (hk : C'.knownTypes = C.knownTypes) (ha : Γ'.aliases = Γ.aliases) (h : AliasNamesFresh C Γ) :
    AliasNamesFresh C' Γ' := by
  intro al hal
  rw [hk]
  exact h al (ha ▸ hal)

/-! ### Preserving alias-registry coherence -/

/-- A step that registers names and keeps the known-types table and alias list preserves
    alias-registry coherence. -/
private theorem AliasRegistryCoherent.step_of_context_eq
    {C C2 : Expression.TyContext} {Env Env2 : Expression.TyEnv} {i i' : Identifiers Unit}
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message}
    (hreg : Identifiers.addListWithError i l f = .ok i')
    (haliases : Env2.context.aliases = Env.context.aliases)
    (hknown : C2.knownTypes = C.knownTypes)
    (hc : AliasRegistryCoherent C Env i) : AliasRegistryCoherent C2 Env2 i' :=
  AliasRegistryCoherent.of_knownTypes_eq hknown
    (AliasRegistryCoherent.of_aliases_eq haliases
      (AliasRegistryCoherent.of_idents_mem (Identifiers.addListWithError_mem_mono hreg) hc))

/-- Under alias-registry coherence, no alias has a name the identifier registry newly accepts. -/
private theorem AliasRegistryCoherent.alias_ne_of_registered
    {C : Expression.TyContext} {Env : Expression.TyEnv} {i i' : Identifiers Unit}
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message} {n : String}
    (hc : AliasRegistryCoherent C Env i) (hreg : Identifiers.addListWithError i l f = .ok i')
    (hmem : ∃ x ∈ l, x.name = n) : ∀ al ∈ Env.context.aliases, al.name ≠ n := by
  obtain ⟨x, hx, rfl⟩ := hmem
  intro al hal heq
  exact Identifiers.addListWithError_not_mem hreg x hx (heq ▸ hc.declared al hal)

/-- Registering a type constructor whose name the registry newly accepts preserves alias-registry
    coherence. -/
private theorem AliasRegistryCoherent.step_type_con
    (C C' : Expression.TyContext) (Env : Expression.TyEnv) (i i' : Identifiers Unit)
    (k : KnownType) (msg : Strata.Message)
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message}
    (hmem : ∃ x ∈ l, x.name = k.name)
    (hreg : Identifiers.addListWithError i l f = .ok i')
    (hadd : C.addKnownTypeWithError k msg = .ok C')
    (hc : AliasRegistryCoherent C Env i) :
    AliasRegistryCoherent C' Env i' := by
  exact ⟨fun al hal => Identifiers.addListWithError_mem_mono hreg al.name (hc.declared al hal),
    AliasNamesFresh.addKnownTypeWithError (hc.alias_ne_of_registered hreg hmem) hadd
      hc.freshForKnownTypes⟩

/-- Adding a type alias whose name the registry accepts preserves alias-registry coherence. -/
private theorem AliasRegistryCoherent.step_type_syn
    (C : Expression.TyContext) (Env Env2 : Expression.TyEnv) (i i' : Identifiers Unit)
    (a : TypeAlias)
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message}
    (hmem : ∃ x ∈ l, x.name = a.name)
    (hreg : Identifiers.addListWithError i l f = .ok i')
    (halias : TEnv.addTypeAlias a C Env = .ok Env2)
    (hc : AliasRegistryCoherent C Env i) :
    AliasRegistryCoherent C Env2 i' := by
  obtain ⟨-, -, -, hnotknown, -, storedTy, -, -, haliases, -⟩ :=
    addTypeAlias_decompose a C Env Env2 halias
  obtain ⟨x, hx, hxname⟩ := hmem
  have hnew : a.name ∈ i' := by
    rw [← hxname]; exact Identifiers.addListWithError_mem_new hreg x hx
  refine ⟨?_, ?_⟩
  · intro al hal
    rw [haliases, List.mem_cons] at hal
    rcases hal with heq | htl
    · subst heq; exact hnew
    · exact Identifiers.addListWithError_mem_mono hreg al.name (hc.declared al htl)
  · intro al hal
    rw [haliases, List.mem_cons] at hal
    rcases hal with heq | htl
    · subst heq
      intro hmemk
      exact absurd ((KnownTypes.containsName_eq_true_iff_mem _ _).mpr hmemk)
        (by simpa using hnotknown)
    · exact hc.freshForKnownTypes al htl

/-- Registering a mutual datatype block whose names the registry newly accepts preserves
    alias-registry coherence. -/
private theorem AliasRegistryCoherent.step_type_data
    (C C' : Expression.TyContext) (Env : Expression.TyEnv) (i i' : Identifiers Unit)
    (block : List (LDatatype Unit))
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message}
    (hmem : ∀ d ∈ block, ∃ x ∈ l, x.name = d.name)
    (hreg : Identifiers.addListWithError i l f = .ok i')
    (hadd : C.addMutualBlock block = .ok C')
    (hc : AliasRegistryCoherent C Env i) :
    AliasRegistryCoherent C' Env i' := by
  exact ⟨fun al hal => Identifiers.addListWithError_mem_mono hreg al.name (hc.declared al hal),
    AliasNamesFresh.addMutualBlock (fun d hd => hc.alias_ne_of_registered hreg (hmem d hd))
      hadd hc.freshForKnownTypes⟩

/-! ### Aliases added by a walk step, and declared program names -/

/-- `Env2`'s alias list extends `Env`'s by entries with new names, each declared by `program`
    and not a type constructor `C` registers. -/
structure AliasStepFresh (program : Program) (C : Expression.TyContext)
    (Env Env2 : Expression.TyEnv) : Prop where
  extension : TypeAlias.FreshExtension Env.context.aliases Env2.context.aliases
  newNotKnown : ∀ al ∈ Env2.context.aliases, al ∉ Env.context.aliases → al.name ∉ C.knownTypes
  newDeclared : ∀ al ∈ Env2.context.aliases, al ∉ Env.context.aliases →
    DeclaredProgramName program al.name

/-- A step that keeps the alias list is a fresh alias step. -/
private theorem AliasStepFresh.of_aliases_eq {program : Program} {C : Expression.TyContext}
    {Env Env2 : Expression.TyEnv} (h : Env2.context.aliases = Env.context.aliases) :
    AliasStepFresh program C Env Env2 :=
  ⟨TypeAlias.FreshExtension.of_eq h, fun _ hal hnot => absurd (h ▸ hal) hnot,
   fun _ hal hnot => absurd (h ▸ hal) hnot⟩

/-- Fresh alias steps compose when the known-types table only grows across the first. -/
private theorem AliasStepFresh.trans {program : Program} {C C2 : Expression.TyContext}
    {Env Env2 Env3 : Expression.TyEnv}
    (hmono : ∀ n : String, n ∈ C.knownTypes → n ∈ C2.knownTypes)
    (h1 : AliasStepFresh program C Env Env2) (h2 : AliasStepFresh program C2 Env2 Env3) :
    AliasStepFresh program C Env Env3 := by
  refine ⟨h1.extension.trans h2.extension, ?_, ?_⟩
  · intro al hal hnot
    by_cases hmid : al ∈ Env2.context.aliases
    · exact h1.newNotKnown al hmid hnot
    · exact fun hmem => h2.newNotKnown al hal hmid (hmono al.name hmem)
  · intro al hal hnot
    by_cases hmid : al ∈ Env2.context.aliases
    · exact h1.newDeclared al hmid hnot
    · exact h2.newDeclared al hal hmid

/-- A fresh alias step transfers to an incoming environment with the same alias list. -/
private theorem AliasStepFresh.of_aliases_eq_left {program : Program} {C : Expression.TyContext}
    {Env EnvA Env2 : Expression.TyEnv} (h : EnvA.context.aliases = Env.context.aliases)
    (hs : AliasStepFresh program C EnvA Env2) : AliasStepFresh program C Env Env2 := by
  obtain ⟨new, heq, hfresh⟩ := hs.extension
  refine ⟨⟨new, by rw [heq, h], ?_⟩, ?_, ?_⟩
  · intro a ha b hb
    exact hfresh a ha b (by rw [h]; exact hb)
  · intro al hal hnot
    exact hs.newNotKnown al hal (by rw [h]; exact hnot)
  · intro al hal hnot
    exact hs.newDeclared al hal (by rw [h]; exact hnot)

/-- A fresh alias step transfers to a context with the same known-types table. -/
private theorem AliasStepFresh.of_knownTypes_eq {program : Program} {C D : Expression.TyContext}
    {Env Env2 : Expression.TyEnv} (h : D.knownTypes = C.knownTypes)
    (hs : AliasStepFresh program C Env Env2) : AliasStepFresh program D Env Env2 :=
  ⟨hs.extension, fun al hal hnot => by rw [h]; exact hs.newNotKnown al hal hnot,
   hs.newDeclared⟩

/-- Every alias name a fresh alias step adds fails `KnownTypes.containsName` on the incoming
    table. -/
private theorem AliasStepFresh.newNotKnown' {program : Program} {C : Expression.TyContext}
    {Env Env2 : Expression.TyEnv} (h : AliasStepFresh program C Env Env2) :
    ∀ al ∈ Env2.context.aliases, al ∉ Env.context.aliases →
      KnownTypes.containsName C.knownTypes al.name = false := by
  intro al hal hnot
  cases hb : KnownTypes.containsName C.knownTypes al.name with
  | false => rfl
  | true =>
    exact absurd ((KnownTypes.containsName_eq_true_iff_mem _ _).mp hb) (h.newNotKnown al hal hnot)

/-- Every name declared by a suffix of the declarations is declared by the whole program. -/
private theorem declaredProgramName_of_suffix {program : Program} {decls : List Decl}
    (hsuffix : decls <:+ program.decls) :
    ∀ d ∈ decls, ∀ n ∈ d.names, DeclaredProgramName program n.name := by
  intro d hd n hn
  refine ⟨n, ?_, rfl⟩
  simp only [Program.getNames, Program.getNames.go, List.mem_flatMap]
  exact ⟨d, hsuffix.subset hd, hn⟩

/-! ### One declaration step with an arbitrary continuation -/

/-- A step with any continuation is the step returning its result, followed by the
    continuation. -/
private theorem Program.typeCheck.stepThen_eq_bind {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) :
    Program.typeCheck.stepThen program PS S C Env decl k =
      (Program.typeCheck.stepThen program PS S C Env decl
          (fun d C' Env' S' => .ok (d, C', Env', S')) >>=
        fun r => k r.1 r.2.1 r.2.2.1 r.2.2.2) := by
  simp only [Program.typeCheck.stepThen, bind, Except.bind]
  repeat' split
  all_goals first
    | rfl
    | contradiction
    | (rename_i heqOk; injection heqOk with hv; subst hv; rfl)

/-- Every continuation of the step at `decl` receives the declaration `d'`, context `C'`,
    environment `Env'` and scope type-name set `S'`. -/
abbrev StepReceives (program : Program) (PS : Thunk (Std.HashSet String))
    (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (d' : Decl) (C' : Expression.TyContext) (Env' : Expression.TyEnv)
    (S' : Std.HashSet String) : Prop :=
  ∀ {β : Type} (k' : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message β),
    Program.typeCheck.stepThen program PS S C Env decl k' = k' d' C' Env' S'

/-- A step result (declaration, context, environment, scope type-name set) that `k` maps to
    `.ok res`, and that every continuation of the step at `decl` receives. -/
abbrev StepAccepts {α : Type} (program : Program) (PS : Thunk (Std.HashSet String))
    (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) :
    Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop :=
  fun d' C' Env' S' => k d' C' Env' S' = .ok res ∧
    StepReceives program PS S C Env decl d' C' Env' S'

/-- A step result at `decl` from which the walk over `ds`, with the result declaration added to
    `acc`, ends in `(out, Env')`, and that every continuation of the step receives. -/
abbrev WalkStepAccepts (program : Program) (PS : Thunk (Std.HashSet String))
    (S : Std.HashSet String) (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (ds acc out : Decls) (Env' : Expression.TyEnv) :
    Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop :=
  StepAccepts program PS S C Env decl
    (fun d' C' E T => Program.typeCheck.goWith program PS T C' E ds (d' :: acc)) (out, Env')

/-- A step that succeeds with some continuation produces one elaborated declaration, context,
    environment and scope type-name set, which every continuation receives. -/
private theorem Program.typeCheck.stepThen_ok {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S C Env decl k = .ok res) :
    ∃ (d' : Decl) (C' : Expression.TyContext) (Env' : Expression.TyEnv)
      (S' : Std.HashSet String),
      StepAccepts program PS S C Env decl k res d' C' Env' S' := by
  rw [Program.typeCheck.stepThen_eq_bind] at h
  cases hstep : Program.typeCheck.stepThen program PS S C Env decl
      (fun d C' Env' S' => .ok (d, C', Env', S')) with
  | error e =>
    rw [hstep] at h
    exact absurd h (by simp [bind, Except.bind])
  | ok r =>
    rw [hstep] at h
    obtain ⟨d', C', Env', S'⟩ := r
    refine ⟨d', C', Env', S', h, ?_⟩
    intro β k'
    rw [Program.typeCheck.stepThen_eq_bind, hstep]
    rfl

/-- If a monotone property `Φ` of a continuation's acceptance holds whenever the step accepts
    with any continuation, then it holds for the given accepting continuation together with the
    fact that every continuation of the step receives the same results. -/
private theorem Program.typeCheck.stepThen_det {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {decl : Decl}
    (Φ : (Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop) → Prop)
    (hmono : ∀ R R' : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop,
      (∀ d' C' Env' S', R d' C' Env' S' → R' d' C' Env' S') → Φ R → Φ R')
    (hΦ : ∀ {γ : Type} (k' : Decl → Expression.TyContext → Expression.TyEnv →
        Std.HashSet String → Except Strata.Message γ) (r : γ),
      Program.typeCheck.stepThen program PS S C Env decl k' = .ok r →
        Φ fun d' C' Env' S' => k' d' C' Env' S' = .ok r)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S C Env decl k = .ok res) :
    Φ (StepAccepts program PS S C Env decl k res) := by
  obtain ⟨d0, C0, Env0, S0, hk, hdet⟩ :=
    Program.typeCheck.stepThen_ok program C Env decl k res h
  refine hmono _ _ ?_
    (hΦ (fun d' C' Env' S' => .ok (d', C', Env', S')) (d0, C0, Env0, S0) (hdet _))
  intro d' C' Env' S' hk0
  simp only [Except.ok.injEq, Prod.mk.injEq] at hk0
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hk0
  exact ⟨hk, hdet⟩

/-! ### Typing and invariant preservation for one declaration step -/

/-- Inversion of one accepted declaration step at an opaque type declaration, with any
    continuation `k`. -/
private theorem Program.typeCheck.stepThen_type_con_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (tc : TypeConstructor) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.con tc) md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (ctx : Expression.TyContext),
      (∃ f, Identifiers.addListWithError i (Decl.type (.con tc) md).names f = .ok idents)
      ∧ ({ C with idents := idents } : Expression.TyContext).addKnownTypeWithError
          { name := tc.name, metadata := tc.numargs } default = .ok ctx
      ∧ C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs } default
          = .ok { ctx with idents := C.idents }
      ∧ k (Decl.type (.con tc) md)
          { { ctx with idents := C.idents } with idents := idents }
          Env S = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h with idents hidents
  elim_err h with resres hres
  elim_err hres with C_new hnew
  elim_err hnew with ctx hcheck
  have hdecomp := TypeConstructor.typeCheck_decompose tc .program
    { C with idents := idents } ctx Env hcheck
  have hctx := hdecomp.2.2 default
  simp only [Except.ok.injEq] at hnew hres
  subst hnew
  subst hres
  dsimp only at h
  obtain ⟨hswap, hids⟩ := addKnownTypeWithError_setIdents C idents
    { name := tc.name, metadata := tc.numargs } _ ctx hctx
  have hC : ({ { ctx with idents := C.idents } with idents := idents }
                : Expression.TyContext) = ctx := by
    rw [← hids]
  refine ⟨idents, ctx, ⟨_, hidents⟩, hctx, hswap, ?_⟩
  rw [hC]
  exact h

/-- An accepted opaque-type step preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.type_con_step (C ctx : Expression.TyContext)
    (Env : Expression.TyEnv) (i idents : Identifiers Unit) (tc : TypeConstructor)
    (md : MetaData Expression) (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : ∃ f, Identifiers.addListWithError i (Decl.type (.con tc) md).names f = .ok idents)
    (hctx : ({ C with idents := idents } : Expression.TyContext).addKnownTypeWithError
      { name := tc.name, metadata := tc.numargs } default = .ok ctx) :
    TypeCheckLoopInvariant Q { ctx with idents := C.idents } Env idents := by
  obtain ⟨regMsg, hidents⟩ := hidents
  obtain ⟨h_env, h_fac, h_closed, h_alB, h_mono, h_coh, h_clear⟩ := hinv
  have hfun : ({ ctx with idents := C.idents } : Expression.TyContext).functions
      = C.functions :=
    Lambda.addKnownTypeWithError_functions_eq { C with idents := idents } ctx _ _ hctx
  have hext : KnownTypesExtends C.knownTypes
      ({ ctx with idents := C.idents } : Expression.TyContext).knownTypes :=
    KnownTypesExtends.of_addKnownTypeWithError { C with idents := idents } ctx
      { name := tc.name, metadata := tc.numargs } _ hctx
  have hmem : ∃ x ∈ (Decl.type (.con tc) md).names, x.name = tc.name :=
    ⟨tc.name, by simp [Decl.names, TypeDecl.names], rfl⟩
  refine ⟨h_env, ?_, h_closed, ?_, h_mono, ?_, h_clear⟩
  · rw [hfun]; exact h_fac
  · exact AliasBodiesKnown.of_extends C _ Env.context Env.context rfl hext h_alB
  · exact AliasRegistryCoherent.of_knownTypes_eq (C := ctx) rfl
      (AliasRegistryCoherent.step_type_con { C with idents := idents } ctx Env i idents
        { name := tc.name, metadata := tc.numargs } _ hmem hidents
        hctx (AliasRegistryCoherent.setIdents idents h_coh))

/-- An accepted opaque-type step satisfies the typechecker spec, preserves the input invariant,
    and continues the walk. -/
private theorem type_con_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (tc : TypeConstructor) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.con tc) md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.type (.con tc) md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, ctx, ⟨regMsg, hidents⟩, hctx, hdefault, hrec⟩ :=
    Program.typeCheck.stepThen_type_con_inversion program C Env i tc md k res h
  refine ⟨idents, { ctx with idents := C.idents }, Env, Decl.type (.con tc) md,
    DeclHasType.type_con C { ctx with idents := C.idents } Env.context tc md hdefault,
    TypeCheckLoopInvariant.type_con_step C ctx Env i idents tc md hinv ⟨regMsg, hidents⟩ hctx,
    ⟨_, hrec⟩⟩

/-- Inversion of one accepted declaration step at a type synonym, with any continuation `k`. -/
private theorem Program.typeCheck.stepThen_type_syn_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (ts : TypeSynonym) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.syn ts) md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (v : Expression.TyEnv) (storedTy : LMonoTy)
      (Env_ra : Expression.TyEnv),
      (∃ f, Identifiers.addListWithError i (Decl.type (.syn ts) md).names f = .ok idents)
      ∧ TEnv.addTypeAlias { name := ts.name, typeArgs := ts.typeArgs, type := ts.type }
          { C with idents := idents } Env = .ok v
      ∧ ¬ C.knownTypes.containsName ts.name
      ∧ (∀ b ∈ Env.context.aliases, b.name ≠ ts.name)
      ∧ LMonoTy.resolveAliases ts.type Env = .ok (storedTy, Env_ra)
      ∧ v.context.aliases
          = { typeArgs := ts.typeArgs, name := ts.name, type := storedTy } :: Env.context.aliases
      ∧ TEnv.context v
          = { Env.context with aliases :=
                { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
                  :: Env.context.aliases }
      ∧ (TContext.AliasesResolved Env.context →
          InputSynonymOk C Env.context { typeArgs := ts.typeArgs, name := ts.name, type := ts.type }
            storedTy v.context)
      ∧ k (Decl.type (.syn { ts with type := storedTy }) md)
          { C with idents := idents } v (S.insertMany (ts.name :: getTypeRefs storedTy))
          = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h with idents hidents
  elim_err h with synOut haddmap
  rcases hsyn : TypeSynonym.typeCheck ts { C with idents := idents } Env with err | ⟨ts', v⟩
  · rw [hsyn] at haddmap
    simp [Except.mapError] at haddmap
  · rw [hsyn] at haddmap
    simp only [Except.mapError, Except.ok.injEq] at haddmap
    subst haddmap
    have hsynDecomp :=
      TypeSynonym.typeCheck_decompose ts ts' { C with idents := idents } Env v hsyn
    have hadd := hsynDecomp.1
    obtain ⟨hnodup, hconj2, hconj3, hknown, hnamefresh, storedTy, Env_ra, hra, haliases,
      htypes, -⟩ :=
      addTypeAlias_decompose { name := ts.name, typeArgs := ts.typeArgs, type := ts.type }
        { C with idents := idents } Env v hadd
    obtain ⟨storedTySrc, hsrc, haliasesSrc, hts'⟩ :=
      TypeSynonym.typeCheck_sourceTyWF_withIdents ts ts' C idents Env v hsyn
    have hstoredEq : storedTy = storedTySrc := by
      rw [haliases] at haliasesSrc
      simp only [List.cons.injEq, TypeAlias.mk.injEq, true_and, and_true] at haliasesSrc
      exact haliasesSrc
    subst hstoredEq
    have hvctx : TEnv.context v
        = { Env.context with aliases :=
              { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
                :: Env.context.aliases } := by
      have hrw : ({ Env.context with aliases :=
              { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
                :: Env.context.aliases } : TContext Unit)
          = { types := Env.context.types,
              aliases := { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
                :: Env.context.aliases } := rfl
      rw [hrw, ← haliases, ← htypes]
    subst hts'
    have htyping : TContext.AliasesResolved Env.context →
        InputSynonymOk C Env.context { typeArgs := ts.typeArgs, name := ts.name, type := ts.type }
          storedTy v.context := by
      intro hresolved
      have haliasFree := Lambda.resolveAliases_output_aliasFree (T := CoreLParams)
        ts.type Env storedTy Env_ra hra hresolved
      exact ⟨⟨fun tv => ⟨hconj2 tv, hconj3 tv⟩, hnodup⟩, hknown, hnamefresh, hsrc, haliasFree,
        hvctx⟩
    exact ⟨idents, v, storedTy, Env_ra, ⟨_, hidents⟩, hadd, hknown, hnamefresh, hra, haliases,
      hvctx, htyping, h⟩

/-- An accepted type-synonym step preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.type_syn_step (C : Expression.TyContext)
    (Env v : Expression.TyEnv) (i idents : Identifiers Unit) (ts : TypeSynonym)
    (md : MetaData Expression) (storedTy : LMonoTy) (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : ∃ f, Identifiers.addListWithError i (Decl.type (.syn ts) md).names f = .ok idents)
    (hadd : TEnv.addTypeAlias { name := ts.name, typeArgs := ts.typeArgs, type := ts.type }
      { C with idents := idents } Env = .ok v)
    (hvctx : TEnv.context v
      = { Env.context with aliases :=
            { typeArgs := ts.typeArgs, name := ts.name, type := storedTy }
              :: Env.context.aliases }) :
    TypeCheckLoopInvariant Q C v idents := by
  obtain ⟨regMsg, hidents⟩ := hidents
  have h_res := AliasesResolved_of_invariant hinv
  obtain ⟨h_env, h_fac, h_closed, h_alB, h_mono, h_coh, h_clear⟩ := hinv
  obtain ⟨stored, hstoredList, -, -, -, hstoredKnown⟩ :=
    Lambda.addTypeAlias_stored
      { name := ts.name, typeArgs := ts.typeArgs, type := ts.type }
      { C with idents := idents } Env v h_res hadd
  have htypesEq : v.context.types = Env.context.types := by rw [hvctx]
  have hmem : ∃ x ∈ (Decl.type (.syn ts) md).names, x.name = ts.name :=
    ⟨ts.name, by simp [Decl.names, TypeDecl.names], rfl⟩
  refine ⟨addTypeAlias_preserves_TEnvWF _ { C with idents := idents } Env v h_env hadd,
      h_fac, ?_, ?_, ?_, ?_, AmbientClear.type_syn_step hadd h_clear⟩
  · simp only [LExpr.checkContextTypesClosed] at h_closed ⊢
    rw [hvctx]
    exact h_closed
  · intro al hal
    rw [hstoredList] at hal
    rcases List.mem_cons.mp hal with rfl | hal
    · exact hstoredKnown
    · exact h_alB al hal
  · intro z tz hfind
    refine h_mono z tz ?_
    rw [htypesEq] at hfind
    exact hfind
  · exact AliasRegistryCoherent.of_knownTypes_eq (C := { C with idents := idents }) rfl
      (AliasRegistryCoherent.step_type_syn { C with idents := idents } Env v i idents
        { name := ts.name, typeArgs := ts.typeArgs, type := ts.type }
        hmem hidents hadd (AliasRegistryCoherent.setIdents idents h_coh))

/-- An accepted type-synonym step satisfies the typechecker spec, preserves the input invariant,
    and continues the walk. -/
private theorem type_syn_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (ts : TypeSynonym) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.syn ts) md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.type (.syn ts) md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, v, storedTy, Env_ra, ⟨regMsg, hidents⟩, hadd, -, -, -, -, hvctx,
    htyping, hrec⟩ :=
      Program.typeCheck.stepThen_type_syn_inversion program C Env i ts md k res h
  have h_res := AliasesResolved_of_invariant hinv
  refine ⟨idents, C, v, _,
    DeclHasType.type_syn C Env.context ts md v.context ⟨storedTy, htyping h_res⟩,
    TypeCheckLoopInvariant.type_syn_step C Env v i idents ts md storedTy hinv ⟨regMsg, hidents⟩
      hadd hvctx,
    ⟨_, hrec⟩⟩

/-- Inversion of one accepted declaration step at a mutual datatype block, with any continuation
    `k`. -/
private theorem Program.typeCheck.stepThen_type_data_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (block : List (LDatatype Unit)) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.data block) md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (block_r : List (LDatatype Unit)) (C' : Expression.TyContext),
      (∃ f, Identifiers.addListWithError i (Decl.type (.data block) md).names f = .ok idents)
      ∧ MutualDatatype.resolveAliases block Env = .ok (block_r, Env)
      ∧ ({ C with idents := idents } : Expression.TyContext).addMutualBlock block_r = .ok C'
      ∧ C.addMutualBlock block_r = .ok { C' with idents := C.idents }
      ∧ k (Decl.type (.data block_r) md)
          { { C' with idents := C.idents } with idents := idents }
          Env (S.insertMany (Factory.tyNamesFrom C.functions.toArray.size C'.functions))
        = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch, Factory.numFunctions] at h
  elim_err h with idents hidents
  elim_err h with v heq
  elim_err heq with a heqa
  elim_err heqa with vres hvres
  obtain ⟨block_r, C', Env_r⟩ := vres
  simp only [Except.ok.injEq] at heqa heq
  subst heqa
  subst heq
  simp only at h
  have htc := hvres
  unfold Core.MutualDatatype.typeCheck at htc
  simp only [bind, Except.bind] at htc
  repeat (split_ns at htc <;> try contradiction)
  simp only [Except.ok.injEq, Prod.mk.injEq] at htc
  obtain ⟨hblock, hC', hEnv_r⟩ := htc
  have hresMapped :
      (MutualDatatype.resolveAliases block Env).mapError Strata.Message.fromFormat =
        .ok (block_r, Env_r) := by
    rw [← hblock, ← hEnv_r]
    assumption
  have hadd :
      ({ C with idents := idents } : Expression.TyContext).addMutualBlock block_r =
        .ok C' := by
    rw [← hblock, ← hC']
    assumption
  have hres : MutualDatatype.resolveAliases block Env = .ok (block_r, Env_r) :=
    Except.mapError_ok_h' hresMapped
  have hEnv : Env_r = Env := MutualDatatype.resolveAliases_env_eq block block_r Env Env_r hres
  subst hEnv
  obtain ⟨hadd', hidents'⟩ :=
    addMutualBlock_setIdents C idents block_r C' hadd
  have hC' : ({ { C' with idents := C.idents } with idents := idents }
                : Expression.TyContext) = C' := by
    rw [← hidents']
  refine ⟨idents, block_r, C', ⟨_, hidents⟩, hres, hadd, hadd', ?_⟩
  rw [hC']
  exact h

/-- An accepted mutual-datatype step preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.type_data_step [hQ : WalkFactoryClosed Q]
    (C C' : Expression.TyContext) (Env : Expression.TyEnv) (i idents : Identifiers Unit)
    (block block_r : List (LDatatype Unit)) (md : MetaData Expression)
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : ∃ f, Identifiers.addListWithError i (Decl.type (.data block) md).names f
      = .ok idents)
    (hres : MutualDatatype.resolveAliases block Env = .ok (block_r, Env))
    (hadd : ({ C with idents := idents } : Expression.TyContext).addMutualBlock block_r
      = .ok C') :
    TypeCheckLoopInvariant Q { C' with idents := C.idents } Env idents := by
  obtain ⟨regMsg, hidents⟩ := hidents
  obtain ⟨h_env, h_fac, h_closed, h_alB, h_mono, h_coh, h_clear⟩ := hinv
  have hext : KnownTypesExtends C.knownTypes C'.knownTypes :=
    KnownTypesExtends.of_addMutualBlock { C with idents := idents } C' block_r hadd
  refine ⟨h_env, ?_, h_closed, ?_, h_mono, ?_, h_clear⟩
  · exact hQ.addMutualBlock { C with idents := idents } C' block_r h_fac hadd
  · exact AliasBodiesKnown.of_extends C _ Env.context Env.context rfl hext h_alB
  · exact AliasRegistryCoherent.of_knownTypes_eq (C := C') rfl
      (AliasRegistryCoherent.step_type_data { C with idents := idents } C' Env i idents block_r
        (names_mem_of_resolveAliases block block_r md Env Env hres) hidents hadd
        (AliasRegistryCoherent.setIdents idents h_coh))

/-- An accepted mutual-datatype step satisfies the typechecker spec, preserves the input
    invariant, and continues the walk. -/
private theorem type_data_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (block : List (LDatatype Unit)) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.data block) md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.type (.data block) md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, block_r, C', ⟨regMsg, hidents⟩, hres, hadd, hadd', hrec⟩ :=
    Program.typeCheck.stepThen_type_data_inversion program C Env i block md k res h
  refine ⟨idents, { C' with idents := C.idents }, Env,
    Decl.type (TypeDecl.data block_r) md,
    DeclHasType.type_data C { C' with idents := C.idents } Env.context block md block_r
      (resolveAliases_MutualBlockTyCompat_poly block block_r Env Env hres) hadd',
    TypeCheckLoopInvariant.type_data_step C C' Env i idents block block_r md hinv
      ⟨regMsg, hidents⟩ hres hadd,
    ⟨_, hrec⟩⟩

/-- A successful distinctness route is a distinctness check in fresh variable and substitution
    scopes, followed by restoring the incoming type scope. -/
private theorem Decl.routeDistinct_success
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (name : Expression.Ident) (es : List Expression.Expr)
    (md : MetaData Expression) (fileRange : Strata.FileRange)
    (checked : Option (List Expression.Expr))
    (h : Decl.routeDistinctBeforeRegistration (.distinct name es md) C Env fileRange =
      .ok (checked, Env')) :
    ∃ es' EnvR, checked = some es'
      ∧ Env' = (EnvR.popSubstScope.popContext).updateContext Env.context
      ∧ Distinct.typeCheck C Env.pushEmptyContext.pushEmptySubstScope name es =
        .ok (es', EnvR) := by
  unfold Decl.routeDistinctBeforeRegistration at h
  simp only [Except.mapError, bind, Except.bind] at h
  elim_err h with result hcheck
  obtain ⟨es', EnvR⟩ := result
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨es', EnvR, rfl, rfl, Except.mapError_ok_h' hcheck⟩

/-- Decomposes a successful distinctness check into its guards, resolution, unification and
    output. -/
private theorem Distinct.typeCheck_success
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (name : Expression.Ident) (es es' : List Expression.Expr)
    (h : Distinct.typeCheck C Env name es = .ok (es', Env')) :
    ∃ (ets : List (LExprT CoreLParams.mono)) (S : SubstInfo),
      SourceExpr.resolves C Env es = .ok (ets, Env')
      ∧ Constraints.unify (Distinct.sharedTypeConstraints ets) Env'.stateSubstInfo = .ok S
      ∧ es' = ets.map (fun et =>
          LExpr.unresolved (LExpr.applySubstT et S.subst))
      ∧ (∀ e ∈ es', annotTyVars e = [])
      ∧ ∀ e ∈ es, WrittenTyVarScope.unboundAnnotVar? false [] [] e = none := by
  unfold Distinct.typeCheck at h
  cases hsc : es.findSome? (WrittenTyVarScope.unboundAnnotVar? false [] []) with
  | some v => simp [unboundAnnotMsg?_eq, hsc] at h
  | none =>
  simp only [unboundAnnotMsg?_eq, hsc, Option.map_none] at h
  split at h
  · simp at h
  rename_i ets EnvR hres
  have hres' := SourceExpr.orFreeVarError_eq_ok.mp hres
  split at h
  · simp at h
  rename_i S hunify
  split at h
  · rename_i hstored
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hfin : ∀ et, (finishStored [] S.subst (tyVarsIn []) et).1 =
        LExpr.unresolved (LExpr.applySubstT et S.subst) := by
      intro et
      rw [finishStored_eq, finishDeskolemized, funext deskolemizeTy_nil]
      exact congrFun mapExprTys_id _
    refine ⟨ets, S, hres', hunify, ?_, ?_, List.findSome?_eq_none_iff.mp hsc⟩
    · simp only [List.map_map, Function.comp_def, hfin]
    · intro e he
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
      have hb := List.all_eq_true.mp hstored q hq
      obtain ⟨et, -, rfl⟩ := List.mem_map.mp hq
      rw [finishStored_eq] at hb ⊢
      exact List.eq_nil_iff_forall_not_mem.mpr fun v hv =>
        nomatch annotTyVars_mem_of_tyVarsIn hb v hv
  · simp at h

/-- Successful shared-type unification gives every resolved expression in the group the same
    substituted monotype. -/
private theorem Distinct.sharedTypeConstraints_sound
    (ets : List (LExprT CoreLParams.mono)) (old new : SubstInfo)
    (h : Constraints.unify (Distinct.sharedTypeConstraints ets) old = .ok new) :
    ∃ mty, ∀ et ∈ ets, LMonoTy.subst new.subst et.toLMonoTy = mty := by
  cases ets with
  | nil => exact ⟨.bool, by simp⟩
  | cons et ets =>
    refine ⟨LMonoTy.subst new.subst et.toLMonoTy, ?_⟩
    intro et' het'
    rcases List.mem_cons.mp het' with rfl | het'
    · rfl
    · have hpairMem : (et'.toLMonoTy, et.toLMonoTy) ∈ sharedTypeConstraints (et :: ets) := by
        simp only [Distinct.sharedTypeConstraints, List.mem_map]
        exact ⟨et', het', rfl⟩
      exact Constraints.unify_sound _ _ _ h (et'.toLMonoTy, et.toLMonoTy) hpairMem

/-- The rigid renaming of a proposition check, whose constants are no type name in scope at the
    check, changes nothing in scope when deskolemized. -/
private theorem NoSkolemAmbient.of_prop {C : Expression.TyContext} {i : Identifiers Unit}
    {Env : Expression.TyEnv} {σ : RigidNames} (hpfx : RigidNamesPrefixed σ)
    (hnot : ∀ p ∈ σ, p.2 ∉ scopeTyNames { C with idents := i } Env.pushEmptySubstScope) :
    NoSkolemAmbient C Env.context σ := by
  have hpush := NoSkolemAmbient.of_not_scopeTyNames hpfx hnot
  rw [TEnv.pushEmptySubstScope_context_eq] at hpush
  exact ⟨hpush.ctxTypes, hpush.aliases, hpush.functions⟩

/-- What a successful proposition check establishes about its rigid renaming `σ` of the type
    parameters and its resolved proposition `et`: the constants are distinct, prefixed,
    unregistered, no type name in scope and named by no annotation of `e`; the proposition
    skolemized by `σ` resolves at `bool`; the result is the deskolemized `et`; and every
    annotation type variable of the result is a type parameter. -/
private structure TypeCheckPropFacts (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (typeArgs : List TyIdentifier) (e e' : Expression.Expr) (σ : RigidNames)
    (et : LExprT CoreLParams.mono) : Prop where
  /-- Every rigid constant carries the reserved prefix. -/
  prefixed : RigidNamesPrefixed σ
  /-- The rigid constants are distinct. -/
  nodup : (σ.map Prod.snd).Nodup
  /-- The renamed parameters are exactly the type parameters. -/
  map_fst : σ.map Prod.fst = typeArgs
  /-- No rigid constant is a registered type. -/
  unregistered : RigidNamesFresh C.knownTypes σ
  /-- No rigid constant is a type name in scope. -/
  not_scope : ∀ p ∈ σ, p.2 ∉ scopeTyNames C Env
  /-- No annotation of `e` names a rigid constant. -/
  annots : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true
  /-- The literal types of `e` are fixed by deskolemization. -/
  constTysFixed : ConstTysFixed σ e
  /-- The proposition skolemized by `σ` resolves at `bool`. -/
  resolves : resolveWithType (addSkolemTypes C σ) Env (skolemizeBody none σ e) LMonoTy.bool
    = .ok (et, Env')
  /-- The result is the deskolemized resolved proposition. -/
  out_eq : e' = finishDeskolemized σ Env'.stateSubstInfo.subst et
  /-- Every annotation type variable of the result is a type parameter. -/
  annotTyVars_in : ∀ v ∈ annotTyVars e', v ∈ typeArgs

/-- A successful proposition check finds no unbound annotation type variable in the
    proposition: every one is a type parameter. -/
private theorem typeCheckProp_scope_ok (scope : Thunk (Std.HashSet String))
    (kind : String) (name : CoreLabel) (typeArgs : List TyIdentifier)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (e e' : Expression.Expr)
    (tyNames : Unit → List String)
    (h : typeCheckProp scope kind name typeArgs C Env e tyNames = .ok (e', Env')) :
    WrittenTyVarScope.unboundAnnotVar? false typeArgs [] e = none := by
  unfold typeCheckProp at h
  simp only [bind, Except.bind] at h
  elim_err h with r hprop
  obtain ⟨out, stored, EnvR⟩ := r
  obtain ⟨et, hscope, -, -, -⟩ :=
    Function.checkBoolProp_ok_inv (Except.mapError_ok_h' hprop)
  exact hscope

/-- Suppose that, when there are type parameters, `scope` holds every type name in scope and
    `tyNames ()` lists every type name `e` mentions. Then a successful check of proposition `e`
    with type parameters `typeArgs` has a rigid renaming and resolved proposition with the
    facts of `TypeCheckPropFacts`. -/
private theorem typeCheckProp_success (scope : Thunk (Std.HashSet String))
    (kind : String) (name : CoreLabel) (typeArgs : List TyIdentifier)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (e e' : Expression.Expr)
    (tyNames : Unit → List String)
    (h : typeCheckProp scope kind name typeArgs C Env e tyNames
      = .ok (e', Env'))
    (hcov : typeArgs ≠ [] → ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (htn : typeArgs ≠ [] → ∀ n ∈ exprTyNames e, n ∈ tyNames ()) :
    ∃ (σ : RigidNames) (et : LExprT CoreLParams.mono),
      TypeCheckPropFacts C Env Env' typeArgs e e' σ et := by
  unfold typeCheckProp at h
  simp only [bind, Except.bind] at h
  elim_err h with r hprop
  obtain ⟨out, stored, EnvR⟩ := r
  elim_err h with hstored
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨et, -, hresolve, rfl, rfl⟩ :=
    Function.checkBoolProp_ok_inv (Except.mapError_ok_h' hprop)
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false] at hstored
  have hspec :=
    ScopeRigid.of_cover C Env scope (Thunk.pure ∅) name tyNames typeArgs hcov
  have hne : ∀ p ∈ rigidNamesAvoiding C scope (Thunk.pure ∅) name tyNames typeArgs,
      typeArgs ≠ [] := by
    intro p hp hnil
    have hmem := List.mem_map_of_mem (f := Prod.fst) hp
    rw [hspec.map_fst, hnil] at hmem
    exact List.not_mem_nil hmem
  refine ⟨_, et,
    { prefixed := hspec.prefixed
      nodup := hspec.nodup
      map_fst := hspec.map_fst
      unregistered := hspec.fresh
      not_scope := hspec.not_scope
      annots := ?_
      constTysFixed := ?_
      resolves := hresolve
      out_eq := rfl
      annotTyVars_in := annotTyVars_mem_of_tyVarsIn hstored }⟩
  · refine allExprTys_of_exprTyNames fun n hn => notRigidConst_of_ne fun p hp heq => ?_
    exact hspec.not_extra p hp (heq ▸ htn (hne p hp) n hn)
  · refine ConstTysFixed_of_exprTyNames fun p hp hn => ?_
    exact hspec.not_extra p hp (htn (hne p hp) _ hn)

/-- A successful axiom or lemma route is the declaration's proposition check in a pushed
    substitution scope, followed by popping it. -/
private theorem Decl.routeProp_success {d : Decl} {C : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {S : Std.HashSet String} {Env Env' : Expression.TyEnv}
    {fileRange : Strata.FileRange} {checked : Option Decl}
    (h : d.routePropBeforeRegistration S C Env fileRange = .ok (checked, Env')) :
    ∃ d' EnvR, checked = some d' ∧ Env' = EnvR.popSubstScope
      ∧ check S Env.pushEmptySubstScope = .ok (d', EnvR) := by
  simp only [Decl.routePropBeforeRegistration, hd, Except.mapError, bind, Except.bind] at h
  elim_err h with result hcheck
  obtain ⟨d', EnvR⟩ := result
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨d', EnvR, rfl, rfl, Except.mapError_ok_h' hcheck⟩

/-- The lemma `l` with its reserved type parameters renamed passes the proposition check against
    the type names `scope` with result `e'` and final environment `Env'`, its rigid constants
    avoiding the type names `l` mentions. -/
private abbrev Lemma.PropChecks (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (l : Lemma)
    (e' : Expression.Expr) : Prop :=
  typeCheckProp scope "lemma" l.name
    (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).typeArgs
    C Env (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).e
    (fun _ => exprTyNames l.e) = .ok (e', Env')

/-- A successful lemma check against the names `scope` has distinct type parameters and returns
    the lemma with its reserved type parameters renamed and its proposition replaced, where the
    renamed proposition passes the proposition check with the returned proposition as result. -/
private theorem Lemma.typeCheckIn_ok {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {l l' : Lemma}
    (h : Lemma.typeCheckIn scope C Env l = .ok (l', Env')) :
    l.typeArgs.Nodup
      ∧ (∃ e', l' = { l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)
        with e := e' })
      ∧ Lemma.PropChecks scope C Env Env' l l'.e := by
  unfold Lemma.typeCheckIn at h
  simp only [bind, Except.bind] at h
  elim_err h with _ hnodup
  elim_err h with r hprop
  obtain ⟨e', EnvR⟩ := r
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨checkTypeArgsNodup_ok hnodup, ⟨e', rfl⟩, hprop⟩

/-- A successful axiom or lemma check returns the declaration with a checked proposition `e'`:
    an axiom's proposition checks to `e'`, and a lemma passes the lemma check, returning the
    output lemma with proposition `e'`. -/
private theorem Decl.propCheck?_inv {d : Decl} {C : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {S : Std.HashSet String} {Env Env' : Expression.TyEnv}
    {d' : Decl} (h : check S Env = .ok (d', Env')) :
    ∃ e',
      (∀ a md, d = .ax a md → d' = .ax { a with e := e' } md ∧
        Axiom.typeCheckIn C Env a = .ok (e', Env')) ∧
      (∀ l md, d = .lemma l md → ∃ l', d' = .lemma l' md ∧ l'.e = e' ∧
        Lemma.typeCheckIn (Thunk.pure S) C Env l = .ok (l', Env')) := by
  cases d with
  | ax a md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    obtain ⟨⟨e', EnvA⟩, hax, hfin⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, rfl⟩ := hfin
    refine ⟨e', ?_, fun _ _ heq => nomatch heq⟩
    intro _ _ heq
    cases heq
    exact ⟨rfl, hax⟩
  | lemma l md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    obtain ⟨⟨l', EnvA⟩, hlem, hfin⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
    obtain ⟨rfl, rfl⟩ := hfin
    refine ⟨l'.e, (fun _ _ heq => nomatch heq), ?_⟩
    intro _ _ heq
    cases heq
    exact ⟨l', rfl, rfl, hlem⟩
  | _ => simp [Decl.propCheck?] at hd

/-- When a lemma declaration checks to a lemma with proposition `e'`, the input lemma with its
    reserved type parameters renamed passes the proposition check with result `e'`. -/
private theorem Decl.propCheck?_inv_propChecks {d d' : Decl}
    {scope : Thunk (Std.HashSet String)} {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {e' : Expression.Expr}
    (hlem : ∀ l md, d = .lemma l md → ∃ l', d' = .lemma l' md ∧ l'.e = e' ∧
      Lemma.typeCheckIn scope C Env l = .ok (l', Env')) :
    ∀ l md, d = .lemma l md → Lemma.PropChecks scope C Env Env' l e' :=
  fun l md hl => (hlem l md hl).elim fun _ h => h.2.1 ▸ (Lemma.typeCheckIn_ok h.2.2).2.2

/-- A successful axiom or lemma check is a proposition check against the type names in scope,
    under the declaration's name and with allowed type parameters, of the axiom's expression or
    of the expression of the lemma with its reserved type parameters renamed; when there are
    type parameters, the names the rigid constants avoid hold every type name of that
    expression. -/
private theorem Decl.propCheck?_ok {d : Decl} {C : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {scope : Thunk (Std.HashSet String)}
    {Env Env' : Expression.TyEnv} {e' : Expression.Expr}
    (hax : ∀ a md, d = .ax a md → Axiom.typeCheckIn C Env a = .ok (e', Env'))
    (hlem : ∀ l md, d = .lemma l md → Lemma.PropChecks scope C Env Env' l e') :
    ∃ (kind : String) (name : CoreLabel) (typeArgs : List TyIdentifier)
      (e : Expression.Expr) (tyNames : Unit → List String),
      typeCheckProp scope kind name typeArgs C Env e tyNames = .ok (e', Env')
      ∧ (typeArgs ≠ [] → ∀ n ∈ exprTyNames e, n ∈ tyNames ())
      ∧ (∀ a ∈ typeArgs, isAllowedName a = true)
      ∧ d.names = [(name : Expression.Ident)]
      ∧ (∀ a md, d = .ax a md → e = a.e)
      ∧ ∀ l md, d = .lemma l md →
        e = (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).e := by
  cases d with
  | ax a md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    refine ⟨"axiom", a.name, [], a.e, fun _ => [], hax a md rfl,
      fun hne => absurd rfl hne, List.forall_mem_nil _, rfl, ?_,
      fun _ _ heq => nomatch heq⟩
    intro _ _ heq
    cases heq
    rfl
  | lemma l md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    refine ⟨"lemma", l.name,
      (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).typeArgs,
      (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).e,
      fun _ => exprTyNames l.e, hlem l md rfl,
      fun _ _ hn => Lemma.exprTyNames_renameReservedTypeArgs C Env l _ ▸ hn,
      Lemma.renameReservedTypeArgs_typeArgs_allowed C Env l _, rfl,
      (fun _ _ heq => nomatch heq), ?_⟩
    intro _ _ heq
    cases heq
    rfl
  | _ => simp [Decl.propCheck?] at hd

/-- A successful axiom or lemma check returns a declaration with the input's names and kind. -/
private theorem Decl.propCheck?_names_kind {d : Decl} {C : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {S : Std.HashSet String} {Env Env' : Expression.TyEnv}
    {d' : Decl} (h : check S Env = .ok (d', Env')) :
    d'.names = d.names ∧ d'.kind = d.kind ∧ declNameKind d' = declNameKind d := by
  obtain ⟨e', hax, hlem⟩ := Decl.propCheck?_inv hd h
  cases d with
  | ax a md =>
    obtain ⟨rfl, -⟩ := hax a md rfl
    exact ⟨rfl, rfl, rfl⟩
  | lemma l md =>
    obtain ⟨l', rfl, -, hl⟩ := hlem l md rfl
    obtain ⟨-, ⟨_, rfl⟩, -⟩ := Lemma.typeCheckIn_ok hl
    have hname : (l.renameReservedTypeArgs C Env (fun _ => exprAnnotTys l.e)).name = l.name := by
      rw [Lemma.renameReservedTypeArgs_eq]
      rfl
    refine ⟨?_, rfl, rfl⟩
    simp only [Decl.names, hname]
    rfl
  | _ => simp [Decl.propCheck?] at hd

/-- A successful axiom or lemma check returns a declaration that is not a procedure. -/
private theorem Decl.propCheck?_kind_ne_proc {d : Decl} {C : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {S : Std.HashSet String} {Env Env' : Expression.TyEnv}
    {d' : Decl} (h : check S Env = .ok (d', Env')) :
    d'.kind ≠ DeclKind.proc := by
  rw [(Decl.propCheck?_names_kind hd h).2.1]
  cases d <;> simp [Decl.propCheck?, Decl.kind] at hd ⊢

/-- Resolving a proposition at `bool` in a pushed scope is resolution then unification; popping
    the scope gives a well-formed, closed environment finding the same variables as the input. -/
private theorem prop_resolve_facts
    (C : Expression.TyContext) (Env EnvA : Expression.TyEnv) (i : Identifiers Unit)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (hresolveWith : resolveWithType { C with idents := i } Env.pushEmptySubstScope e LMonoTy.bool
      = .ok (et, EnvA)) :
    ∃ (EnvR : Expression.TyEnv) (S : SubstInfo),
      EnvA = EnvR.updateSubst S
      ∧ SourceExpr.resolve { C with idents := i } Env.pushEmptySubstScope e = .ok (et, EnvR)
      ∧ Constraints.unify [(et.toLMonoTy, LMonoTy.bool)] EnvR.stateSubstInfo = .ok S
      ∧ TContext.FindEq (T := CoreLParams) (EnvR.updateSubst S).popSubstScope.context
          Env.context
      ∧ LExpr.TEnvWF (T := CoreLParams) (EnvR.updateSubst S).popSubstScope
      ∧ LExpr.checkContextTypesClosed (T := CoreLParams) (EnvR.updateSubst S).popSubstScope := by
  obtain ⟨EnvR, S, hresolve, hunify, hEnvA⟩ :=
    resolveWithType_decompose { C with idents := i } Env.pushEmptySubstScope EnvA
      e et LMonoTy.bool hresolveWith
  subst EnvA
  obtain ⟨hfe, hclosed⟩ :=
    SourceExpr.resolve_pushSubstScope_context_FindEq C Env e i et EnvR hresolve h_env h_fac
  have hfeOut : TContext.FindEq (T := CoreLParams)
      (EnvR.updateSubst S).popSubstScope.context Env.context := by
    simpa only [TEnv.updateSubst, TEnv.popSubstScope, TEnv.context] using hfe
  have h_wf_out : LExpr.TEnvWF (T := CoreLParams) (EnvR.updateSubst S).popSubstScope :=
    resolveWithType_pop_TEnvWF { C with idents := i } Env (EnvR.updateSubst S)
      e et hresolveWith h_env h_fac
  have h_closed_out : LExpr.checkContextTypesClosed (T := CoreLParams)
      (EnvR.updateSubst S).popSubstScope := by
    simpa only [TEnv.updateSubst, TEnv.popSubstScope, TEnv.context,
      LExpr.checkContextTypesClosed] using hclosed h_closed
  exact ⟨EnvR, S, rfl, hresolve, hunify, hfeOut, h_wf_out, h_closed_out⟩

/-- A typing of the skolemized `e` in the skolemized context gives one of `e` at the deskolemized
    type, over a scope that deskolemization leaves unchanged. -/
private theorem HasType_of_skolemizeBody
    (C : Expression.TyContext) (Γ : TContext Unit) (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) (hnd : (σ.map Prod.snd).Nodup)
    (e : Expression.Expr) (mty : LMonoTy)
    (h : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ) Γ (skolemizeBody none σ e)
      (.forAll [] mty))
    (h_amb : NoSkolemAmbient C Γ σ) (h_fwf : FactorySigWF C.functions)
    (h_aliasesWF : TContext.AliasesWF Γ) (h_mono : MonoScope Γ)
    (h_annots : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true)
    (h_lits : ConstTysFixed σ e) :
    LExpr.HasType (T := CoreLParams) C Γ e (.forAll [] (deskolemizeTy σ mty)) := by
  have hfind : ∀ k, (Γ.types.push (Strata.Util.HMap.ofList
      ([] : List (Lambda.Identifier Unit × LTy)))).find? k = Γ.types.find? k := by
    intro k
    simp only [Strata.Util.HMaps.push, Strata.Util.HMaps.find?, Strata.Util.HMap.find?,
      Strata.Util.HMap.ofList, Std.HashMap.ofList_nil, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_empty]
  have hsk : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
      { Γ with types := Γ.types.push (Strata.Util.HMap.ofList (([] : @LMonoTySignature Unit).map
          (fun q => (q.1, LTy.forAll [] (skolemizeTy σ q.2))))) }
      (skolemizeBody none σ e) (.forAll [] mty) :=
    HasType_FindEq _ _ _ _ _ ⟨hfind, rfl⟩ h
  have hrt : ∀ m ∈ ListMap.values ([] : @LMonoTySignature Unit),
      deskolemizeTy σ (skolemizeTy σ m) = m := by
    intro m hm
    simp [ListMap.values] at hm
  have hT := HasType_of_skolemScope_general C Γ σ hpfx [] e (skolemizeBody none σ e) mty hsk
    h_amb h_fwf h_aliasesWF h_mono hrt
    (allExprTys_annotNoRigidClash_skolemizeBody none σ e h_annots)
    (ConstTysFixed_skolemizeBody none h_lits)
    (mapExprTys_deskolemizeTy_skolemizeBody none hnd e h_annots)
  have hback : TContext.FindEq (T := CoreLParams) Γ
      { Γ with types := Γ.types.push (Strata.Util.HMap.ofList
          (([] : @LMonoTySignature Unit).map (fun q => (q.1, LTy.forAll [] q.2)))) } :=
    ⟨fun k => (hfind k).symm, rfl⟩
  exact HasType_FindEq _ _ _ _ _ hback hT

/-- The type names in scope do not depend on the registered identifiers. -/
private theorem scopeTyNames_setIdents (D : Expression.TyContext) (j : Identifiers Unit)
    (E : Expression.TyEnv) : scopeTyNames { D with idents := j } E = scopeTyNames D E :=
  scopeTyNames_congr rfl rfl

/-- A set holding every type name in scope in `C` and `Env` holds every one in scope in `C` and
    any environment with the same type context as `Env`. -/
private theorem scopeTyNames_cover_of_context_eq {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {S : Std.HashSet String} (hc : Env'.context = Env.context)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) : ∀ n ∈ scopeTyNames C Env', n ∈ S := by
  rw [scopeTyNames_congr rfl hc]
  exact hcov

/-- The type names in scope do not depend on the registered identifiers or on a pushed
    substitution scope, so a set holding every type name in scope in `C` and `Env` holds every
    type name in scope in `C` with any identifiers and `Env` with a pushed substitution scope. -/
private theorem scopeTyNames_cover_idents_push {C : Expression.TyContext}
    {Env : Expression.TyEnv} {S : Std.HashSet String} (i : Identifiers Unit)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    ∀ n ∈ scopeTyNames { C with idents := i } Env.pushEmptySubstScope, n ∈ S := by
  rw [scopeTyNames_setIdents]
  exact scopeTyNames_cover_of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hcov

/-- Inversion of an accepted declaration step at an axiom or a lemma: its proposition check
    succeeds in a pushed substitution scope. -/
private theorem Program.typeCheck.stepThen_prop_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (d : Decl) {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? { C with idents := i } = some check)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env d k = .ok res) :
    ∃ (idents : Identifiers Unit) (d' : Decl) (EnvA : Expression.TyEnv),
      (∃ f, Identifiers.addListWithError i d.names f = .ok idents)
      ∧ check S Env.pushEmptySubstScope = .ok (d', EnvA)
      ∧ k d' { C with idents := idents } EnvA.popSubstScope S = .ok res := by
  simp only [Program.typeCheck.stepThen] at h
  obtain ⟨routed, hroute, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨checked, Env2⟩ := routed
  obtain ⟨d', EnvA, rfl, rfl, hcheck⟩ := Decl.routeProp_success hd hroute
  cases d <;> simp only [Decl.propCheck?, reduceCtorEq] at hd
  all_goals
    obtain ⟨routedDistinct, hrouteDistinct, h⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [Decl.routeDistinctBeforeRegistration, Except.ok.injEq] at hrouteDistinct
    subst routedDistinct
    obtain ⟨idents, hidents, h⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨step, hstep, hrec⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [Option.getD_some, Except.ok.injEq] at hstep
    subst step
    exact ⟨idents, d', EnvA, ⟨_, hidents⟩, hcheck, hrec⟩

/-- An axiom or lemma declaration whose proposition check succeeds satisfies the typechecker spec
    with contexts unchanged. The check runs in a context with the rigid type variables of `C`
    and an environment with the variables of `Γ`. The proposition `e` must have type `bool`,
    have valid written annotations, and have every annotation type variable in any list `ps`
    for which the scope check finds no unbound annotation variable. -/
private theorem DeclHasType_checkedProp (P : Program)
    (C : Expression.TyContext) (Γ : TContext Unit) {d : Decl} {C' : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C' = some check) {scope : Thunk (Std.HashSet String)}
    {Env Env' : Expression.TyEnv} {e e' : Expression.Expr}
    (hrigid : C.rigidTypeVars = C'.rigidTypeVars)
    (hctx : TContext.FindEq (T := CoreLParams) Γ Env.context)
    (hcheckAx : ∀ a md, d = .ax a md →
      Axiom.typeCheckIn C' Env a = .ok (e', Env'))
    (hcheckLem : ∀ l md, d = .lemma l md →
      ∃ l', Lemma.typeCheckIn scope C' Env l = .ok (l', Env'))
    (ht : LExpr.HasType C Γ e (.forAll [] .bool)) (ha : WrittenAnnotsOk C Γ e)
    (hax : ∀ a md, d = .ax a md → e = a.e)
    (hlem : ∀ l md, d = .lemma l md →
      e = (l.renameReservedTypeArgs C' Env (fun _ => exprAnnotTys l.e)).e)
    (hs : ∀ ps, WrittenTyVarScope.unboundAnnotVar? false ps [] e = none →
      AnnotsInScope ps (fun _ => none) e) :
    DeclHasType P C Γ d C Γ := by
  cases d with
  | ax a md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    have hscope := typeCheckProp_scope_ok _ "axiom" a.name [] C' Env Env' a.e e' _
      (hcheckAx a md rfl)
    obtain rfl : e = a.e := hax a md rfl
    exact DeclHasType.ax C Γ _ md ht ha (hs [] hscope)
  | lemma l md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    obtain ⟨l', hl⟩ := hcheckLem l md rfl
    obtain ⟨hnodup, -, hprop⟩ := Lemma.typeCheckIn_ok hl
    have hscope := typeCheckProp_scope_ok _ "lemma" l.name _ C' Env Env' _ _ _ hprop
    obtain rfl : e = (l.renameReservedTypeArgs C' Env (fun _ => exprAnnotTys l.e)).e :=
      hlem l md rfl
    obtain ⟨hren, hnodupR⟩ :=
      Lemma.renameReservedTypeArgs_tyArgRenaming C' Env l (fun _ => exprAnnotTys l.e) hnodup
    have hrenC := TyArgRenaming.congr hrigid hctx hren
    exact DeclHasType.lemma C Γ _ _ md ⟨_, hrenC, Lemma.renameReservedTypeArgs_eq C' Env l _⟩ ht
      ha hnodupR (Lemma.renameReservedTypeArgs_typeArgs_allowed C' Env l _) (hs _ hscope)
  | _ => simp [Decl.propCheck?] at hd

/-- An axiom or lemma step, resolved and unified at `bool` in a pushed substitution scope that is
    then popped, preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.prop_step {C D : Expression.TyContext}
    {Env EnvR : Expression.TyEnv} {i idents : Identifiers Unit} {l : List Expression.Ident}
    {f : Expression.Ident → Strata.Message} {e : Expression.Expr} {et : LExprT CoreLParams.mono}
    {S : SubstInfo} (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : Identifiers.addListWithError i l f = .ok idents)
    (hresolve : SourceExpr.resolve D Env.pushEmptySubstScope e = .ok (et, EnvR))
    (hunify : Constraints.unify [(et.toLMonoTy, LMonoTy.bool)] EnvR.stateSubstInfo = .ok S)
    (hfeOut : TContext.FindEq (T := CoreLParams) (EnvR.updateSubst S).popSubstScope.context
      Env.context)
    (hwfOut : LExpr.TEnvWF (T := CoreLParams) (EnvR.updateSubst S).popSubstScope)
    (hclosedOut : LExpr.checkContextTypesClosed (T := CoreLParams)
      (EnvR.updateSubst S).popSubstScope) :
    TypeCheckLoopInvariant Q C (EnvR.updateSubst S).popSubstScope idents := by
  refine ⟨hwfOut, hinv.factory, hclosedOut, ?_, ?_,
    AliasRegistryCoherent.step_of_context_eq hidents hfeOut.2 rfl hinv.coherent,
    AmbientClear.prop_step hresolve hunify hinv.clear⟩
  · intro al hal
    rw [hfeOut.2] at hal
    exact hinv.aliasBodies al hal
  · intro z tz hfind
    rw [hfeOut.find? z] at hfind
    exact hinv.mono z tz hfind

/-- An axiom or lemma step accepted against a set holding every type name in scope satisfies the
    typechecker spec, preserves the input invariant, and continues the walk. -/
private theorem prop_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? { C with idents := i } = some check)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env d k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context d C2 Env.context
        ∧ TContext.FindEq (T := CoreLParams) Env2.context Env.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, d', EnvA, ⟨regMsg, hidents⟩, hcheck, hrec⟩ :=
    Program.typeCheck.stepThen_prop_inversion program C Env i d k res hd h
  obtain ⟨e', hcheckAx, hcheckLem⟩ := Decl.propCheck?_inv hd hcheck
  obtain ⟨kind, name, typeArgs, e, tyNames, hprop, htn, hta, -, hax, hlem⟩ :=
    Decl.propCheck?_ok hd (fun a md ha => (hcheckAx a md ha).2)
      (Decl.propCheck?_inv_propChecks hcheckLem)
  obtain ⟨σ, et, hfacts⟩ :=
    typeCheckProp_success _ kind name typeArgs _ _ _ e e' tyNames hprop
      (fun _ => scopeTyNames_cover_idents_push i hcov) htn
  have hpfx := hfacts.prefixed
  have hnd := hfacts.nodup
  have hfst := hfacts.map_fst
  have hscopeNames := hfacts.not_scope
  have hannots := hfacts.annots
  have hlits := hfacts.constTysFixed
  have hresolveWith := hfacts.resolves
  have hrig : ∀ p ∈ σ, TyVarAdmissibility.notGeneratedOrRigid p.1 = true := by
    intro p hp
    have hmem := List.mem_map_of_mem (f := Prod.fst) hp
    rw [hfst] at hmem
    exact TyVarAdmissibility.notGeneratedOrRigid_of_isAllowedName (hta _ hmem)
  obtain ⟨EnvR, TS, rfl, hresolve, hunify, hfeOut, h_wf_out, h_closed_out⟩ :=
    prop_resolve_facts (addSkolemTypes C σ) Env EnvA i (skolemizeBody none σ e) et hinv.envWF
      (hQ.sigWF _ hinv.factory) hinv.ctxClosed hresolveWith
  have h_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have h_closed_push : LExpr.checkContextTypesClosed (T := CoreLParams)
      Env.pushEmptySubstScope := by
    simpa only [TEnv.pushEmptySubstScope, LExpr.checkContextTypesClosed, TEnv.context] using
      hinv.ctxClosed
  have h_ws : LExpr.WellScoped (skolemizeBody none σ e) Env.pushEmptySubstScope.context :=
    resolveWithType_WellScoped _ _ _ _ _ _ hresolveWith
  have h_type_subst := resolveWithType_HasType_bool { addSkolemTypes C σ with idents := i }
    Env.pushEmptySubstScope (EnvR.updateSubst TS) _ et hresolveWith h_push (hQ.sigWF _ hinv.factory)
    h_ws (MonoScope_of_invariant C Env hinv)
  have h_type_push : LExpr.HasType (T := CoreLParams) { addSkolemTypes C σ with idents := i }
      Env.pushEmptySubstScope.context (skolemizeBody none σ e) (.forAll [] LMonoTy.bool) :=
    HasType_FindEq _ _ _ _ _
      (LExpr.TContext.FindEq_subst_of_closed (T := CoreLParams)
        Env.pushEmptySubstScope.context _
        (LExpr.ctx_closed_of_check (T := CoreLParams) Env.pushEmptySubstScope h_closed_push))
      h_type_subst
  have h_type_sk : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ) Env.context
      (skolemizeBody none σ e) (.forAll [] LMonoTy.bool) := by
    have h_type_base := HasType_idents_irrel (addSkolemTypes C σ) i
      Env.pushEmptySubstScope.context _ _ h_type_push
    simpa only [TEnv.pushEmptySubstScope_context_eq] using h_type_base
  have h_amb : NoSkolemAmbient C Env.context σ := NoSkolemAmbient.of_prop hpfx hscopeNames
  have h_type : LExpr.HasType (T := CoreLParams) C Env.context e (.forAll [] LMonoTy.bool) := by
    have h_type_e := HasType_of_skolemizeBody C Env.context σ hpfx hnd e .bool h_type_sk h_amb
      (hQ.sigWF _ hinv.factory) hinv.envWF.aliasesWF hinv.mono hannots hlits
    rwa [deskolemizeTy_bool hpfx] at h_type_e
  have h_annots : WrittenAnnotsOk C Env.context e := by
    have hfvar := resolveWithType_fvarAnnotsWF _ _ _ _ _ _ hresolveWith
    have hbinder := resolveWithType_binderAnnotTyVarsAdmissible _ _ _ _ _ _ hresolveWith
    rw [TEnv.pushEmptySubstScope_context_eq] at hfvar
    rw [← mapExprTys_deskolemizeTy_skolemizeBody none hnd e hannots]
    exact ⟨TypeSpec.FVarAnnotsWF.deskolemize σ
      (Csk := addSkolemTypes ({ C with idents := i } : Expression.TyContext) σ) (Crig := C)
      (fun _ => rfl) h_amb.aliases hrig hfvar,
      TypeSpec.BinderAnnotTyVarsAdmissible.deskolemize σ hrig hbinder⟩
  have hdecl := DeclHasType_checkedProp program C Env.context hd
    (scope := Thunk.pure S) (Env := Env.pushEmptySubstScope) rfl (TContext.FindEq.refl _)
    (fun a md ha => (hcheckAx a md ha).2)
    (fun l md hl => (hcheckLem l md hl).imp fun _ h => h.2.2)
    h_type h_annots hax hlem
    fun _ hu => annotsInScope_of_unboundAnnotVar? (m := []) (fun _ _ hl => nomatch hl) hu
  exact ⟨idents, C, (EnvR.updateSubst TS).popSubstScope, _, hdecl, hfeOut,
    TypeCheckLoopInvariant.prop_step hinv hidents hresolve hunify hfeOut h_wf_out h_closed_out,
    ⟨_, hrec⟩⟩

/-- An accepted declaration step at a distinctness declaration registers its name, checks its
    expressions in a pushed variable and substitution scope, and continues with the checked
    declaration. -/
private theorem Program.typeCheck.stepThen_distinct_route
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (l : Expression.Ident) (es : List Expression.Expr) (md : MetaData Expression) {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S C Env (Decl.distinct l es md) k
          = .ok res) :
    ∃ (idents : Identifiers Unit) (es' : List Expression.Expr) (EnvR : Expression.TyEnv),
      (∃ f, Identifiers.addListWithError C.idents (Decl.distinct l es md).names f = .ok idents)
      ∧ Distinct.typeCheck C Env.pushEmptyContext.pushEmptySubstScope l es = .ok (es', EnvR)
      ∧ k (Decl.distinct l es' md) { C with idents := idents }
          ((EnvR.popSubstScope.popContext).updateContext Env.context) S = .ok res := by
  simp only [Program.typeCheck.stepThen] at h
  obtain ⟨routedProp, hrouteProp, h⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Decl.routePropBeforeRegistration, Decl.propCheck?, Except.ok.injEq] at hrouteProp
  have hroutedProp : routedProp = (none, Env) := hrouteProp.symm
  subst routedProp
  obtain ⟨routedDistinct, hrouteDistinct, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨idents, hidents, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨step, hstep, hrec⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨checked, EnvOut⟩ := routedDistinct
  obtain ⟨es', EnvR, hchecked, hEnvOut, hcheck⟩ :=
    Decl.routeDistinct_success C Env EnvOut l es md _ checked hrouteDistinct
  subst checked
  subst EnvOut
  simp only [Option.getD_some, Except.ok.injEq] at hstep
  obtain ⟨rfl, rfl, rfl⟩ := hstep
  exact ⟨idents, es', EnvR, ⟨_, hidents⟩, hcheck, hrec⟩

/-- Inversion of one accepted declaration step at a distinctness declaration, with any
    continuation `k`. -/
private theorem Program.typeCheck.stepThen_distinct_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (l : Expression.Ident) (es : List Expression.Expr)
    (md : MetaData Expression) {α : Type}
    {PS : Thunk (Std.HashSet String)} {TS : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h : Program.typeCheck.stepThen program PS TS { C with idents := i } Env
          (Decl.distinct l es md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (ets : List (LExprT CoreLParams.mono))
      (EnvR : Expression.TyEnv) (S : SubstInfo) (sharedTy : LMonoTy),
      (∃ f, Identifiers.addListWithError i (Decl.distinct l es md).names f = .ok idents)
      ∧ (∀ e ∈ es, WrittenTyVarScope.unboundAnnotVar? false [] [] e = none)
      ∧ SourceExpr.resolves { C with idents := i } Env.pushEmptyContext.pushEmptySubstScope es
          = .ok (ets, EnvR)
      ∧ Constraints.unify (Distinct.sharedTypeConstraints ets) EnvR.stateSubstInfo = .ok S
      ∧ (∀ et ∈ ets, LMonoTy.subst S.subst et.toLMonoTy = sharedTy)
      ∧ (∀ e ∈ ets.map (fun et => LExpr.unresolved (LExpr.applySubstT et S.subst)),
          annotTyVars e = [])
      ∧ ets.length = es.length
      ∧ (∀ idx (hi : idx < es.length) (hj : idx < ets.length),
          ∃ (Ei Ei' : Expression.TyEnv),
            SourceExpr.resolve { C with idents := i } Ei (es)[idx] = .ok (ets[idx], Ei')
            ∧ LExpr.TEnvWF (T := CoreLParams) Ei
            ∧ TContext.Equiv (T := CoreLParams) Ei.context
                Env.pushEmptyContext.pushEmptySubstScope.context
            ∧ Ei.context.types ≠ []
            ∧ Subst.absorbs EnvR.stateSubstInfo.subst Ei'.stateSubstInfo.subst)
      ∧ LExpr.TEnvWF (T := CoreLParams)
          ((EnvR.popSubstScope.popContext).updateContext Env.context)
      ∧ k (Decl.distinct l (ets.map fun et => LExpr.unresolved (LExpr.applySubstT et S.subst)) md)
          { C with idents := idents }
          ((EnvR.popSubstScope.popContext).updateContext Env.context) TS = .ok res := by
  obtain ⟨idents, es', EnvR, hidents, hcheck, hrec⟩ :=
    Program.typeCheck.stepThen_distinct_route program { C with idents := i } Env l es md k res h
  obtain ⟨ets, S, hresolve, hunify, hout, hstored, hscope⟩ :=
    Distinct.typeCheck_success { C with idents := i }
      Env.pushEmptyContext.pushEmptySubstScope EnvR l es es' hcheck
  subst es'
  obtain ⟨sharedTy, hshared⟩ :=
    Distinct.sharedTypeConstraints_sound ets EnvR.stateSubstInfo S hunify
  let Env0 := Env.pushEmptyContext.pushEmptySubstScope
  have hwf0 : LExpr.TEnvWF (T := CoreLParams) Env0 :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env.pushEmptyContext
      (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env h_env)
  have hsource := hresolve
  change SourceExpr.resolves { C with idents := i } Env0 es = .ok (ets, EnvR) at hsource
  have htypes0 : Env0.context.types ≠ [] := by
    simpa only [Env0, TEnv.pushEmptySubstScope, TEnv.context] using
      (TEnv.pushEmptyContext_types_ne_nil (T := CoreLParams) Env)
  obtain ⟨hwfR, -, hctxRNe, -, hlen, hperNe⟩ :=
    SourceExpr.resolves_step { C with idents := i } Env0 EnvR es ets hresolve hwf0 h_fac
  have hctxR := hctxRNe htypes0
  have hgen : Env.genEnv.genState.tyGen ≤ EnvR.genEnv.genState.tyGen := by
    have hmono := SourceExpr.resolves_genState_tyGen_mono
      { C with idents := i } Env0 EnvR es ets hsource
    simpa only [Env0, TEnv.pushEmptySubstScope, TEnv.pushEmptyContext,
      TEnv.updateContext, TEnv.context] using hmono
  have hctxPop : TContext.Equiv (T := CoreLParams)
      (EnvR.popSubstScope.popContext).context Env.context := by
    refine ⟨?_, ?_⟩
    · simp only [TEnv.popSubstScope, TEnv.popContext, TEnv.updateContext, TEnv.context,
        Env0, TEnv.pushEmptySubstScope, TEnv.pushEmptyContext, Strata.Util.HMaps.push,
        Strata.Util.HMaps.pop] at hctxR ⊢
      exact Strata.Util.HMaps.Equiv.pop hctxR.1
    · simpa only [TEnv.popSubstScope, TEnv.popContext, TEnv.updateContext, TEnv.context,
        Env0, TEnv.pushEmptySubstScope, TEnv.pushEmptyContext] using hctxR.2
  have hwfPopSubst : LExpr.TEnvWF (T := CoreLParams) EnvR.popSubstScope :=
    popSubstScope_preserves_TEnvWF (T := CoreLParams) EnvR hwfR
  have hwfPop : LExpr.TEnvWF (T := CoreLParams) EnvR.popSubstScope.popContext :=
    popContext_preserves_TEnvWF (T := CoreLParams) Env EnvR.popSubstScope
      h_env hwfPopSubst hgen hctxPop
  have hwfOut : LExpr.TEnvWF (T := CoreLParams)
      ((EnvR.popSubstScope.popContext).updateContext Env.context) :=
    updateContext_preserves_TEnvWF_of_mono Env EnvR.popSubstScope.popContext
      h_env hwfPop hgen
  refine ⟨idents, ets, EnvR, S, sharedTy, hidents, hscope, hsource,
    hunify, hshared, hstored, hlen, ?_, hwfOut, hrec⟩
  intro idx hi hj
  obtain ⟨Ei, Ei', hri, hwfi, -, heqNe, habsi⟩ := hperNe idx hi hj
  exact ⟨Ei, Ei', hri, hwfi, (heqNe htypes0).1, (heqNe htypes0).2, habsi⟩

/-- An accepted distinctness step preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.distinct_step [hQ : WalkFactoryClosed Q]
    {C : Expression.TyContext} {Env EnvR : Expression.TyEnv} {i idents : Identifiers Unit}
    {l : Expression.Ident} {es : List Expression.Expr} {md : MetaData Expression}
    {ets : List (LExprT CoreLParams.mono)} (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : ∃ f, Identifiers.addListWithError i (Decl.distinct l es md).names f = .ok idents)
    (hsource : SourceExpr.resolves { C with idents := i }
      Env.pushEmptyContext.pushEmptySubstScope es = .ok (ets, EnvR))
    (hwfOut : LExpr.TEnvWF (T := CoreLParams)
      ((EnvR.popSubstScope.popContext).updateContext Env.context)) :
    TypeCheckLoopInvariant Q C ((EnvR.popSubstScope.popContext).updateContext Env.context)
      idents := by
  obtain ⟨regMsg, hidents⟩ := hidents
  obtain ⟨hwfIn, hfac, hclosed, halBodies, hmono, hcoh, hclear⟩ := hinv
  refine ⟨hwfOut, hfac, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [TEnv.updateContext, LExpr.checkContextTypesClosed, TEnv.context] using hclosed
  · simpa only [TEnv.updateContext, TEnv.context] using halBodies
  · simpa only [TEnv.updateContext, TEnv.context] using hmono
  · exact AliasRegistryCoherent.step_of_context_eq
      (Env := Env)
      (Env2 := (EnvR.popSubstScope.popContext).updateContext Env.context)
      hidents rfl rfl hcoh
  · exact SourceExpr.resolves_tailClear _ _ _ EnvR _ hsource
      (pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env.pushEmptyContext
        (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env hwfIn)) (hQ.sigWF _ hfac)
      (TailClear.push hclear _)

/-- An accepted distinctness step satisfies the typechecker spec, preserves the input invariant,
    and continues the walk. -/
private theorem distinct_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (l : Expression.Ident) (es : List Expression.Expr) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {TS : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (h : Program.typeCheck.stepThen program PS TS { C with idents := i } Env
          (Decl.distinct l es md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.distinct l es md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, ets, EnvR, S, sharedTy, ⟨regMsg, hidents⟩, hscope,
    hsourceAll, -, hshared, -, hlen, hper, hwfOut, hrec⟩ :=
    Program.typeCheck.stepThen_distinct_inversion program C Env i l es md k res hinv.envWF
      (hQ.sigWF _ hinv.factory) h
  let Env0 := Env.pushEmptyContext.pushEmptySubstScope
  have hclosed0 : LExpr.checkContextTypesClosed (T := CoreLParams) Env0 := by
    simpa only [Env0, LExpr.checkContextTypesClosed, TEnv.pushEmptySubstScope_context_eq] using
      (Lambda.pushEmptyContext_preserves_closed (T := CoreLParams) Env hinv.ctxClosed)
  refine ⟨idents, C, (EnvR.popSubstScope.popContext).updateContext Env.context,
    Decl.distinct l
      (ets.map fun et => LExpr.unresolved (LExpr.applySubstT et S.subst)) md,
    ?_, TypeCheckLoopInvariant.distinct_step hinv ⟨regMsg, hidents⟩ hsourceAll hwfOut,
    ⟨_, hrec⟩⟩
  · simp only [TEnv.updateContext, TEnv.context]
    have hfind : TContext.FindEq (T := CoreLParams) Env.context Env0.context := by
      simpa only [Env0, TEnv.pushEmptySubstScope_context_eq] using
        (pushEmptyContext_context_FindEq (T := CoreLParams) Env).symm
    have hkeys : LExpr.Subst.allKeysFresh (T := CoreLParams) S.subst Env.context :=
      LExpr.Subst.allKeysFresh_of_ctx_closed
        (LExpr.ctx_closed_of_check (T := CoreLParams) Env hinv.ctxClosed)
    have hmember : ∀ e ∈ es, WrittenAnnotsOk C Env.context e
        ∧ LExpr.HasType (T := CoreLParams) C Env.context e (.forAll [] sharedTy) := by
      intro e he
      obtain ⟨idx, hi, rfl⟩ := List.mem_iff_getElem.mp he
      let ei : Expression.Expr := List.get es ⟨idx, hi⟩
      have hj : idx < ets.length := by simpa only [hlen] using hi
      obtain ⟨Ei, Ei', hri, hwfi, heqi, -, -⟩ := hper idx hi hj
      have hsourcei := hri
      change SourceExpr.resolve { C with idents := i } Ei ei =
        .ok (ets[idx], Ei') at hsourcei
      have hannotsi : WrittenAnnotsOk { C with idents := i }
          Ei.context ei :=
        ⟨SourceExpr.resolve_fvarAnnotsWF _ _ _ _ _ hsourcei,
          SourceExpr.resolve_binderAnnotTyVarsAdmissible _ _ _ _ _ hsourcei⟩
      have hwsi : LExpr.WellScoped ei Ei.context :=
        SourceExpr.resolve_WellScoped _ Ei Ei' ei ets[idx] hsourcei
      have hclosedi : LExpr.checkContextTypesClosed (T := CoreLParams) Ei :=
        LExpr.checkContextTypesClosed_of_ctx_eq hclosed0 heqi
      obtain ⟨EiDirect, hriDirect, -⟩ := SourceExpr.resolve_decompose
        { C with idents := i } Ei Ei' ei ets[idx] hsourcei
      have htyi := (LExpr.resolve_HasType_toLMonoTy ei ets[idx]
        { C with idents := i } Ei EiDirect hriDirect hwfi
        (hQ.sigWF _ hinv.factory) hwsi hclosedi).1
      have hty0 : LExpr.HasType (T := CoreLParams) { C with idents := i }
          Env0.context ei (.forAll [] ets[idx].toLMonoTy) :=
        HasType_Equiv htyi heqi
      have htyBase : LExpr.HasType (T := CoreLParams) { C with idents := i }
          Env.context ei (.forAll [] ets[idx].toLMonoTy) :=
        HasType_FindEq { C with idents := i } Env0.context Env.context ei
          (.forAll [] ets[idx].toLMonoTy) hfind hty0
      have htySub : LExpr.HasType (T := CoreLParams) { C with idents := i }
          Env.context ei (.forAll [] (LMonoTy.subst S.subst ets[idx].toLMonoTy)) :=
        LExpr.HasType_subst_fresh_all { C with idents := i } Env.context ei
          ets[idx].toLMonoTy S.subst htyBase (fun a ha _ => hkeys a ha) S.isWF
      rw [hshared ets[idx] (List.getElem_mem hj)] at htySub
      exact ⟨writtenAnnotsOk_of_aliases_eq (hfind.2.trans heqi.2.symm)
          (writtenAnnotsOk_idents_irrel C i Ei.context ei hannotsi),
        HasType_idents_irrel C i Env.context ei (.forAll [] sharedTy) htySub⟩
    exact DeclHasType.distinct C Env.context l es md
      ⟨sharedTy, fun e he => (hmember e he).2⟩ (fun e he => (hmember e he).1)
      fun e he => annotsInScope_of_unboundAnnotVar? (m := []) (fun _ _ hl => nomatch hl)
        (hscope e he)

/-- Inversion of one accepted declaration step at a procedure declaration, with any continuation
    `k`. -/
private theorem Program.typeCheck.stepThen_proc_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (proc : Procedure) (md : MetaData Expression) {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.proc proc md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (proc' : Procedure) (Env2 : Expression.TyEnv),
      Procedure.typeCheckIn (Thunk.pure S) PS
          { C with idents := idents } Env.pushEmptySubstScope program proc md
          = .ok (proc', Env2)
      ∧ TEnv.context Env2.popSubstScope = TEnv.context Env
      ∧ (∀ n : String, n ∈ i → n ∈ idents)
      ∧ k (Decl.proc proc' md)
          { C with idents := idents } Env2.popSubstScope S = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration, bind, Except.bind, tryCatch, tryCatchThe,
    MonadExceptOf.tryCatch, Except.tryCatch] at h
  elim_err h with idents hidents
  elim_err h with v heq
  elim_err heq with w hinner
  elim_err hinner with x htc
  obtain ⟨proc', Env2⟩ := x
  simp only [Except.ok.injEq] at heq hinner
  subst heq hinner
  simp only at h
  exact ⟨idents, proc', Env2, htc,
    Procedure.typeCheckIn_context_eq _ _ { C with idents := idents } Env.pushEmptySubstScope Env2
      program proc proc' md htc,
    Identifiers.addListWithError_mem_mono hidents, h⟩

/-- After an accepted procedure check from an environment with a pushed substitution scope,
    popping that scope gives a well-formed state with the incoming context, whose scopes stay
    closed and monotype. -/
private theorem proc_step_popped {sc ps : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env Env2 : Expression.TyEnv}
    {program : Program} {proc proc' : Procedure} {md : MetaData Expression}
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context)
    (htc : Procedure.typeCheckIn sc ps C Env.pushEmptySubstScope program proc md
            = .ok (proc', Env2)) :
    LExpr.TEnvWF (T := CoreLParams) Env2.popSubstScope
      ∧ TEnv.context Env2.popSubstScope = TEnv.context Env
      ∧ LExpr.checkContextTypesClosed (T := CoreLParams) Env2.popSubstScope
      ∧ MonoScope Env2.popSubstScope.context := by
  have hctxeq : TEnv.context Env2.popSubstScope = TEnv.context Env :=
    Procedure.typeCheckIn_context_eq sc ps C Env.pushEmptySubstScope Env2 program proc proc' md htc
  have hwf_tc : LExpr.TEnvWF (T := CoreLParams) Env2 :=
    Procedure.typeCheckIn_preserves_TEnvWF sc ps C Env.pushEmptySubstScope Env2 program proc proc'
      md htc
      (pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env)
  exact ⟨popSubstScope_preserves_TEnvWF (T := CoreLParams) Env2 hwf_tc, hctxeq,
    scopeFacts_of_context_eq hctxeq h_closed h_mono⟩

/-- An accepted procedure step preserves the input loop invariant. -/
private theorem TypeCheckLoopInvariant.proc_step (sc ps : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env2 : Expression.TyEnv) (idents : Identifiers Unit)
    (program : Program) (proc proc' : Procedure) (md : MetaData Expression) {i : Identifiers Unit}
    (hinv : TypeCheckLoopInvariant Q C Env i) (hreg : ∀ n : String, n ∈ i → n ∈ idents)
    (htc : Procedure.typeCheckIn sc ps { C with idents := idents } Env.pushEmptySubstScope program
            proc md = .ok (proc', Env2)) :
    TypeCheckLoopInvariant Q C Env2.popSubstScope idents := by
  obtain ⟨hwf, hctxeq, hcl, hmo⟩ := proc_step_popped hinv.envWF hinv.ctxClosed
    hinv.mono htc
  exact ⟨hwf, hinv.factory, hcl, hctxeq ▸ hinv.aliasBodies, hmo,
    AliasRegistryCoherent.of_aliases_eq (by rw [hctxeq])
      (AliasRegistryCoherent.of_idents_mem hreg hinv.coherent),
    AmbientClear.proc_step htc hinv.clear⟩

/-- An accepted procedure step preserves the output loop invariant. -/
private theorem TypeCheckLoopInvariantOutput.proc_step (sc ps : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env Env2 : Expression.TyEnv) (idents : Identifiers Unit)
    (program : Program) (proc proc' : Procedure) (md : MetaData Expression) {i : Identifiers Unit}
    (hinv : TypeCheckLoopInvariantOutput Q C Env i) (hreg : ∀ n : String, n ∈ i → n ∈ idents)
    (htc : Procedure.typeCheckIn sc ps { C with idents := idents } Env.pushEmptySubstScope program
            proc md = .ok (proc', Env2)) :
    TypeCheckLoopInvariantOutput Q C Env2.popSubstScope idents :=
  ⟨TypeCheckLoopInvariant.proc_step sc ps C Env Env2 idents program proc proc' md
      hinv.toTypeCheckLoopInvariant hreg htc,
    KnownTypesReady.proc_step sc ps C Env Env2 idents program proc proc' md htc hinv.ready⟩

/-- A procedure step accepted against a set holding every type name in scope, and a set holding
    every type name of the procedure signatures, satisfies the typechecker spec, preserves the
    input invariant, and continues the walk. -/
private theorem proc_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (proc : Procedure) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hsigs : ProcSigsDeclared program)
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get)
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.proc proc md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.proc proc md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, proc', Env2, htc, hctxeq, hregmono, hrec⟩ :=
    Program.typeCheck.stepThen_proc_inversion program C Env i proc md k res h
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have haliasFresh : ∀ al ∈ Env.pushEmptySubstScope.context.aliases,
      KnownTypes.containsName ({ C with idents := idents } : Expression.TyContext).knownTypes
        al.name = false := by
    intro al hal
    refine Bool.eq_false_iff.mpr fun htrue => ?_
    rw [TEnv.pushEmptySubstScope_context_eq Env] at hal
    exact hinv.coherent.freshForKnownTypes al hal
      ((KnownTypes.containsName_eq_true_iff_mem _ _).mp htrue)
  have hsound :=
    Procedure.typeCheckIn_sound _ _ { C with idents := idents } Env.pushEmptySubstScope
      Env2 program proc proc' md htc
      (scopeTyNames_cover_idents_push idents hcov) hP hwf_push (hQ.sigWF _ hinv.factory)
      hinv.ctxClosed
      (MonoScope_of_invariant C Env hinv) haliasFresh hsigs
      ((SubstClear.push_empty hinv.clear).varsAvoid _)
  refine ⟨idents, C, Env2.popSubstScope, Decl.proc proc' md, ?_, ?_, ⟨_, hrec⟩⟩
  · rw [hctxeq]
    obtain ⟨procR, hv, hsoundR⟩ := hsound
    have hvC : ProcAlphaVariant C Env.context proc procR :=
      ProcAlphaVariant.congr rfl (TContext.FindEq.refl _) hv
    exact DeclHasType.proc C Env.context proc md
      ⟨procR, hvC, ProcHasTypeExact_idents_irrel program C idents Env.context procR hsoundR⟩
  · exact TypeCheckLoopInvariant.proc_step _ _ C Env Env2 idents program proc proc' md hinv
      hregmono htc

/-- Adding one well-formed function, after registering its name, preserves the input loop
    invariant. -/
private theorem TypeCheckLoopInvariant.func_step [hQ : WalkFactoryClosed Q]
    {C : Expression.TyContext} {Env : Expression.TyEnv} {i idents : Identifiers Unit}
    {l : List Expression.Ident} {f : Expression.Ident → Strata.Message} {fn : LFunc CoreLParams}
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hidents : Identifiers.addListWithError i l f = .ok idents) (hfn : LFuncWF fn) :
    TypeCheckLoopInvariant Q (C.addFactoryFunction fn) Env idents :=
  have hktEq : (C.addFactoryFunction fn).knownTypes = C.knownTypes :=
    Lambda.addFactoryFunction_knownTypes C fn
  ⟨hinv.envWF, hQ.addFunction C fn hinv.factory hfn, hinv.ctxClosed,
    AliasBodiesKnown.of_extends C _ Env.context _ rfl
      (KnownTypesExtends.of_knownTypes_eq C _ hktEq) hinv.aliasBodies,
    hinv.mono, AliasRegistryCoherent.step_of_context_eq hidents rfl hktEq hinv.coherent,
    hinv.clear⟩

/-- A function declaration accepted against a set holding every type name in scope satisfies the
    typechecker spec and preserves the input loop invariant. -/
private theorem func_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (func : Function) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.func func md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.func func md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  obtain ⟨idents, renamed, func', ⟨regMsg, hidents⟩, hnotrec, hfresh, htc', hrec⟩ :=
    WF.Program.typeCheck.stepThen_func_inversion program C Env i func md k res h
  obtain rfl := Function.typeCheckIn_renamed htc'
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  refine ⟨idents, C.addFactoryFunction func'.toLFunc, Env, Decl.func func' md, ?_, ?_, ⟨_, hrec⟩⟩
  · have hpushCtx := TEnv.pushEmptySubstScope_context_eq Env
    have hren : Function.renameReservedTypeArgs { C with idents := idents } Env.pushEmptySubstScope
        func (fun _ => func.annotTys) =
          Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys) :=
      Function.renameReservedTypeArgs_congr func _ rfl hpushCtx
    have hname : func'.toLFunc.name.name
        = (Function.renameReservedTypeArgs C Env func
            (fun _ => func.annotTys)).toLFunc.name.name := by
      show func'.name.name = (Function.renameReservedTypeArgs C Env func
        (fun _ => func.annotTys)).name.name
      rw [(Function.typeCheckIn_copies_untouched_fields _ _ _ _ _ _ htc').1,
        (Function.renameReservedTypeArgs_fields C Env func _).1]
    have hfresh' : func'.toLFunc.name.name ∉ C.functions := by
      rw [hname]
      show (Function.renameReservedTypeArgs C Env func
        (fun _ => func.annotTys)).name.name ∉ C.functions
      rw [(Function.renameReservedTypeArgs_fields C Env func _).1]
      exact hfresh
    have hagree := Function.typeCheckIn_funcSigAgree _ _ _ _ _ _ htc'
    have hshape := Function.typeCheckIn_funcShapeAgree _ _ _ _ _ _ htc'
    rw [TEnv.pushEmptySubstScope_context_eq Env, hren] at hagree
    rw [hren] at hshape
    have hentry : ∀ f ∈ [(Function.renameReservedTypeArgs C Env func
        (fun _ => func.annotTys)).toLFunc],
        ∃ e ∈ [func'.toLFunc], e.name.name = f.name.name ∧ FuncEntryOk Env.context f e := by
      intro f hf
      obtain rfl := List.mem_singleton.mp hf
      exact ⟨func'.toLFunc, List.mem_singleton_self _, hname, hagree, hshape⟩
    have hnames : [func'.toLFunc].map (·.name.name)
        = [(Function.renameReservedTypeArgs C Env func
            (fun _ => func.annotTys)).toLFunc].map (·.name.name) := by
      simp only [List.map_cons, List.map_nil, hname]
    have halpha := Function.typeCheckIn_alphaVariant htc'
    rw [hren] at halpha
    refine DeclHasType.func C (C.addFactoryFunction func'.toLFunc) Env.context func
      (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys))
      md hnotrec hfresh
      (FuncAlphaVariant.congr (C := { C with idents := idents })
        (Γ := Env.pushEmptySubstScope.context) rfl (TContext.FindEq.refl _) halpha) ?_
      (FactoryExtendedBy.of_entries
        (factoryExtendedBy_addFactoryFunction C func'.toLFunc hfresh') hnames hentry)
    have hsound := Function.typeCheckIn_sound _ {C with idents := idents}
      Env.pushEmptySubstScope func _ func' htc'
      (scopeTyNames_cover_idents_push idents hcov) hwf_push
      (hQ.sigWF _ hinv.factory) hinv.ctxClosed (MonoScope_of_invariant C Env hinv)
    rw [TEnv.pushEmptySubstScope_context_eq Env, hren] at hsound
    exact FuncHasTypeExact_idents_irrel C idents Env.context _ hsound
  · exact TypeCheckLoopInvariant.func_step hinv hidents
      (LFuncWF_of_typeCheckIn _ _ _ _ _ _ htc' hwf_push.aliasesWF)

/-! ### The program-loop step for a recursive function block -/

/-- Lists with equal identifier lists have equal name lists. -/
private theorem name_strings_eq {α β : Type} (f : α → Expression.Ident) (g : β → Expression.Ident)
    (xs : List α) (ys : List β) (h : xs.map f = ys.map g) :
    xs.map (fun x => (f x).name) = ys.map (fun y => (g y).name) := by
  simpa only [List.map_map, Function.comp_def] using congrArg (List.map (·.name)) h

/-- Folding in the registration of functions named, in order, like a list `ref` of distinct names
    new to `C` extends `C` by exactly those functions. -/
private theorem factoryExtendedBy_foldl_of_names {α : Type} (C : Expression.TyContext)
    (l : List α) (g : α → LFunc CoreLParams) (ref : List Function)
    (hnames : l.map (fun a => (g a).name) = ref.map (·.name))
    (hnodup : (ref.map (·.name.name)).Nodup) (hfresh : ∀ f ∈ ref, f.name.name ∉ C.functions) :
    FactoryExtendedBy (fun f e => e = f) C (l.foldl (fun C a => C.addFactoryFunction (g a)) C)
      (l.map g) := by
  have hstr : l.map (fun a => (g a).name.name) = ref.map (·.name.name) :=
    name_strings_eq _ _ l ref hnames
  have hnodupL : (l.map fun a => (g a).name.name).Nodup := by
    rw [hstr]
    exact hnodup
  refine factoryExtendedBy_foldl C l g hnodupL ?_
  intro a ha hmem
  have hin : (g a).name.name ∈ ref.map (·.name.name) := by
    rw [← hstr]
    exact List.mem_map_of_mem ha
  obtain ⟨f, hf, hfn⟩ := List.mem_map.mp hin
  rw [← hfn] at hmem
  exact hfresh f hf hmem

/-- Registering stubs named like `ref` (distinct names new to `C`) extends `C` by the signature
    stubs of `gs`, also named like `ref`, when each agrees with a stub of its name. -/
private theorem factoryExtendedBy_stubContext
    {agrees : LFunc CoreLParams → LFunc CoreLParams → Prop} (C : Expression.TyContext)
    (stubs : List (LFunc CoreLParams)) (gs ref : List Function)
    (hstubs : stubs.map (·.name) = ref.map (·.name)) (hgs : gs.map (·.name) = ref.map (·.name))
    (hnodup : (ref.map (·.name.name)).Nodup) (hfresh : ∀ f ∈ ref, f.name.name ∉ C.functions)
    (hagree : ∀ f ∈ gs, ∃ e ∈ stubs, e.name = f.name ∧
      agrees (LFunc.mk f.name f.typeArgs (inputs := f.inputs) (output := f.output)) e) :
    FactoryExtendedBy agrees C (RecFuncBlock.stubContext C stubs)
      (gs.map (fun f => LFunc.mk f.name f.typeArgs (inputs := f.inputs) (output := f.output))) := by
  have hext : FactoryExtendedBy (fun f e => e = f) C (RecFuncBlock.stubContext C stubs) stubs := by
    unfold RecFuncBlock.stubContext
    simpa using factoryExtendedBy_foldl_of_names C stubs id ref hstubs hnodup hfresh
  refine FactoryExtendedBy.of_entries hext ?_ ?_
  · rw [List.map_map, name_strings_eq _ _ stubs ref hstubs, ← name_strings_eq _ _ gs ref hgs]
    rfl
  · intro s hs
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
    obtain ⟨e, he, hname, hag⟩ := hagree f hf
    exact ⟨e, he, congrArg (·.name) hname, hag⟩

/-- Registering functions `funcs'` named like `ref` (distinct names new to `C`) extends `C` by
    the functions `gs`, also named like `ref`, when each agrees with a function of `funcs'` of
    its name. -/
private theorem factoryExtendedBy_fullContext
    {agrees : LFunc CoreLParams → LFunc CoreLParams → Prop} (C : Expression.TyContext)
    (funcs' gs ref : List Function)
    (hfuncs' : funcs'.map (·.name) = ref.map (·.name)) (hgs : gs.map (·.name) = ref.map (·.name))
    (hnodup : (ref.map (·.name.name)).Nodup) (hfresh : ∀ f ∈ ref, f.name.name ∉ C.functions)
    (hagree : ∀ f ∈ gs, ∃ e ∈ funcs', e.name = f.name ∧ agrees (f.toLFunc none) (e.toLFunc none)) :
    FactoryExtendedBy agrees C (RecFuncBlock.fullContext C funcs') (gs.map (·.toLFunc none)) := by
  have hext : FactoryExtendedBy (fun f e => e = f) C (RecFuncBlock.fullContext C funcs')
      (funcs'.map (·.toLFunc none)) := by
    unfold RecFuncBlock.fullContext
    exact factoryExtendedBy_foldl_of_names C funcs' (·.toLFunc none) ref hfuncs' hnodup hfresh
  refine FactoryExtendedBy.of_entries hext ?_ ?_
  · rw [List.map_map, List.map_map]
    exact (name_strings_eq _ _ funcs' ref hfuncs').trans (name_strings_eq _ _ gs ref hgs).symm
  · intro s hs
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hs
    obtain ⟨e, he, hname, hag⟩ := hagree f hf
    exact ⟨e.toLFunc none, List.mem_map_of_mem he, congrArg (·.name) hname, hag⟩

/-- Inversion of one accepted declaration step at a recursive function block, with any
    continuation `k`. -/
private theorem Program.typeCheck.stepThen_recFuncBlock_inversion
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (i : Identifiers Unit) (funcs : List Function) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.recFuncBlock funcs md) k = .ok res) :
    ∃ (idents : Identifiers Unit) (funcs' : List Function)
      (C' : Expression.TyContext) (E' : Expression.TyEnv) (S' : Std.HashSet String),
      RecFuncBlock.typeCheckIn S
          { C with idents := idents } Env.pushEmptySubstScope funcs = .ok (funcs', C', E', S')
      ∧ ({ RecFuncBlock.fullContext C funcs' with idents := idents } : Expression.TyContext) = C'
      ∧ (∀ n : String, n ∈ i → n ∈ idents)
      ∧ (funcs.map (·.name.name)).Nodup
      ∧ k (Decl.recFuncBlock funcs' md)
          { RecFuncBlock.fullContext C funcs' with idents := idents }
          E'.popSubstScope S' = .ok res := by
  simp only [Program.typeCheck.stepThen, Decl.routePropBeforeRegistration, Decl.propCheck?,
    Decl.routeDistinctBeforeRegistration] at h
  obtain ⟨routed, hroute, h⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq] at hroute
  subst routed
  obtain ⟨routedDistinct, hrouteDistinct, h⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq] at hrouteDistinct
  subst routedDistinct
  obtain ⟨idents, hidents, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨step, hstep, hrec⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [tryCatch, tryCatchThe, MonadExceptOf.tryCatch, Except.tryCatch] at hstep
  elim_err hstep with accepted haccepted
  obtain rfl : accepted = step := by injection hstep
  obtain ⟨checked, hchecked, hout⟩ := (Except.bind_is_ok _ _ _).mp haccepted
  obtain ⟨funcs', C', E', S'⟩ := checked
  simp only [Except.ok.injEq] at hout
  subst accepted
  have htc := Except.mapError_ok_h' hchecked
  obtain ⟨-, -, -, -, hC', -⟩ :=
    RecFuncBlock.typeCheckIn_decompose _ S' { C with idents := idents } C'
      Env.pushEmptySubstScope E' funcs funcs' htc
  have hfull : ({ RecFuncBlock.fullContext C funcs' with idents := idents } :
      Expression.TyContext) = C' := by
    rw [hC']
    unfold RecFuncBlock.fullContext
    exact (foldl_addFactoryFunction_setIdents C funcs' (·.toLFunc none) idents).symm
  rw [← hfull] at hrec
  have hnd : (funcs.map (·.name)).Nodup := Identifiers.addListWithErrorNoDup hidents
  have hndStr := List.nodup_map_of_injective _ _ coreIdent_name_injective hnd
  rw [List.map_map] at hndStr
  exact ⟨idents, funcs', C', E', S', htc, hfull, Identifiers.addListWithError_mem_mono hidents,
    hndStr, hrec⟩

/-- For any name set, the signature of a function `Function.typeCheckIn` accepts, as a
    bodyless factory entry, is a well-formed factory function. -/
private theorem LFuncWF_signature_of_typeCheckIn
    (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (h_aw : TContext.AliasesWF Env.context) :
    LFuncWF (T := CoreLParams)
      { name := func'.name, typeArgs := func'.typeArgs, inputs := func'.inputs,
        output := func'.output } := by
  have hchecked := LFuncWF_of_typeCheckIn scope C Env func renamed func' h h_aw
  exact
    { arg_nodup := hchecked.arg_nodup
      typeArgs_nodup := hchecked.typeArgs_nodup
      inputs_typevars_in_typeArgs := hchecked.inputs_typevars_in_typeArgs
      output_typevars_in_typeArgs := hchecked.output_typevars_in_typeArgs
      body_freevars := by intro _ hb; exact absurd hb (by simp)
      precond_freevars := by intro _ hp; exact absurd hp (by simp)
      constr_no_eval := by simp
      typeArgs_no_gen_prefix := hchecked.typeArgs_no_gen_prefix }

/-- Facts about an accepted recursive-block check run in a fresh substitution scope over a
    well-formed environment, against a set holding every type name in scope. The returned set
    holds every type name in scope in the context with the stubs, and the function checker, run
    against that set in that context, accepts each member; both block contexts keep the factory
    property `Q`. -/
private theorem RecFuncBlock.typeCheckIn_accepted_facts
    (C : Expression.TyContext) (idents : Identifiers Unit) (Env : Expression.TyEnv)
    (funcs funcs' : List Function) (C' : Expression.TyContext) (E' : Expression.TyEnv)
    {S : Std.HashSet String} (S' : Std.HashSet String)
    [WalkFactoryClosed Q]
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : Q C.functions)
    (htc : RecFuncBlock.typeCheckIn S
      { C with idents := idents } Env.pushEmptySubstScope funcs = .ok (funcs', C', E', S'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    (∀ n ∈ scopeTyNames (RecFuncBlock.stubContext { C with idents := idents }
          (RecFuncBlock.signatureStubs funcs')) Env.pushEmptySubstScope, n ∈ S')
      ∧ (∀ f ∈ funcs, ∃ f' ∈ funcs', ∃ renamed,
          Function.typeCheckIn (Thunk.pure S')
            (RecFuncBlock.stubContext { C with idents := idents }
                (RecFuncBlock.signatureStubs funcs'))
            Env.pushEmptySubstScope f = .ok (renamed, f'))
      ∧ (∀ f' ∈ funcs', ∃ f ∈ funcs, ∃ renamed,
          Function.typeCheckIn (Thunk.pure S')
            (RecFuncBlock.stubContext { C with idents := idents }
                (RecFuncBlock.signatureStubs funcs'))
            Env.pushEmptySubstScope f = .ok (renamed, f'))
      ∧ Q (RecFuncBlock.stubContext { C with idents := idents }
          (RecFuncBlock.signatureStubs funcs')).functions
      ∧ Q (RecFuncBlock.fullContext C funcs').functions
      ∧ RecFuncBlock.stubContext { C with idents := idents } (RecFuncBlock.signatureStubs funcs')
          = { RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs')
              with idents := idents }
      ∧ (RecFuncBlock.stubContext { C with idents := idents }
          (RecFuncBlock.signatureStubs funcs')).knownTypes = C.knownTypes
      ∧ (RecFuncBlock.fullContext C funcs').knownTypes = C.knownTypes := by
  obtain ⟨-, -, hstubCov, -, hrel⟩ :=
    RecFuncBlock.typeCheckIn_members _ S' { C with idents := idents } C'
      Env.pushEmptySubstScope E' funcs funcs' htc (scopeTyNames_cover_idents_push idents hcov)
  have h_env0 : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env
  have hfwd : ∀ f ∈ funcs, ∃ f' ∈ funcs', ∃ renamed,
      Function.typeCheckIn (Thunk.pure S')
        (RecFuncBlock.stubContext { C with idents := idents } (RecFuncBlock.signatureStubs funcs'))
        Env.pushEmptySubstScope f = .ok (renamed, f') :=
    fun _ hf => hrel.exists_of_mem_left hf
  have hbwd : ∀ f' ∈ funcs', ∃ f ∈ funcs, ∃ renamed,
      Function.typeCheckIn (Thunk.pure S')
        (RecFuncBlock.stubContext { C with idents := idents } (RecFuncBlock.signatureStubs funcs'))
        Env.pushEmptySubstScope f = .ok (renamed, f') :=
    fun _ hf' => hrel.exists_of_mem_right hf'
  have h_fac_stub :
      Q (RecFuncBlock.stubContext { C with idents := idents }
          (RecFuncBlock.signatureStubs funcs')).functions := by
    unfold RecFuncBlock.stubContext
    refine WalkFactoryClosed.foldl_addFactoryFunction (RecFuncBlock.signatureStubs funcs') id
      { C with idents := idents } h_fac ?_
    intro stub hstub
    obtain ⟨f', hf', rfl⟩ := (RecFuncBlock.mem_signatureStubs funcs' stub).mp hstub
    obtain ⟨f, -, renamed, htcf⟩ := hbwd f' hf'
    exact LFuncWF_signature_of_typeCheckIn _ _ _ f renamed f' htcf h_env0.aliasesWF
  have h_fac_full : Q (RecFuncBlock.fullContext C funcs').functions := by
    unfold RecFuncBlock.fullContext
    refine WalkFactoryClosed.foldl_addFactoryFunction funcs' (·.toLFunc none) C h_fac ?_
    intro f' hf'
    obtain ⟨f, -, renamed, htcf⟩ := hbwd f' hf'
    exact LFuncWF_of_typeCheckIn _ _ _ f renamed f' htcf h_env0.aliasesWF
  have hCstub_eq :
      RecFuncBlock.stubContext { C with idents := idents } (RecFuncBlock.signatureStubs funcs') =
        { RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs')
          with idents := idents } := by
    unfold RecFuncBlock.stubContext
    exact foldl_addFactoryFunction_setIdents C (RecFuncBlock.signatureStubs funcs') id idents
  have hstubKnown :
      (RecFuncBlock.stubContext { C with idents := idents }
          (RecFuncBlock.signatureStubs funcs')).knownTypes = C.knownTypes := by
    unfold RecFuncBlock.stubContext
    exact foldl_addFactoryFunction_knownTypes { C with idents := idents }
        (RecFuncBlock.signatureStubs funcs') id
  have hktEq : (RecFuncBlock.fullContext C funcs').knownTypes = C.knownTypes := by
    unfold RecFuncBlock.fullContext
    exact foldl_addFactoryFunction_knownTypes C funcs' (·.toLFunc none)
  exact ⟨hstubCov, hfwd, hbwd, h_fac_stub, h_fac_full, hCstub_eq, hstubKnown, hktEq⟩

/-- An accepted recursive-function block, after registering its names and adding its functions,
    preserves the input loop invariant; its scope pushes and pops without change. -/
private theorem TypeCheckLoopInvariant.recFuncBlock_step {C : Expression.TyContext}
    {Env : Expression.TyEnv} {i v : Identifiers Unit} {funcs' : List Function}
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hfull : Q (RecFuncBlock.fullContext C funcs').functions)
    (hktEq : (RecFuncBlock.fullContext C funcs').knownTypes = C.knownTypes)
    (hregmono : ∀ n : String, n ∈ i → n ∈ v) :
    TypeCheckLoopInvariant Q (RecFuncBlock.fullContext C funcs')
      Env.pushEmptySubstScope.popSubstScope v := by
  have h_env0 : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have hpopCtx : (Env.pushEmptySubstScope.popSubstScope).context = Env.context := rfl
  obtain ⟨hcl, hmo⟩ := scopeFacts_of_context_eq hpopCtx hinv.ctxClosed hinv.mono
  have halias : (Env.pushEmptySubstScope.popSubstScope).context.aliases
      = Env.context.aliases := by
    rw [hpopCtx]
  exact ⟨popSubstScope_preserves_TEnvWF (T := CoreLParams)
      Env.pushEmptySubstScope h_env0, hfull, hcl,
    AliasBodiesKnown.of_extends C _ Env.context _ (by rw [hpopCtx])
      (KnownTypesExtends.of_knownTypes_eq C _ hktEq) hinv.aliasBodies,
    hmo,
    AliasRegistryCoherent.of_knownTypes_eq hktEq
      (AliasRegistryCoherent.of_aliases_eq halias
        (AliasRegistryCoherent.of_idents_mem hregmono hinv.coherent)),
    hinv.clear⟩

/-- A recursive-function-block step accepted against a set holding every type name in scope
    satisfies the typechecker spec, preserves the input invariant, and continues the walk. -/
private theorem recFuncBlock_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (funcs : List Function) (md : MetaData Expression)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.recFuncBlock funcs md) k = .ok res) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      DeclHasType program C Env.context (Decl.recFuncBlock funcs md) C2 Env2.context
        ∧ TypeCheckLoopInvariant Q C2 Env2 i'
        ∧ ∃ S2, k d' { C2 with idents := i' } Env2 S2 = .ok res := by
  have h_env := hinv.envWF
  have h_fac := hinv.factory
  have h_closed := hinv.ctxClosed
  have h_mono := hinv.mono
  obtain ⟨v, funcs', Cfinal, Efinal, S', htc, -, hregmono, hnodup, hrec⟩ :=
    Program.typeCheck.stepThen_recFuncBlock_inversion
      program C Env i funcs md k res h
  obtain ⟨hstubCov, hfwd, -, h_fac_stub, h_fac_full, hCstub_eq, -, hktEq⟩ :=
    RecFuncBlock.typeCheckIn_accepted_facts C v Env funcs funcs' Cfinal Efinal S' h_env h_fac
      htc hcov
  obtain rfl : Efinal = Env.pushEmptySubstScope :=
    (RecFuncBlock.typeCheckIn_members _ S' { C with idents := v } Cfinal Env.pushEmptySubstScope
      Efinal funcs funcs' htc (scopeTyNames_cover_idents_push v hcov)).1
  have hnoinline := RecFuncBlock.typeCheckIn_noInline _ _ _ _ _ _ _ _ htc
  have hstubNames : (RecFuncBlock.signatureStubs funcs').map (·.name) = funcs.map (·.name) :=
    RecFuncBlock.typeCheckIn_stubs_names _ _ _ _ _ _ _ _ htc
  have h_env0 : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env
  have h_closed0 : LExpr.checkContextTypesClosed (T := CoreLParams)
      Env.pushEmptySubstScope := by
    rw [LExpr.checkContextTypesClosed_of_context_eq (T := CoreLParams)
      Env.pushEmptySubstScope Env rfl]
    exact h_closed
  have hpopCtx : (Env.pushEmptySubstScope.popSubstScope).context = Env.context := rfl
  have hnames : funcs'.map (·.name) = funcs.map (·.name) :=
    RecFuncBlock.typeCheckIn_names_eq _ _ _ _ _ _ _ _ htc
  have hfresh := RecFuncBlock.typeCheckIn_names_fresh _ _ _ _ _ _ _ _ htc
  have hpushCtx := TEnv.pushEmptySubstScope_context_eq Env
  have hrenBody : ∀ g, Function.renameReservedTypeArgs
      (RecFuncBlock.stubContext { C with idents := v } (RecFuncBlock.signatureStubs funcs'))
          Env.pushEmptySubstScope g
        (fun _ => g.annotTys) =
      Function.renameReservedTypeArgs C Env g (fun _ => g.annotTys) :=
    fun g => Function.renameReservedTypeArgs_congr g _
      (RecFuncBlock.stubContext_rigidTypeVars _ (RecFuncBlock.signatureStubs funcs')) hpushCtx
  have hfwdR : ∀ g ∈ funcs, ∃ f' ∈ funcs', Function.typeCheckIn (Thunk.pure S')
      (RecFuncBlock.stubContext { C with idents := v } (RecFuncBlock.signatureStubs funcs'))
          Env.pushEmptySubstScope g
        = .ok (Function.renameReservedTypeArgs C Env g (fun _ => g.annotTys), f') := by
    intro g hg
    obtain ⟨f', hf', _, htcf⟩ := hfwd g hg
    obtain rfl := Function.typeCheckIn_renamed htcf
    rw [hrenBody] at htcf
    exact ⟨f', hf', htcf⟩
  let renamed := funcs.map fun f =>
    Function.renameReservedTypeArgs C Env f (fun _ => f.annotTys)
  have hrenNames : renamed.map (·.name) = funcs.map (·.name) := by
    rw [List.map_map]
    exact List.map_congr_left fun f _ => (Function.renameReservedTypeArgs_fields C Env f _).1
  refine ⟨v, RecFuncBlock.fullContext C funcs', Env.pushEmptySubstScope.popSubstScope,
    Decl.recFuncBlock funcs' md, ?_, ?_, ⟨_, hrec⟩⟩
  · rw [hpopCtx]
    refine DeclHasType.recFuncBlock (P := program) C
      (RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs'))
      (RecFuncBlock.fullContext C funcs')
      Env.context funcs renamed md
      (renamed.map
        (fun f => LFunc.mk f.name f.typeArgs (inputs := f.inputs) (output := f.output)))
      (renamed.map (·.toLFunc none))
      (RecFuncBlock.typeCheckIn_nonempty _ _ _ _ _ _ _ _ htc) hfresh
      hnoinline ?_ rfl rfl ?_ ?_ ?_ (RecFuncBlock.typeCheckIn_recursive _ _ _ _ _ _ _ _ htc)
    · refine List.Rel₂.self_map _ funcs fun f hf => ?_
      obtain ⟨f', -, htcf⟩ := hfwdR f hf
      have halpha := Function.typeCheckIn_alphaVariant htcf
      exact FuncAlphaVariant.congr (C := RecFuncBlock.stubContext { C with idents := v }
          (RecFuncBlock.signatureStubs funcs'))
        (Γ := Env.pushEmptySubstScope.context)
        (RecFuncBlock.stubContext_rigidTypeVars { C with idents := v }
            (RecFuncBlock.signatureStubs funcs')).symm
        (TContext.FindEq.refl _) halpha
    · refine factoryExtendedBy_stubContext C (RecFuncBlock.signatureStubs funcs') _ funcs
        hstubNames hrenNames hnodup hfresh ?_
      intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨f', hf', htcf⟩ := hfwdR g hg
      have hag := Function.typeCheckIn_funcSigAgree _ _ _ g _ f' htcf
      rw [TEnv.pushEmptySubstScope_context_eq Env] at hag
      obtain ⟨hname, hta, hkeys, hins, hout⟩ := hag
      have hstub : LFunc.mk f'.name f'.typeArgs (inputs := f'.inputs) (output := f'.output) ∈
          (RecFuncBlock.signatureStubs funcs') := by
        exact (RecFuncBlock.mem_signatureStubs _ _).mpr ⟨f', hf', rfl⟩
      exact ⟨_, hstub, hname.symm, ⟨hname, hta, hkeys, hins, hout⟩,
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
    · refine factoryExtendedBy_fullContext C funcs' _ funcs hnames hrenNames hnodup hfresh ?_
      intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨f', hf', htcf⟩ := hfwdR g hg
      have hag := Function.typeCheckIn_funcSigAgree _ _ _ g _ f' htcf
      rw [TEnv.pushEmptySubstScope_context_eq Env] at hag
      exact ⟨f', hf', hag.1.symm, hag, Function.typeCheckIn_funcShapeAgree _ _ _ g _ f' htcf⟩
    · intro f hf
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
      obtain ⟨f', -, htcf⟩ := hfwdR g hg
      have hsound := Function.typeCheckIn_sound _ _ Env.pushEmptySubstScope g _ f' htcf
        hstubCov h_env0 (hQ.sigWF _ h_fac_stub) h_closed0 h_mono
      rw [TEnv.pushEmptySubstScope_context_eq Env, hCstub_eq] at hsound
      exact FuncHasTypeExact_idents_irrel _ v Env.context _ hsound
  · exact TypeCheckLoopInvariant.recFuncBlock_step hinv h_fac_full hktEq hregmono

/-! ### The scope type-name set across one step -/

/-- An axiom or lemma check accepted against a set holding every type name in scope adds no type
    names in scope: every type name in scope in the environment it returns is one in the
    environment it starts from. -/
private theorem Decl.propCheck?_scopeTyNames {d : Decl} {C D : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check) {S : Std.HashSet String} {Env Env' : Expression.TyEnv}
    {d' : Decl} (h : check S Env = .ok (d', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    ∀ n ∈ scopeTyNames D Env', n ∈ scopeTyNames D Env := by
  obtain ⟨e', hax, hlem⟩ := Decl.propCheck?_inv hd h
  obtain ⟨kind, name, typeArgs, e, tyNames, hprop, htn, -⟩ :=
    Decl.propCheck?_ok hd (fun a md hda => (hax a md hda).2)
      (Decl.propCheck?_inv_propChecks hlem)
  obtain ⟨_, _, hfacts⟩ :=
    typeCheckProp_success _ kind name typeArgs C Env Env' e e' tyNames hprop
      (fun _ => hcov) htn
  obtain ⟨EnvR, SI, hresolve, -, rfl⟩ :=
    resolveWithType_decompose _ Env _ _ _ LMonoTy.bool hfacts.resolves
  rw [scopeTyNames_congr rfl (TEnv.updateSubst_context EnvR SI)]
  exact scopeTyNames_of_resolve hresolve

/-- An accepted axiom or lemma step keeps the scope type-name set covering the type names in
    scope: when `S` holds every type name in scope in `C` and `Env`, it holds every one in the
    context and environment the continuation receives. -/
private theorem Program.typeCheck.stepThen_prop_cover (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl) {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C = some check)
    (h : Program.typeCheck.stepThen program PS S C Env d k = .ok res)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    ∃ (d' : Decl) (C' : Expression.TyContext) (Env' : Expression.TyEnv)
      (S' : Std.HashSet String),
      (∀ n ∈ scopeTyNames C' Env', n ∈ S') ∧ k d' C' Env' S' = .ok res := by
  obtain ⟨idents, d', EnvA, -, hcheck, hrec⟩ :=
    Program.typeCheck.stepThen_prop_inversion program C Env C.idents d k res hd h
  have hpop : scopeTyNames { C with idents := idents } EnvA.popSubstScope =
      scopeTyNames C EnvA :=
    scopeTyNames_congr rfl (TEnv.popSubstScope_context_eq EnvA)
  have hcovPush := scopeTyNames_cover_of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hcov
  refine ⟨_, _, _, _, fun n hn => hcovPush n ?_, hrec⟩
  rw [hpop] at hn
  exact Decl.propCheck?_scopeTyNames hd hcheck (scopeTyNames_cover_idents_push C.idents hcov) n hn

/-- Some declaration, context, environment and scope type-name set satisfy `R`, and the set
    holds every type name in scope in that context and environment. -/
abbrev StepScopeCovered
    (R : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop) : Prop :=
  ∃ (d' : Decl) (C' : Expression.TyContext) (Env' : Expression.TyEnv)
    (S' : Std.HashSet String), (∀ n ∈ scopeTyNames C' Env', n ∈ S') ∧ R d' C' Env' S'

/-- An accepted step keeps the scope type-name set covering the type names in scope: when `S`
    holds every type name in scope in `C` and `Env`, the set that every continuation receives
    holds every type name in scope in the context and environment it receives. -/
private theorem Program.typeCheck.stepThen_cover {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (decl : Decl)
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S C Env decl k = .ok res)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    StepScopeCovered (StepAccepts program PS S C Env decl k res) := by
  refine Program.typeCheck.stepThen_det program StepScopeCovered
    (fun _ _ hR ⟨d', C', Env', S', hc, hr⟩ => ⟨d', C', Env', S', hc, hR _ _ _ _ hr⟩)
    ?_ k res h
  intro _ k' r h'
  cases decl with
  | type td md =>
    cases td with
    | con tc =>
      obtain ⟨idents, ctx, -, hctx, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_con_inversion program C Env C.idents tc md k' r h'
      have hfun : ctx.functions = C.functions :=
        Lambda.addKnownTypeWithError_functions_eq { C with idents := idents } ctx _ _ hctx
      have hscope : scopeTyNames { { ctx with idents := C.idents } with idents := idents } Env
          = scopeTyNames C Env :=
        scopeTyNames_congr (congrArg (·.toArray) hfun) rfl
      refine ⟨_, _, _, _, ?_, hrec⟩
      rw [hscope]
      exact hcov
    | syn ts =>
      obtain ⟨idents, v, storedTy, -, -, -, -, -, -, haliases, hvctx, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_syn_inversion program C Env C.idents ts md k' r h'
      have htypes : v.context.types = Env.context.types := by rw [hvctx]
      refine ⟨_, _, _, _, Std.HashSet.mem_insertMany_of_cover hcov fun n hn => ?_, hrec⟩
      rw [scopeTyNames_addAlias _ haliases htypes, List.mem_append, scopeTyNames_setIdents] at hn
      exact hn.symm
    | data block =>
      obtain ⟨idents, block_r, C', -, -, hadd, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_data_inversion program C Env C.idents block md k' r h'
      obtain ⟨_, -, hlist⟩ := LContext.addMutualBlock_functions_toList hadd
      have hscope : scopeTyNames { { C' with idents := C.idents } with idents := idents } Env =
          scopeTyNames C Env ++ Factory.tyNamesFrom C.functions.toArray.size C'.functions :=
        scopeTyNames_append hlist rfl
      refine ⟨_, _, _, _, Std.HashSet.mem_insertMany_of_cover hcov fun n hn => ?_, hrec⟩
      rw [hscope, List.mem_append] at hn
      exact hn
  | ax _ _ | lemma _ _ =>
    exact Program.typeCheck.stepThen_prop_cover program C Env _ k' r rfl h' hcov
  | distinct l es md =>
    obtain ⟨idents, es', EnvR, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_distinct_route program C Env l es md k' r h'
    refine ⟨_, _, _, _, ?_, hrec⟩
    rw [scopeTyNames_setIdents]
    exact hcov
  | proc proc md =>
    obtain ⟨idents, proc', Env2, -, hctx, -, hrec⟩ :=
      Program.typeCheck.stepThen_proc_inversion program C Env C.idents proc md k' r h'
    refine ⟨_, _, _, _, ?_, hrec⟩
    rw [scopeTyNames_setIdents]
    exact scopeTyNames_cover_of_context_eq hctx hcov
  | func func md =>
    obtain ⟨idents, _, func', -, -, -, -, hrec⟩ :=
      WF.Program.typeCheck.stepThen_func_inversion program C Env C.idents func md k' r h'
    refine ⟨_, _, _, _, ?_, hrec⟩
    rw [scopeTyNames_setIdents]
    exact scopeTyNames_addFactoryFunction_cover hcov
  | recFuncBlock funcs md =>
    obtain ⟨idents, funcs', C2, E2, S2, htc, hfull, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_recFuncBlock_inversion program C Env C.idents funcs md k' r h'
    obtain ⟨rfl, -, -, hcovC2, -⟩ :=
      RecFuncBlock.typeCheckIn_members _ S2 { C with idents := idents } C2 _ E2 funcs funcs' htc
        (scopeTyNames_cover_idents_push idents hcov)
    have hscope : scopeTyNames { RecFuncBlock.fullContext C funcs' with idents := idents }
        Env.pushEmptySubstScope.popSubstScope = scopeTyNames C2 Env.pushEmptySubstScope := by
      rw [hfull]
      exact scopeTyNames_congr rfl (TEnv.popSubstScope_context_eq _)
    refine ⟨_, _, _, _, ?_, hrec⟩
    rw [hscope]
    exact hcovC2

/-- An accepted step keeps the scope type-name set covering the type names in scope: when `S`
    holds every type name in scope in `C` and `Env`, and every continuation of the step receives
    the set `S2` with the context `C2` (with any identifiers) and the environment `Env2`, then
    `S2` holds every type name in scope in `C2` and `Env2`. -/
private theorem Program.typeCheck.stepThen_next_cover {α : Type} (program : Program)
    {PS : Thunk (Std.HashSet String)} {S S2 : Std.HashSet String}
    {C C2 : Expression.TyContext} {Env Env2 : Expression.TyEnv} {i i' : Identifiers Unit}
    {decl d' : Decl}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env decl k = .ok res)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (hdet : StepReceives program PS S { C with idents := i } Env decl d' { C2 with idents := i' }
      Env2 S2) :
    ∀ n ∈ scopeTyNames C2 Env2, n ∈ S2 := by
  have hcovI : ∀ n ∈ scopeTyNames { C with idents := i } Env, n ∈ S := by
    rw [scopeTyNames_setIdents]
    exact hcov
  obtain ⟨d3, C3, Env3, S3, hc, -, hdet3⟩ :=
    Program.typeCheck.stepThen_cover program _ Env decl k res h hcovI
  let tuple : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message (Decl × Expression.TyContext × Expression.TyEnv ×
        Std.HashSet String) :=
    fun d C E T => .ok (d, C, E, T)
  have heq := (hdet3 tuple).symm.trans (hdet tuple)
  simp only [tuple, Except.ok.injEq, Prod.mk.injEq] at heq
  obtain ⟨-, rfl, rfl, rfl⟩ := heq
  rw [scopeTyNames_setIdents] at hc
  exact hc

/-! ### Input soundness of the declaration walk -/

/-- Some results of a step at `d`, with some scope type-name set, satisfy `R`. For them the
    step meets the typechecker spec over `C` and the context of `Env`, the result environment
    agrees with the spec's type context on lookups, and the input invariant holds. -/
abbrev DeclStepHasType (Q : Lambda.Factory CoreLParams → Prop) (program : Program)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl)
    (R : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop) : Prop :=
  ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv)
    (Ξ : TContext Unit) (d' : Decl),
    DeclHasType program C Env.context d C2 Ξ
      ∧ TContext.FindEq (T := CoreLParams) Env2.context Ξ
      ∧ TypeCheckLoopInvariant Q C2 Env2 i'
      ∧ ∃ S2, R d' { C2 with idents := i' } Env2 S2

/-- An accepted step at any declaration, whose scope type-name set holds every type name in
    scope and whose procedure-signature set holds every type name of the procedure signatures,
    meets the typechecker spec and keeps the input invariant. Its results are accepted by the
    continuation and received by every continuation of the step. -/
private theorem decl_declHasType
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl)
    {α : Type}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α)
    (i : Identifiers Unit)
    [WalkFactoryClosed Q]
    (hsigs : ProcSigsDeclared program)
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get)
    (hinv : TypeCheckLoopInvariant Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env d k = .ok res) :
    DeclStepHasType Q program C Env d
      (StepAccepts program PS S { C with idents := i } Env d k res) := by
  refine Program.typeCheck.stepThen_det program (DeclStepHasType Q program C Env d)
    (fun _ _ hR ⟨i', C2, Env2, Ξ, d', hstep, hfe, hinv2, S2, hr⟩ =>
      ⟨i', C2, Env2, Ξ, d', hstep, hfe, hinv2, S2, hR _ _ _ _ hr⟩)
    ?_ k res h
  intro _ k' r h'
  cases d with
  | type td md =>
    cases td with
    | con tc =>
      obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
        type_con_declHasType program C Env tc md k' r i hinv h'
      exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
    | syn ts =>
      obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
        type_syn_declHasType program C Env ts md k' r i hinv h'
      exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
    | data block =>
      obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
        type_data_declHasType program C Env block md k' r i hinv h'
      exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
  | ax _ _ | lemma _ _ =>
    obtain ⟨i', C2, Env2, d', hstep, hfe, hinv2, hrec⟩ :=
      prop_declHasType program C Env _ k' r i rfl hinv hcov h'
    exact ⟨i', C2, Env2, _, d', hstep, hfe, hinv2, hrec⟩
  | distinct l es md =>
    obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
      distinct_declHasType program C Env l es md k' r i hinv h'
    exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
  | proc proc md =>
    obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
      proc_declHasType program C Env proc md k' r i hsigs hP hinv hcov h'
    exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
  | func func md =>
    obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
      func_declHasType program C Env func md k' r i hinv hcov h'
    exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩
  | recFuncBlock funcs md =>
    obtain ⟨i', C2, Env2, d', hstep, hinv2, hrec⟩ :=
      recFuncBlock_declHasType program C Env funcs md k' r i hinv hcov h'
    exact ⟨i', C2, Env2, _, d', hstep, TContext.FindEq.refl _, hinv2, hrec⟩

/-- A successful walk from the input invariant types the remaining declarations, when every
    procedure signature's free type variables are among its type parameters, `PS` holds every
    type name of the procedure signatures, and `S` holds every type name in scope. -/
private theorem goWith_sound_generalized (program : Program) (PS : Thunk (Std.HashSet String))
    (hsigs : ProcSigsDeclared program) (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get) :
    ∀ (decls : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env : Expression.TyEnv) (i : Identifiers Unit) (acc out : Decls) (Env' : Expression.TyEnv),
      Program.typeCheck.goWith program PS S { C with idents := i } Env decls acc
        = .ok (out, Env') →
      (∀ n ∈ scopeTyNames C Env, n ∈ S) →
      TypeCheckLoopInvariant FactorySigWF C Env i →
      ∃ C' Γ', DeclsHasType program C Env.context decls C' Γ' := by
  intro decls
  induction decls with
  | nil =>
    intro _ C Env i acc out Env' _ _ _
    exact ⟨C, Env.context, DeclsHasType.nil _ _⟩
  | cons d ds IH =>
    intro S C Env i acc out Env' h hcov hinv
    rw [Program.typeCheck.goWith] at h
    obtain ⟨i', C2, Env2, Ξ, d', hstep, hfe, hinv2, _, hrec, hdet⟩ :=
      decl_declHasType program C Env d _ _ i hsigs hP hinv hcov h
    obtain ⟨C'', Γ'', hrest⟩ := IH _ C2 Env2 i' (d' :: acc) out Env' hrec
      (Program.typeCheck.stepThen_next_cover program _ _ h hcov hdet) hinv2
    obtain ⟨Γ''', hrest', -⟩ :=
      DeclsHasType_transport hfe.symm hrest
    exact ⟨C'', Γ''', DeclsHasType.cons _ _ _ _ _ _ _ _ hstep hrest'⟩

/-- Input soundness of the declaration walk from a substitution that binds nothing, against a
    set `S` holding every type name in scope: the accepted declarations satisfy the typechecker
    spec. The ambient context and environment must be well formed (function signatures, stored
    types, scope, aliases), and the free type variables of every procedure signature must be
    among its type parameters. -/
private theorem Program.typeCheck.goWith_sound
    (program : Program) (S : Std.HashSet String) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (decls : List Decl) (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.goWith program (procSigTyNameThunk program) S C Env decls []
      = .ok (out, Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_coh : AliasRegistryCoherent C Env C.idents)
    (h_substClear : AmbientClear Env)
    (h_sigs : ProcSigsDeclared program) :
    ∃ C' Γ', DeclsHasType program C Env.context decls C' Γ' :=
  goWith_sound_generalized program (procSigTyNameThunk program) h_sigs
    (procSigTyNameThunk_cover program) decls S C Env C.idents [] out Env' h hcov
    ⟨h_env, h_fac, h_closed, h_aliasBodies, h_mono, h_coh, h_substClear⟩

/-- Input soundness of the declaration walk from a substitution that binds nothing: the accepted
    declarations satisfy the typechecker spec. The ambient context and environment must be well
    formed: the function signatures are well formed, stored types are closed, the scope holds
    only monotypes, every alias body uses registered types, and no alias is a registered type
    or missing from the identifier registry. The free type variables of every procedure
    signature must be among its type parameters. -/
theorem Program.typeCheck.go_sound
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (decls : List Decl) (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.go program C Env decls [] = .ok (out, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_coh : AliasRegistryCoherent C Env C.idents)
    (h_substClear : AmbientClear Env)
    (h_sigs : ProcSigsDeclared program) :
    ∃ C' Γ', DeclsHasType program C Env.context decls C' Γ' :=
  Program.typeCheck.goWith_sound program _ C Env decls out Env' h (scopeTyNameThunk_cover C Env)
    h_env h_fac h_closed h_aliasBodies h_mono h_coh h_substClear h_sigs

/-! ### Per-declaration step lemmas (output soundness) -/

/-- Adding stubs whose input and output types are registered to a table with registered
    signatures and datatypes keeps every signature registered. -/
private theorem stubContext_sigsKnown (C : Expression.TyContext)
    (stubs : List (LFunc CoreLParams))
    (hknown : ∀ stub ∈ stubs, ∀ ty ∈ stub.output :: stub.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true)
    (hs : FactorySigsKnown C.knownTypes C.functions) (hd : C.DatatypesKnown) :
    FactorySigsKnown (RecFuncBlock.stubContext C stubs).knownTypes
      (RecFuncBlock.stubContext C stubs).functions := by
  unfold RecFuncBlock.stubContext
  exact (tablesKnown_foldl_addFactoryFunction stubs id C hs hd hknown).1

/-- An expression resolved at `bool` in a pushed substitution scope with `σ`'s constants
    registered, then substituted and deskolemized, agrees with the table and the alias-resolved
    starting scope, when deskolemizing by `σ` leaves every function type of the table unchanged. -/
private theorem typeCheckProp_annotAgree (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (i : Identifiers Unit) {σ : RigidNames}
    (hamb : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty → mapLTyTys (deskolemizeTy σ) ty = ty)
    (hfresh : RigidNamesFresh C.knownTypes σ) (e : Expression.Expr) (et : LExprT CoreLParams.mono)
    (hresolveWith : resolveWithType (addSkolemTypes { C with idents := i } σ)
      Env.pushEmptySubstScope e LMonoTy.bool = .ok (et, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    ScopesAnnotAgree C Env.context.dealias.types
      (finishDeskolemized σ Env'.stateSubstInfo.subst et) := by
  have h_monoPush : MonoScope Env.pushEmptySubstScope.context := by
    rw [TEnv.pushEmptySubstScope_context_eq Env]
    exact h_mono
  have hsc : DeskolemizesScope σ
      { TContext.subst Env.pushEmptySubstScope.context.dealias Env'.stateSubstInfo.subst with
        aliases := [] }
      { substDeskolemizedAmbient σ Env'.stateSubstInfo.subst Env.context with aliases := [] } := by
    rw [TEnv.pushEmptySubstScope_context_eq Env]
    exact substDeskolemizedAmbient_deskolemizes σ _ Env.context
  have hfind : ∀ x, Env.context.dealias.types.find? x
      = ({ substDeskolemizedAmbient σ Env'.stateSubstInfo.subst Env.context with
          aliases := [] } : TContext Unit).types.find? x := by
    intro x
    rw [TContext.dealias_find? (T := CoreLParams)]
    exact substDeskolemizedAmbient_find?_of_known σ _ C Env h_env.aliasesWF h_closed h_mono
      h_known hfresh x
  exact ScopesAnnotAgree.of_functions_eq (C := { C with idents := i }) rfl
    (resolveWithType_deskolemized_annotAgree { C with idents := i } Env.pushEmptySubstScope Env'
      σ _ LMonoTy.bool et Env'.stateSubstInfo.subst hresolveWith
      (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)
      (pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env) h_fac h_monoPush
      hamb h_sigsFixed hsc ⟨hfind, rfl⟩)

/-- An axiom or lemma check accepted against a set holding every type name in scope, with its
    elaborated proposition well typed in `ts`, gives a well-typed output declaration `d'` with
    valid names: an axiom with its proposition replaced by the checked one, or a lemma with its
    type parameters renamed and its proposition replaced by the checked one. -/
private theorem DeclWellTyped_checkedProp (P : Program) (C : Expression.TyContext)
    (ts : TypeScopes) {d d' : Decl} {C' : Expression.TyContext}
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? C' = some check) {scope : Thunk (Std.HashSet String)}
    {Env Env' : Expression.TyEnv} {e' : Expression.Expr}
    (hcheckAx : ∀ a md, d = .ax a md → d' = .ax { a with e := e' } md ∧
      Axiom.typeCheckIn C' Env a = .ok (e', Env'))
    (hcheckLem : ∀ l md, d = .lemma l md → ∃ l', d' = .lemma l' md ∧ l'.e = e' ∧
      Lemma.typeCheckIn scope C' Env l = .ok (l', Env'))
    (hcov : ∀ n ∈ scopeTyNames C' Env, n ∈ scope.get)
    (ht : ExprWellTyped C ts e' .bool) :
    DeclWellTyped P C ts d' C ∧ DeclNamesWF P d' := by
  cases d with
  | ax a md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    obtain ⟨rfl, hax⟩ := hcheckAx a md rfl
    obtain ⟨_, _, hfacts⟩ :=
      typeCheckProp_success _ "axiom" a.name [] C' Env Env' a.e e' _ hax
        (fun hne => absurd rfl hne) fun hne => absurd rfl hne
    exact ⟨DeclWellTyped.ax C ts _ md ht (List.eq_nil_of_subset_nil hfacts.annotTyVars_in),
      trivial⟩
  | lemma l md =>
    simp only [Decl.propCheck?, Option.some.injEq] at hd
    subst hd
    obtain ⟨l', rfl, rfl, hl⟩ := hcheckLem l md rfl
    obtain ⟨hnodup, ⟨_, rfl⟩, hprop⟩ := Lemma.typeCheckIn_ok hl
    obtain ⟨_, _, hfacts⟩ :=
      typeCheckProp_success _ "lemma" l.name _ C' Env Env' _ _ _ hprop
        (fun _ => hcov) fun _ _ hn =>
          Lemma.exprTyNames_renameReservedTypeArgs C' Env l _ ▸ hn
    exact ⟨DeclWellTyped.lemma C ts _ md ht
      (Lemma.renameReservedTypeArgs_tyArgRenaming C' Env l _ hnodup).2 hfacts.annotTyVars_in,
      trivial⟩
  | _ => simp [Decl.propCheck?] at hd

/-- What one accepted non-procedure walk step from the output invariant establishes, for the
    output declaration `d'`, context `C2`, environment `Env2` and identifiers `i'` it produces:
    with registered signatures, datatypes and ambient types, `d'` is well typed over the
    alias-resolved starting scopes and has valid names, and the alias-resolved lookups after the
    step agree with those before it; the invariant holds again; and the step's results, with
    some scope type-name set, satisfy `R`. -/
structure OutputNonProcStepFacts (Q : Lambda.Factory CoreLParams → Prop) (program : Program)
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (R : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop)
    (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl) :
    Prop where
  wellTyped : FactorySigsKnown C.knownTypes C.functions → C.DatatypesKnown →
    AmbientTypesKnown C.knownTypes Env → ∀ P : Program,
      DeclWellTyped P C Env.context.dealias.types d' C2
      ∧ DeclNamesWF P d'
      ∧ TContext.FindEq (T := CoreLParams) Env2.context.dealias Env.context.dealias
  invariant : TypeCheckLoopInvariantOutput Q C2 Env2 i'
  aliasFresh : AliasStepFresh program C Env Env2
  knownTypesExtends : KnownTypesExtends C.knownTypes C2.knownTypes
  ambientKnown : AmbientTypesKnown C.knownTypes Env → AmbientTypesKnown C2.knownTypes Env2
  aliasesSubset : Env.context.aliases ⊆ Env2.context.aliases
  tablesKnown : FactorySigsKnown C.knownTypes C.functions → C.DatatypesKnown →
    FactorySigsKnown C2.knownTypes C2.functions ∧ C2.DatatypesKnown
  kindNeProc : d'.kind ≠ DeclKind.proc
  results : ∃ S2, R d' { C2 with idents := i' } Env2 S2

/-- One accepted non-procedure walk step from the output invariant: some output declaration,
    context, environment and identifiers satisfy `OutputNonProcStepFacts`. -/
abbrev OutputNonProcStep (Q : Lambda.Factory CoreLParams → Prop) (program : Program)
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (R : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop) : Prop :=
  ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
    OutputNonProcStepFacts Q program C Env R i' C2 Env2 d'

/-- An accepted opaque-type step types its output declaration and preserves the output
    invariant. -/
private theorem type_con_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (tc : TypeConstructor) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.con tc) md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, ctx, ⟨regMsg, hidents⟩, hctx, hdefault, hrec⟩ :=
    Program.typeCheck.stepThen_type_con_inversion program C Env i tc md _ _ h
  have hext : KnownTypesExtends C.knownTypes
      ({ ctx with idents := C.idents } : Expression.TyContext).knownTypes :=
    KnownTypesExtends.of_addKnownTypeWithError { C with idents := idents } ctx
      { name := tc.name, metadata := tc.numargs } _ hctx
  have hfun : ({ ctx with idents := C.idents } : Expression.TyContext).functions
      = C.functions :=
    Lambda.addKnownTypeWithError_functions_eq { C with idents := idents } ctx _ _ hctx
  have hsigs2 : FactorySigsKnown C.knownTypes C.functions →
      FactorySigsKnown ({ ctx with idents := C.idents } : Expression.TyContext).knownTypes
        ({ ctx with idents := C.idents } : Expression.TyContext).functions := by
    intro hs
    rw [hfun]
    exact hs.mono hext
  refine ⟨idents, { ctx with idents := C.idents }, Env, Decl.type (.con tc) md,
    fun _ _ _ P => ⟨DeclWellTyped.type_con C _ Env.context.dealias.types tc md hdefault,
      trivial, TContext.FindEq.refl _⟩,
    ?_, AliasStepFresh.of_aliases_eq rfl,
    hext, fun hk => AmbientTypesKnown.of_findEq (TContext.FindEq.refl _) hext hk,
    List.Subset.refl _, fun hs hd => ⟨hsigs2 hs, ?_⟩, by simp [Decl.kind], ⟨_, hrec⟩⟩
  · exact ⟨TypeCheckLoopInvariant.type_con_step C ctx Env i idents tc md
      hinv.toTypeCheckLoopInvariant ⟨regMsg, hidents⟩ hctx,
      KnownTypesReady.mono _ _ _ _ hext hinv.ready.substRange hinv.ready⟩
  · exact LContext.DatatypesKnown.of_extends
      (Lambda.addKnownTypeWithError_datatypes_eq { C with idents := idents } ctx _ _ hctx) hext hd

/-- An accepted type-synonym step types its output declaration and preserves the output
    invariant. -/
private theorem type_syn_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (ts : TypeSynonym) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hdecl : ∀ n ∈ (Decl.type (.syn ts) md).names, DeclaredProgramName program n.name)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.syn ts) md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, v, storedTy, Env_ra, ⟨regMsg, hidents⟩, hadd, hknown, hnamefresh,
    -, haliases, hvctx, htyping, hrec⟩ :=
    Program.typeCheck.stepThen_type_syn_inversion program C Env i ts md _ _ h
  have htypesEq : v.context.types = Env.context.types := by rw [hvctx]
  have hres0 : TContext.AliasesResolved Env.context :=
    AliasesResolved_of_invariant hinv.toTypeCheckLoopInvariant
  have hstoredMem : ({ typeArgs := ts.typeArgs, name := ts.name, type := storedTy } : TypeAlias)
      ∈ v.context.aliases := by
    rw [haliases]
    exact List.mem_cons_self
  have hfresh0 : AliasNamesFresh C Env.context := hinv.coherent.freshForKnownTypes
  have hfresh2 : AliasNamesFresh C v.context := by
    intro al hal
    rw [haliases, List.mem_cons] at hal
    rcases hal with rfl | htl
    · intro hmem
      exact hknown ((KnownTypes.containsName_eq_true_iff_mem _ _).mpr hmem)
    · exact hfresh0 al htl
  have hext : TypeAlias.FreshExtension Env.context.aliases v.context.aliases := by
    rw [haliases]
    exact TypeAlias.FreshExtension.cons hnamefresh
  have hnewFresh : ∀ al ∈ v.context.aliases, al ∉ Env.context.aliases →
      KnownTypes.containsName C.knownTypes al.name = false :=
    fun al hal _ => hfresh2.containsName_eq_false al hal
  have hwfV := addTypeAlias_preserves_TEnvWF _ { C with idents := idents } Env v hinv.envWF hadd
  have hw := htyping hres0
  have hwfStored := hwfV.aliasesWF _ hstoredMem
  refine ⟨idents, C, v, Decl.type (.syn { ts with type := storedTy }) md,
    fun _ _ hk P => ⟨DeclWellTyped.type_syn C Env.context.dealias.types _ md hwfStored
        hw.nameUnregistered hw.bodyTyped.htype,
      trivial,
      (TContext.dealias_FindEq_of_FreshExtension (T := CoreLParams) htypesEq hext hnewFresh
        hk).symm⟩,
    ?_, ?_, KnownTypesExtends.refl _,
    fun hk => AmbientTypesKnown.of_FreshExtension htypesEq hext hnewFresh hk,
    TEnv.addTypeAlias_aliases_subset _ ({ C with idents := idents }) Env v hadd,
    fun hs hd => ⟨hs, hd⟩, by simp [Decl.kind], ⟨_, hrec⟩⟩
  · refine ⟨TypeCheckLoopInvariant.type_syn_step C Env v i idents ts md storedTy
      hinv.toTypeCheckLoopInvariant ⟨regMsg, hidents⟩ hadd hvctx, ?_⟩
    refine KnownTypesReady.mono _ _ _ _ (KnownTypesExtends.refl _) ?_ hinv.ready
    rw [TEnv.addTypeAlias_stateSubstInfo _ { C with idents := idents } Env v hadd]
    exact hinv.ready.substRange
  · have hknownMem : ts.name ∉ C.knownTypes := fun hmemk =>
      hknown ((KnownTypes.containsName_eq_true_iff_mem _ _).mpr hmemk)
    refine ⟨hext, ?_, ?_⟩
    · intro al hal hnot
      rw [haliases, List.mem_cons] at hal
      rcases hal with heq | htl
      · subst heq
        exact hknownMem
      · exact absurd htl hnot
    · intro al hal hnot
      rw [haliases, List.mem_cons] at hal
      rcases hal with heq | htl
      · subst heq
        exact hdecl ((ts.name : String) : Expression.Ident)
          (by simp [Decl.names, TypeDecl.names])
      · exact absurd htl hnot

/-- An accepted mutual-datatype step types its output declaration and preserves the output
    invariant. -/
private theorem type_data_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (block : List (LDatatype Unit)) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.type (.data block) md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, block_r, C', ⟨regMsg, hidents⟩, hres, hadd, hadd', hrec⟩ :=
    Program.typeCheck.stepThen_type_data_inversion program C Env i block md _ _ h
  have hext : KnownTypesExtends C.knownTypes
      ({ C' with idents := C.idents } : Expression.TyContext).knownTypes :=
    KnownTypesExtends.of_addMutualBlock { C with idents := idents } C' block_r hadd
  have htabs : FactorySigsKnown C.knownTypes C.functions → C.DatatypesKnown →
      FactorySigsKnown ({ C' with idents := C.idents } : Expression.TyContext).knownTypes
          ({ C' with idents := C.idents } : Expression.TyContext).functions ∧
        ({ C' with idents := C.idents } : Expression.TyContext).DatatypesKnown :=
    fun hs hd => ⟨FactorySigsKnown.addMutualBlock hs
        hinv.ready.bool hd hadd',
      datatypesKnown_addMutualBlock hadd' hd⟩
  refine ⟨idents, { C' with idents := C.idents }, Env,
    Decl.type (TypeDecl.data block_r) md,
    fun _ _ _ _ => ⟨DeclWellTyped.type_data C _ Env.context.dealias.types block_r md hadd',
      trivial, TContext.FindEq.refl _⟩,
    ?_, AliasStepFresh.of_aliases_eq rfl,
    hext, fun hk => AmbientTypesKnown.of_findEq (TContext.FindEq.refl _) hext hk,
    List.Subset.refl _, htabs, by simp [Decl.kind], ⟨_, hrec⟩⟩
  exact ⟨TypeCheckLoopInvariant.type_data_step C C' Env i idents block block_r md
      hinv.toTypeCheckLoopInvariant ⟨regMsg, hidents⟩ hres hadd,
    KnownTypesReady.mono _ _ _ _ hext hinv.ready.substRange hinv.ready⟩

/-- An axiom or lemma step accepted against a set holding every type name in scope types its
    output declaration and preserves the output invariant. -/
private theorem prop_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    {check : Std.HashSet String → Expression.TyEnv →
      Except Std.Format (Decl × Expression.TyEnv)}
    (hd : d.propCheck? { C with idents := i } = some check)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env d k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, d', EnvA, ⟨regMsg, hidents⟩, hcheck, hrec⟩ :=
    Program.typeCheck.stepThen_prop_inversion program C Env i d _ _ hd h
  obtain ⟨e', hcheckAx, hcheckLem⟩ := Decl.propCheck?_inv hd hcheck
  obtain ⟨kind, name, typeArgs, e, tyNames, hprop, htn, -, -, -⟩ :=
    Decl.propCheck?_ok hd (fun a md ha => (hcheckAx a md ha).2)
      (Decl.propCheck?_inv_propChecks hcheckLem)
  have hfresh0 : AliasNamesFresh C Env.context := hinv.coherent.freshForKnownTypes
  obtain ⟨σ, et, hfacts⟩ :=
    typeCheckProp_success _ kind name typeArgs _ _ _ e e' tyNames hprop
      (fun _ => scopeTyNames_cover_idents_push i hcov) htn
  have hpfx := hfacts.prefixed
  have hfresh := hfacts.unregistered
  have hscopeNames := hfacts.not_scope
  have hlits := hfacts.constTysFixed
  have hresolveWith := hfacts.resolves
  have hout := hfacts.out_eq
  subst hout
  have hamb : NoSkolemAmbient C Env.context σ := NoSkolemAmbient.of_prop hpfx hscopeNames
  have hagree : FactorySigsKnown C.knownTypes C.functions → AmbientTypesKnown C.knownTypes Env →
      ScopesAnnotAgree C Env.context.dealias.types _ := fun hs hk =>
    typeCheckProp_annotAgree C Env EnvA i hamb.functions hfresh _ et hresolveWith hinv.envWF
      (hQ.sigWF _ hinv.factory) hinv.ctxClosed hinv.mono hk
      (hs.sigsFixed hfresh0.containsName_eq_false)
  obtain ⟨EnvR, S, rfl, hresolve, hunify, hfeOut, h_wf_out, h_closed_out⟩ :=
    prop_resolve_facts (addSkolemTypes C σ) Env EnvA i (skolemizeBody none σ e) et hinv.envWF
      (hQ.sigWF _ hinv.factory) hinv.ctxClosed hresolveWith
  have h_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have h_aliases : TContext.AliasesResolved Env.pushEmptySubstScope.context := by
    simpa only [TEnv.pushEmptySubstScope_context_eq]
      using AliasesResolved_of_invariant hinv.toTypeCheckLoopInvariant
  have hA := HasTypeA_replaceUserProvidedType_deskolemizeTy hpfx [] _ _
    (ConstTysFixed_resolveWithType _ Env.pushEmptySubstScope (EnvR.updateSubst S) _ et
      LMonoTy.bool hresolveWith _ (ConstTysFixed_skolemizeBody none hlits))
    (resolveWithType_HasTypeA_bool _ Env.pushEmptySubstScope (EnvR.updateSubst S) _ et
      hresolveWith h_push (hQ.sigWF _ hinv.factory) h_aliases)
  rw [List.map_nil, deskolemizeTy_bool hpfx] at hA
  have hready := hinv.ready
  have hext : KnownTypesExtends C.knownTypes (addSkolemTypes C σ).knownTypes :=
    KnownTypesExtends_addSkolemTypes C hfresh
  have hBsk := resolveWithType_binderAnnotations_known { addSkolemTypes C σ with idents := i }
    Env.pushEmptySubstScope (EnvR.updateSubst S) _ et LMonoTy.bool hresolveWith h_push
    (hQ.sigWF _ hinv.factory) (hext "arrow" 2 hready.arrow) (hext "bool" 0 hready.bool)
    (fun c hp _ => Lambda.knownInstance_mono c.ty _ _ hext (hready.literals c hp))
    (Lambda.knownInstance_mono _ _ _ hext (hready.literals (.boolConst true) rfl))
    (Lambda.Subst.RangeKnown_mono _ _ _ hext
      (TEnv.RangeKnown_pushEmptySubstScope Env _ hready.substRange))
  have hB : BinderAnnotsKnown C
      (finishDeskolemized σ (EnvR.updateSubst S).stateSubstInfo.subst et) :=
    binderAnnotations_known_deskolemize
      (knownTypes_contains_of_getElem?_addSkolemTypes (Crig := C) (fun _ => rfl)) _ hBsk
  have hclear := AmbientClear.prop_step hresolve hunify
    hinv.clear
  have hrangeOut : Lambda.Subst.RangeKnown
      (EnvR.updateSubst S).popSubstScope.stateSubstInfo.subst C.knownTypes := by
    intro mty hmty
    rw [SubstClear.values_eq_nil hclear] at hmty
    exact absurd hmty (List.not_mem_nil)
  refine ⟨idents, C, (EnvR.updateSubst S).popSubstScope, _,
    fun hs _ hk P =>
      have hset := DeclWellTyped_checkedProp P C Env.context.dealias.types hd hcheckAx hcheckLem
        (scopeTyNames_cover_idents_push i hcov) ⟨hA, hB, hagree hs hk⟩
      ⟨hset.1, hset.2, hfeOut.dealias⟩,
    ?_, AliasStepFresh.of_aliases_eq hfeOut.2, KnownTypesExtends.refl _,
    fun hk => AmbientTypesKnown.of_findEq hfeOut (KnownTypesExtends.refl _) hk,
    hfeOut.2 ▸ List.Subset.refl _, fun hs hd => ⟨hs, hd⟩, ?_, ⟨_, hrec⟩⟩
  · exact ⟨TypeCheckLoopInvariant.prop_step hinv.toTypeCheckLoopInvariant hidents hresolve
      hunify hfeOut h_wf_out h_closed_out,
      KnownTypesReady.mono _ _ _ _ (KnownTypesExtends.refl _) hrangeOut hready⟩
  · exact Decl.propCheck?_kind_ne_proc hd hcheck

/-- The shared-type constraints of a distinct group relate only registered types when every
    resolved member's type is registered. -/
private theorem Distinct.sharedTypeConstraints_Known (ks : Lambda.KnownTypes)
    (ets : List (LExprT CoreLParams.mono))
    (h : ∀ et ∈ ets, LMonoTy.knownInstance et.toLMonoTy ks = true) :
    Constraints.Known (Distinct.sharedTypeConstraints ets) ks := by
  cases ets with
  | nil =>
    intro c hc
    simp only [Distinct.sharedTypeConstraints, List.not_mem_nil] at hc
  | cons et rest =>
    intro c hc
    simp only [Distinct.sharedTypeConstraints, List.mem_map] at hc
    obtain ⟨et', het', rfl⟩ := hc
    exact ⟨h et' (List.mem_cons_of_mem _ het'), h et List.mem_cons_self⟩

/-- An accepted distinctness step types its output declaration and preserves the output
    invariant. -/
private theorem distinct_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (l : Expression.Ident) (es : List Expression.Expr) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.distinct l es md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, ets, EnvR, S, sharedTy, ⟨regMsg, hidents⟩, -, hsource,
    hunify, hshared, hstored, hlen, hper, hwfOut, hrec⟩ :=
    Program.typeCheck.stepThen_distinct_inversion program C Env i l es md _ _ hinv.envWF
      (hQ.sigWF _ hinv.factory) h
  let Env0 := Env.pushEmptyContext.pushEmptySubstScope
  have hwf0 : LExpr.TEnvWF (T := CoreLParams) Env0 :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env.pushEmptyContext
      (pushEmptyContext_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF)
  have hready := hinv.ready
  have hrange0 : Subst.RangeKnown Env0.stateSubstInfo.subst C.knownTypes :=
    TEnv.RangeKnown_pushEmptySubstScope _ _
      (TEnv.RangeKnown_pushEmptyContext _ _ hready.substRange)
  obtain ⟨hrangeR, htysK⟩ := SourceExpr.resolves_TEnvWF_RangeKnown_tys_known
    { C with idents := i } Env0 EnvR es ets hsource hwf0 (hQ.sigWF _ hinv.factory) hready.arrow
    hready.bool (fun c hp _ => hready.literals c hp) hrange0
  have hrangeS : Subst.RangeKnown S.subst C.knownTypes :=
    Constraints.unify_RangeKnown _ _ _ _ hunify hrangeR
      (Distinct.sharedTypeConstraints_Known C.knownTypes ets htysK)
  have hfresh0 : AliasNamesFresh C Env.context := hinv.coherent.freshForKnownTypes
  have hEnv0 : TContext.FindEq (T := CoreLParams) Env0.context Env.context := by
    rw [TEnv.pushEmptySubstScope_context_eq]
    exact pushEmptyContext_context_FindEq (T := CoreLParams) Env
  have helem : ∀ e' ∈ ets.map (fun et => LExpr.unresolved (LExpr.applySubstT et S.subst)),
      (LExpr.HasTypeA [] e' sharedTy ∧ BinderAnnotsKnown C e') ∧
        (FactorySigsKnown C.knownTypes C.functions →
          ScopesAnnotAgree C Env.context.dealias.types e') := by
    intro e' he'
    obtain ⟨et, het, rfl⟩ := List.mem_map.mp he'
    obtain ⟨idx, hi, rfl⟩ := List.mem_iff_getElem.mp het
    have hj : idx < ets.length := hi
    have hes : idx < es.length := by simpa only [hlen] using hi
    obtain ⟨Ei, Ei', hri, hwfi, heqi, -, habsi⟩ := hper idx hes hj
    have hresolved0 : TContext.AliasesResolved Env0.context := by
      simpa only [Env0, TEnv.pushEmptySubstScope, TEnv.pushEmptyContext,
        TEnv.updateContext, TEnv.context, TContext.AliasesResolved] using
        (AliasesResolved_of_invariant hinv.toTypeCheckLoopInvariant)
    have hresolvedi : TContext.AliasesResolved Ei.context :=
      heqi.symm.aliasesResolved hresolved0
    let ei : Expression.Expr := List.get es ⟨idx, hes⟩
    have hsourcei := hri
    change SourceExpr.resolve { C with idents := i } Ei ei =
      .ok (ets[idx], Ei') at hsourcei
    obtain ⟨EiDirect, hriDirect, hlinkAbs⟩ := SourceExpr.resolve_link_absorbs
      { C with idents := i } Ei Ei' ei ets[idx] hsourcei
    have habsS : Subst.absorbs S.subst EiDirect.stateSubstInfo.subst :=
      Subst.absorbs_trans EiDirect.stateSubstInfo.subst Ei'.stateSubstInfo.subst S.subst hlinkAbs
        (Subst.absorbs_trans Ei'.stateSubstInfo.subst EnvR.stateSubstInfo.subst S.subst
          habsi (Constraints.unify_absorbs _ _ _ hunify))
    have htyped := Lambda.resolve_HasTypeA_subst ei ets[idx] { C with idents := i } Ei
      EiDirect hriDirect hwfi (hQ.sigWF _ hinv.factory) hresolvedi S.subst habsS
    have hBi : BinderAnnotsKnown C (LExpr.unresolved (LExpr.applySubstT ets[idx] S.subst)) :=
      resolve_binderAnnotations_known { C with idents := i } Ei EiDirect ei ets[idx] hriDirect
        hwfi (hQ.sigWF _ hinv.factory) S.subst habsS hrangeS
    rw [LExpr.applySubstT_toLMonoTy] at htyped
    rw [hshared ets[idx] (List.getElem_mem hi)] at htyped
    refine ⟨⟨htyped, hBi⟩, fun hs => ?_⟩
    have hEi : TContext.FindEq (T := CoreLParams) Ei.context Env.context :=
      heqi.toFindEq.trans hEnv0
    have hA := resolve_annotAgree { C with idents := i } Ei EiDirect ei ets[idx] hriDirect hwfi
      (hQ.sigWF _ hinv.factory) (MonoScope_of_findEq hEi hinv.mono)
      (hEi.2 ▸ hs.sigsFixed hfresh0.containsName_eq_false) S.subst habsS
    exact ScopesAnnotAgree.of_functions_eq (C := { C with idents := i }) rfl
      (ScopesAnnotAgree.of_find? (Γ := TContext.subst Ei.context.resolveTypes S.subst)
        (Ξ := Env.context.dealias)
        (fun x => (subst_dealias_find?_of_closed S.subst Env Ei.context hEi hinv.envWF.aliasesWF
          hinv.ctxClosed hinv.mono x).symm) hA)
  refine ⟨idents, C, (EnvR.popSubstScope.popContext).updateContext Env.context,
    Decl.distinct l
      (ets.map fun et => LExpr.unresolved (LExpr.applySubstT et S.subst)) md,
    fun hs _ _ P => ⟨DeclWellTyped.distinct C Env.context.dealias.types l _ md
        ⟨sharedTy, fun e' he' => ⟨(helem e' he').1.1, (helem e' he').1.2, (helem e' he').2 hs⟩⟩
        hstored,
      trivial, TContext.FindEq.refl _⟩,
    ?_, AliasStepFresh.of_aliases_eq rfl, KnownTypesExtends.refl _,
    fun hk => AmbientTypesKnown.of_findEq (TContext.FindEq.refl _) (KnownTypesExtends.refl _) hk,
    List.Subset.refl _, fun hs hd => ⟨hs, hd⟩, by simp [Decl.kind], ⟨_, hrec⟩⟩
  · refine ⟨TypeCheckLoopInvariant.distinct_step hinv.toTypeCheckLoopInvariant
      ⟨regMsg, hidents⟩ hsource hwfOut, ?_⟩
    refine KnownTypesReady.mono C C Env
      ((EnvR.popSubstScope.popContext).updateContext Env.context)
      (KnownTypesExtends.refl _) ?_ hready
    rw [TEnv.updateContext_stateSubstInfo]
    exact Lambda.TEnv.RangeKnown_popContext EnvR.popSubstScope C.knownTypes
      (Lambda.TEnv.RangeKnown_popSubstScope EnvR C.knownTypes hrangeR)

/-- A function step accepted against a set holding every type name in scope types its output
    declaration and preserves the output invariant. -/
private theorem func_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (func : Function) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.func func md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  obtain ⟨idents, renamed, func', ⟨regMsg, hidents⟩, hnotrec, hfresh, htc', hrec⟩ :=
    WF.Program.typeCheck.stepThen_func_inversion program C Env i func md _ _ h
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have hready := hinv.ready
  have hktEq : (C.addFactoryFunction func'.toLFunc).knownTypes = C.knownTypes :=
    Lambda.addFactoryFunction_knownTypes C func'.toLFunc
  have hsigF : ∀ ty ∈ func'.toLFunc.output :: func'.toLFunc.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true :=
    Function.typeCheckIn_signatureKnown_output (C := { C with idents := idents })
      (func' := func') htc'
  have hnotrec' : ¬ func'.isRecursive := by
    rw [(Function.typeCheckIn_copies_untouched_fields _ {C with idents := idents}
      Env.pushEmptySubstScope func _ func' htc').2.2.1]
    exact hnotrec
  have hfresh' : func'.toLFunc.name.name ∉ C.functions := by
    show func'.name.name ∉ C.functions
    rw [(Function.typeCheckIn_copies_untouched_fields _ _ _ _ _ _ htc').1]
    exact hfresh
  have hfresh0 : AliasNamesFresh C Env.context := hinv.coherent.freshForKnownTypes
  have hmono0 : MonoScope Env.context := hinv.mono
  have hfuncA : FactorySigsKnown C.knownTypes C.functions → AmbientTypesKnown C.knownTypes Env →
      FuncWellTyped C Env.context.dealias.types func' := by
    intro hs hk
    have hfix : FactorySigsFixed Env.context.aliases
        ({ C with idents := idents } : Expression.TyContext).functions :=
      hs.sigsFixed hfresh0.containsName_eq_false
    have hsound := Function.typeCheckIn_sound_output _ { C with idents := idents }
      Env.pushEmptySubstScope func _ func' htc'
      (scopeTyNames_cover_idents_push idents hcov) hwf_push
      (hQ.sigWF _ hinv.factory)
      (AliasesResolved_of_invariant (Env := Env) hinv.toTypeCheckLoopInvariant)
      hready.arrow hready.literals
      (TEnv.RangeKnown_pushEmptySubstScope Env _ hready.substRange) hinv.ctxClosed hmono0
      (AmbientTypesKnown.of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hk)
      hfresh0.containsName_eq_false hfix
    rw [TEnv.pushEmptySubstScope_context_eq Env] at hsound
    exact hsound.withIdents
  have hktExt := KnownTypesExtends.of_knownTypes_eq C _ hktEq
  refine ⟨idents, C.addFactoryFunction func'.toLFunc, Env, Decl.func func' md,
    fun hs _ hk _ => ⟨DeclWellTyped.func C (C.addFactoryFunction func'.toLFunc)
        Env.context.dealias.types func' md hnotrec' hfresh' (hfuncA hs hk)
        (factoryExtendedBy_addFactoryFunction C func'.toLFunc hfresh'),
      trivial, TContext.FindEq.refl _⟩, ?_,
    AliasStepFresh.of_aliases_eq rfl, hktExt,
    fun hk => AmbientTypesKnown.of_findEq (TContext.FindEq.refl _) hktExt hk,
    List.Subset.refl _,
    fun hs hd => tablesKnown_addFactoryFunction hsigF hs hd,
    by simp [Decl.kind], ⟨_, hrec⟩⟩
  · exact ⟨TypeCheckLoopInvariant.func_step hinv.toTypeCheckLoopInvariant hidents
      (LFuncWF_of_typeCheckIn _ _ _ _ _ _ htc' hwf_push.aliasesWF),
      KnownTypesReady.mono _ _ _ _ hktExt hready.substRange hready⟩

/-- A recursive-function block accepted against a set holding every type name in scope types its
    output declaration and preserves the output invariant. -/
private theorem recFuncBlock_declWellTyped_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (funcs : List Function) (md : MetaData Expression)
    {α : Type}
    (k : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String →
      Except Strata.Message α) (res : α) (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.stepThen program PS S { C with idents := i } Env
          (Decl.recFuncBlock funcs md) k = .ok res) :
    OutputNonProcStep Q program C Env fun d' C' Env2 S2 => k d' C' Env2 S2 = .ok res := by
  have h_res := AliasesResolved_of_invariant hinv.toTypeCheckLoopInvariant
  have h_env := hinv.envWF
  have h_fac := hinv.factory
  have h_closed := hinv.ctxClosed
  have h_mono := hinv.mono
  have h_ready := hinv.ready
  have h_fresh : AliasNamesFresh C Env.context := hinv.coherent.freshForKnownTypes
  obtain ⟨v, funcs', Cfinal, Efinal, S', htc, -, hregmono, hnodup, hrec⟩ :=
    Program.typeCheck.stepThen_recFuncBlock_inversion program C Env i funcs md _ _ h
  obtain ⟨hstubCov, -, hbwd, h_fac_stub, h_fac_full, hCstub_eq, hstubKnown, hktEq⟩ :=
    RecFuncBlock.typeCheckIn_accepted_facts C v Env funcs funcs' Cfinal Efinal S' h_env h_fac
      htc hcov
  obtain rfl : Efinal = Env.pushEmptySubstScope :=
    (RecFuncBlock.typeCheckIn_members _ S' { C with idents := v } Cfinal Env.pushEmptySubstScope
      Efinal funcs funcs' htc (scopeTyNames_cover_idents_push v hcov)).1
  have hnoinline := RecFuncBlock.typeCheckIn_noInline _ _ _ _ _ _ _ _ htc
  have hstubNames : (RecFuncBlock.signatureStubs funcs').map (·.name) = funcs.map (·.name) :=
    RecFuncBlock.typeCheckIn_stubs_names _ _ _ _ _ _ _ _ htc
  have h_env0 : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env h_env
  have hpopCtx : (Env.pushEmptySubstScope.popSubstScope).context = Env.context := rfl
  have hrange0 : Lambda.Subst.RangeKnown Env.pushEmptySubstScope.stateSubstInfo.subst
      C.knownTypes :=
    TEnv.RangeKnown_pushEmptySubstScope Env _ h_ready.substRange
  have hnames : funcs'.map (·.name) = funcs.map (·.name) :=
    RecFuncBlock.typeCheckIn_names_eq _ _ _ _ _ _ _ _ htc
  have hfresh := RecFuncBlock.typeCheckIn_names_fresh _ _ _ _ _ _ _ _ htc
  have hfreshChecked : ∀ f' ∈ funcs', f'.name.name ∉ C.functions := by
    have hmapped : ∀ n ∈ funcs.map (·.name), n.name ∉ C.functions :=
      List.forall_mem_map.mpr hfresh
    rw [← hnames] at hmapped
    exact (List.forall_mem_map (P := fun n : CoreLParams.Identifier => n.name ∉ C.functions)).mp
      hmapped
  have hstubArrow :
      (RecFuncBlock.stubContext { C with idents := v }
          (RecFuncBlock.signatureStubs funcs')).knownTypes["arrow"]? = some 2 := by
    rw [hstubKnown]
    exact h_ready.arrow
  have hstubLits : ∀ c : Lambda.LConst, c.isPrimitive = true → LMonoTy.knownInstance c.ty
      (RecFuncBlock.stubContext { C with idents := v }
          (RecFuncBlock.signatureStubs funcs')).knownTypes = true := by
    rw [hstubKnown]
    exact h_ready.literals
  have hstubRange : Lambda.Subst.RangeKnown Env.pushEmptySubstScope.stateSubstInfo.subst
      (RecFuncBlock.stubContext { C with idents := v }
          (RecFuncBlock.signatureStubs funcs')).knownTypes := by
    rw [hstubKnown]
    exact hrange0
  have hsigsFull : ∀ f' ∈ funcs',
      ∀ ty ∈ (f'.toLFunc none).output :: (f'.toLFunc none).inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true := by
    intro f' hf' ty hty
    obtain ⟨f, -, _, htcf⟩ := hbwd f' hf'
    rw [← hstubKnown]
    exact Function.typeCheckIn_signatureKnown_output htcf ty hty
  have hnonempty : funcs' ≠ [] := by
    intro hnil
    apply RecFuncBlock.typeCheckIn_nonempty _ _ _ _ _ _ _ _ htc
    exact List.map_eq_nil_iff.mp (by rw [← hnames, hnil]; rfl)
  have hnoinline' : ∀ f' ∈ funcs', ∀ a ∈ f'.attr, a ≠ .inline := by
    intro f' hf' a ha
    obtain ⟨f, hf, renamed, htcf⟩ := hbwd f' hf'
    rw [(Function.typeCheckIn_copies_untouched_fields _ _ _ f renamed f' htcf).2.2.2] at ha
    exact hnoinline f hf a ha
  have hstubExt : FactoryExtendedBy (fun f g => g = f) C (RecFuncBlock.stubContext C
      (RecFuncBlock.signatureStubs funcs'))
      (funcs'.map fun f =>
        LFunc.mk f.name f.typeArgs (inputs := f.inputs) (output := f.output)) := by
    refine factoryExtendedBy_stubContext C (RecFuncBlock.signatureStubs funcs') funcs' funcs
        hstubNames hnames hnodup hfresh ?_
    intro f' hf'
    have hstub : LFunc.mk f'.name f'.typeArgs (inputs := f'.inputs) (output := f'.output) ∈
        (RecFuncBlock.signatureStubs funcs') := by
      exact (RecFuncBlock.mem_signatureStubs _ _).mpr ⟨f', hf', rfl⟩
    exact ⟨_, hstub, rfl, rfl⟩
  have hfullExt : FactoryExtendedBy (fun f g => g = f) C (RecFuncBlock.fullContext C funcs')
      (funcs'.map (·.toLFunc none)) := by
    refine factoryExtendedBy_fullContext C funcs' funcs' funcs hnames hnames hnodup hfresh ?_
    intro f hf
    exact ⟨f, hf, rfl, rfl⟩
  have hrecursive : ∀ f' ∈ funcs', f'.isRecursive = true := by
    intro f' hf'
    obtain ⟨f, hf, renamed, htcf⟩ := hbwd f' hf'
    rw [(Function.typeCheckIn_copies_untouched_fields _ _ _ f renamed f' htcf).2.2.1]
    exact RecFuncBlock.typeCheckIn_recursive _ _ _ _ _ _ _ _ htc f hf
  have hstubSigs : ∀ stub ∈ RecFuncBlock.signatureStubs funcs',
      ∀ ty ∈ stub.output :: stub.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true := by
    intro stub hstub
    obtain ⟨f', hf', rfl⟩ := (RecFuncBlock.mem_signatureStubs _ _).mp hstub
    exact hsigsFull f' hf'
  have hfreshStub : AliasNamesFresh (RecFuncBlock.stubContext { C with idents := v }
      (RecFuncBlock.signatureStubs funcs'))
      Env.context :=
    AliasNamesFresh.of_eq hstubKnown rfl h_fresh
  have hfuncA : FactorySigsKnown C.knownTypes C.functions → C.DatatypesKnown →
      AmbientTypesKnown C.knownTypes Env → ∀ f' ∈ funcs',
        FuncWellTyped (RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs'))
            Env.context.dealias.types f' := by
    intro hs hd hk f' hf'
    obtain ⟨f, -, renamed, htcf⟩ := hbwd f' hf'
    have hfix : FactorySigsFixed Env.context.aliases
        (RecFuncBlock.stubContext { C with idents := v }
            (RecFuncBlock.signatureStubs funcs')).functions :=
      (stubContext_sigsKnown { C with idents := v } (RecFuncBlock.signatureStubs funcs') hstubSigs
          hs hd).sigsFixed
        hfreshStub.containsName_eq_false
    have hknownS : AmbientTypesKnown
        (RecFuncBlock.stubContext { C with idents := v }
            (RecFuncBlock.signatureStubs funcs')).knownTypes Env := by
      rw [hstubKnown]
      exact hk
    have hsound := Function.typeCheckIn_sound_output _ _ Env.pushEmptySubstScope f renamed f'
      htcf hstubCov h_env0 (hQ.sigWF _ h_fac_stub) h_res
      hstubArrow hstubLits hstubRange
      h_closed h_mono
      (AmbientTypesKnown.of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hknownS)
      hfreshStub.containsName_eq_false hfix
    rw [TEnv.pushEmptySubstScope_context_eq Env, hCstub_eq] at hsound
    exact hsound.withIdents
  have hktExt := KnownTypesExtends.of_knownTypes_eq C _ hktEq
  refine ⟨v, RecFuncBlock.fullContext C funcs', Env.pushEmptySubstScope.popSubstScope,
    Decl.recFuncBlock funcs' md,
    fun hs hd hk _ => ⟨DeclWellTyped.recFuncBlock C (RecFuncBlock.stubContext C
        (RecFuncBlock.signatureStubs funcs'))
        (RecFuncBlock.fullContext C funcs') Env.context.dealias.types funcs' md _ _ hnonempty
        hfreshChecked hnoinline' rfl rfl hstubExt hfullExt
        (fun f hf => hfuncA hs hd hk f hf) hrecursive,
      trivial, TContext.FindEq.refl _⟩, ?_,
    AliasStepFresh.of_aliases_eq (by rw [hpopCtx]), hktExt,
    fun hk => AmbientTypesKnown.of_findEq (TContext.FindEq.refl _) hktExt hk,
    List.Subset.refl _,
    fun hs hd => tablesKnown_foldl_addFactoryFunction funcs' (·.toLFunc none) C hs hd hsigsFull,
    by simp [Decl.kind], ⟨_, hrec⟩⟩
  · exact ⟨TypeCheckLoopInvariant.recFuncBlock_step hinv.toTypeCheckLoopInvariant h_fac_full
      hktEq hregmono,
      KnownTypesReady.mono _ _ _ _ hktExt
        (Lambda.TEnv.RangeKnown_popSubstScope Env.pushEmptySubstScope C.knownTypes hrange0)
        h_ready⟩

/-- An accepted step at a non-procedure declaration from the output invariant, whose scope
    type-name set holds every type name in scope, establishes the facts of a non-procedure
    output step. Its results, scope type-name set included, are received by every continuation
    of the step, and the walk continues from them to the same result. -/
private theorem decl_declWellTyped_output_of_ne_proc
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv) (d : Decl)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (ds : List Decl) (acc out : Decls) (Env' : Expression.TyEnv) (i : Identifiers Unit)
    [WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (hdecl : ∀ n ∈ d.names, DeclaredProgramName program n.name)
    (hkind : d.kind ≠ DeclKind.proc)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env (d :: ds) acc
          = .ok (out, Env')) :
    OutputNonProcStep Q program C Env
      (WalkStepAccepts program PS S { C with idents := i } Env d ds acc out Env') := by
  rw [Program.typeCheck.goWith] at h
  refine Program.typeCheck.stepThen_det program (OutputNonProcStep Q program C Env)
    (fun _ _ hR ⟨i', C2, Env2, d', hstep, hinv2, hfresh, hext, hamb, hsub, htabs, hk, S2, hr⟩ =>
      ⟨i', C2, Env2, d', hstep, hinv2, hfresh, hext, hamb, hsub, htabs, hk, S2,
        hR _ _ _ _ hr⟩)
    ?_ _ _ h
  intro γ k res h
  cases d with
  | type td md =>
    cases td with
    | con tc => exact type_con_declWellTyped_output program C Env tc md k res i hinv h
    | syn ts =>
      exact type_syn_declWellTyped_output program C Env ts md k res i hinv hdecl h
    | data block =>
      exact type_data_declWellTyped_output program C Env block md k res i hinv h
  | ax _ _ | lemma _ _ =>
    exact prop_declWellTyped_output program C Env _ k res i rfl hinv hcov h
  | distinct l es md =>
    exact distinct_declWellTyped_output program C Env l es md k res i hinv h
  | proc proc md => exact absurd rfl hkind
  | func func md => exact func_declWellTyped_output program C Env func md k res i hinv hcov h
  | recFuncBlock funcs md =>
    exact recFuncBlock_declWellTyped_output program C Env funcs md k res i hinv hcov h

/-! ### The shape of the walk's accumulator and output -/

/-- An accepted walk continues after its first declaration, with one more accumulated declaration,
    to the same result, from the results, scope type-name set included, that every continuation
    of the first step receives. -/
private theorem Program.typeCheck.goWith_cons_step (program : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String} (C : Expression.TyContext)
    (Env Env' : Expression.TyEnv) (d : Decl) (ds acc out : Decls)
    (h : Program.typeCheck.goWith program PS S C Env (d :: ds) acc = .ok (out, Env')) :
    ∃ (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl)
      (S2 : Std.HashSet String),
      WalkStepAccepts program PS S C Env d ds acc out Env' d' C2 Env2 S2 := by
  rw [Program.typeCheck.goWith] at h
  obtain ⟨d', C2, Env2, S2, hrec, hdet⟩ := Program.typeCheck.stepThen_ok _ _ _ _ _ _ h
  exact ⟨C2, Env2, d', S2, hrec, hdet⟩

/-- The walk's output is `acc.reverse` followed by one declaration per remaining
    declaration. -/
private theorem Program.typeCheck.goWith_out_eq_reverse_acc_append (program : Program)
    (PS : Thunk (Std.HashSet String)) :
    ∀ (decls : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env : Expression.TyEnv) (acc out : Decls) (Env' : Expression.TyEnv),
      Program.typeCheck.goWith program PS S C Env decls acc = .ok (out, Env') →
      ∃ L, out = acc.reverse ++ L ∧ L.length = decls.length := by
  intro decls
  induction decls with
  | nil =>
    intro _ C Env acc out Env' h
    simp only [Program.typeCheck.goWith, Except.ok.injEq, Prod.mk.injEq] at h
    exact ⟨[], by simp [← h.1], by simp⟩
  | cons d ds IH =>
    intro S C Env acc out Env' h
    obtain ⟨C2, Env2, d', S2, hrec, -⟩ :=
      Program.typeCheck.goWith_cons_step program C Env Env' d ds acc out h
    obtain ⟨L, hL, hlen⟩ := IH S2 C2 Env2 (d' :: acc) out Env' hrec
    refine ⟨d' :: L, ?_, by simpa using hlen⟩
    simpa using hL

/-- At a procedure declaration, the output is `acc.reverse`, then the procedure's elaboration,
    then the rest. -/
private theorem Program.typeCheck.goWith_out_eq_at_proc
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (i : Identifiers Unit) (proc : Procedure) (md : MetaData Expression) (ds acc out : Decls)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env
          (Decl.proc proc md :: ds) acc
          = .ok (out, Env')) :
    ∃ (idents : Identifiers Unit) (proc' : Procedure) (Env2 : Expression.TyEnv) (L : Decls),
      Procedure.typeCheckIn (Thunk.pure S) PS
          { C with idents := idents } Env.pushEmptySubstScope program proc md
          = .ok (proc', Env2)
      ∧ out = acc.reverse ++ Decl.proc proc' md :: L
      ∧ (∀ n : String, n ∈ i → n ∈ idents)
      ∧ Program.typeCheck.goWith program PS S { C with idents := idents } Env2.popSubstScope ds
          (Decl.proc proc' md :: acc) = .ok (out, Env') := by
  rw [Program.typeCheck.goWith] at h
  obtain ⟨idents, proc', Env2, htc, -, hregmono, hrec⟩ :=
    Program.typeCheck.stepThen_proc_inversion program C Env i proc md _ _ h
  obtain ⟨L, hL, _⟩ :=
    Program.typeCheck.goWith_out_eq_reverse_acc_append program PS ds S _ _
      (Decl.proc proc' md :: acc) out Env' hrec
  exact ⟨idents, proc', Env2, L, htc, by simpa using hL, hregmono, hrec⟩

/-! ### Alias freshness across one loop step -/

/-- Some results of a step from `C` and `Env` satisfy `R`, with some scope type-name set: the
    output invariant holds for them, the step adds aliases freshly, and the known-types table
    only grows. -/
abbrev OutputStepAliasFresh (Q : Lambda.Factory CoreLParams → Prop) (program : Program)
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (R : Decl → Expression.TyContext → Expression.TyEnv → Std.HashSet String → Prop) : Prop :=
  ∃ (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (i' : Identifiers Unit) (d' : Decl),
    TypeCheckLoopInvariantOutput Q C2 Env2 i'
    ∧ AliasStepFresh program C Env Env2
    ∧ (∀ n : String, n ∈ C.knownTypes → n ∈ C2.knownTypes)
    ∧ ∃ S2, R d' { C2 with idents := i' } Env2 S2

/-- An accepted step whose scope type-name set holds every type name in scope keeps the output
    invariant, adds aliases freshly and only grows the known-types table. Its results are
    received by every continuation of the step, and the walk continues from them to the same
    result. -/
private theorem Program.typeCheck.goWith_cons_aliasFresh
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (i : Identifiers Unit) (d : Decl) (ds acc out : Decls)
    [WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (hdecl : ∀ n ∈ d.names, DeclaredProgramName program n.name)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env (d :: ds) acc
          = .ok (out, Env')) :
    OutputStepAliasFresh Q program C Env
      (WalkStepAccepts program PS S { C with idents := i } Env d ds acc out Env') := by
  cases d with
  | proc proc md =>
    rw [Program.typeCheck.goWith] at h
    refine Program.typeCheck.stepThen_det program (OutputStepAliasFresh Q program C Env)
      (fun _ _ hR ⟨C2, Env2, i', d', hinv2, hfresh, hmono, S2, hr⟩ =>
        ⟨C2, Env2, i', d', hinv2, hfresh, hmono, S2, hR _ _ _ _ hr⟩)
      ?_ _ _ h
    intro γ k res h
    obtain ⟨idents, proc', Env2, htc, hctxeq, hregmono, hrec⟩ :=
      Program.typeCheck.stepThen_proc_inversion program C Env i proc md k res h
    have haliasEq : (TEnv.context Env2.popSubstScope).aliases = Env.context.aliases := by
      rw [hctxeq]
    exact ⟨C, Env2.popSubstScope, idents, Decl.proc proc' md,
      TypeCheckLoopInvariantOutput.proc_step _ _ C Env Env2 idents program proc proc' md hinv
        hregmono htc,
      AliasStepFresh.of_aliases_eq haliasEq, fun n hn => hn, ⟨_, hrec⟩⟩
  | _ =>
    obtain ⟨i', C2, Env2, d', -, hinv2, hfresh2, hext2, -, -, -, -, hrec⟩ :=
      decl_declWellTyped_output_of_ne_proc program C Env _ ds acc out Env' i hinv hcov hdecl
        (by simp [Decl.kind]) h
    exact ⟨C2, Env2, i', d', hinv2, hfresh2, KnownTypesExtends.mem hext2, hrec⟩

/-! ### Pending procedures are elaborated later -/

/-- A procedure among the remaining declarations is elaborated later in the output under an
    alias list that freshly extends the current one, for a walk whose scope type-name set holds
    every type name in scope. -/
private theorem Program.typeCheck.goWith_pending_procedure_elaborated [WalkFactoryClosed Q]
    (program : Program) (PS : Thunk (Std.HashSet String)) :
    ∀ (decls : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env : Expression.TyEnv) (i : Identifiers Unit) (acc out : Decls) (Env' : Expression.TyEnv),
      Program.typeCheck.goWith program PS S { C with idents := i } Env decls acc
        = .ok (out, Env') →
      (∀ n ∈ scopeTyNames C Env, n ∈ S) →
      TypeCheckLoopInvariantOutput Q C Env i →
      (∀ d ∈ decls, ∀ n ∈ d.names, DeclaredProgramName program n.name) →
      ∀ (q : Procedure) (mdq : MetaData Expression), Decl.proc q mdq ∈ decls →
      ∃ (sc ps : Thunk (Std.HashSet String)) (Cq : Expression.TyContext)
        (Envq Envq' : Expression.TyEnv) (q' : Procedure) (pre post : Decls),
        Procedure.typeCheckIn sc ps Cq Envq program q mdq = .ok (q', Envq')
        ∧ out = acc.reverse ++ (pre ++ Decl.proc q' mdq :: post)
        ∧ AliasStepFresh program C Env Envq := by
  intro decls
  induction decls with
  | nil =>
    intro _ C Env i acc out Env' h _ _ _ q mdq hmem
    simp at hmem
  | cons d ds IH =>
    intro S C Env i acc out Env' h hcov hinv hdecl q mdq hmem
    rcases List.mem_cons.mp hmem with heq | htl
    · subst heq
      obtain ⟨idents, q', Env2, L, htc, hout, -, hrec⟩ :=
        Program.typeCheck.goWith_out_eq_at_proc program C Env Env' i q mdq ds acc out h
      refine ⟨_, _, { C with idents := idents }, Env.pushEmptySubstScope, Env2, q', [], L, htc,
        by simpa using hout, ?_⟩
      exact AliasStepFresh.of_aliases_eq (by rw [TEnv.pushEmptySubstScope_context_eq Env])
    · obtain ⟨C2, Env2, i2, d', hinv2, hfresh, hmono, S2, hrec, hdet⟩ :=
        Program.typeCheck.goWith_cons_aliasFresh program C Env Env' i d ds acc out hinv hcov
          (hdecl d (List.mem_cons_self ..)) h
      rw [Program.typeCheck.goWith] at h
      obtain ⟨sc, ps, Cq, Envq, Envq', q', pre, post, htc, hout, hfreshq⟩ :=
        IH S2 C2 Env2 i2 (d' :: acc) out Env' hrec
          (Program.typeCheck.stepThen_next_cover program _ _ h hcov hdet) hinv2
          (fun d0 hd0 => hdecl d0 (List.mem_cons_of_mem d hd0)) q mdq htl
      exact ⟨sc, ps, Cq, Envq, Envq', q', d' :: pre, post, htc, by simpa using hout,
        AliasStepFresh.trans hmono hfresh hfreshq⟩

/-! ### Declared names of the walk -/

/-- One accepted step of the walk, whatever the declaration: the declaration it emits has the
    same names and kinds as the input, and the rest of the walk continues from it. An input
    procedure becomes the procedure `Procedure.typeCheckIn` returns for it. -/
private theorem Program.typeCheck.goWith_step_shape (p : Program)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String} (C : Expression.TyContext)
    (T : Expression.TyEnv) (decl : Decl) (drest : List Decl) (acc out : Decls)
    (T' : Expression.TyEnv)
    (h : Program.typeCheck.goWith p PS S C T (decl :: drest) acc = .ok (out, T')) :
    ∃ (decl' : Decl) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv)
      (S2 : Std.HashSet String),
      Program.typeCheck.goWith p PS S2 C2 Env2 drest (decl' :: acc) = .ok (out, T')
      ∧ decl'.names = decl.names ∧ declNameKind decl' = declNameKind decl
      ∧ decl'.kind = decl.kind
      ∧ ∀ (proc : Procedure) (md : MetaData Expression), decl = .proc proc md →
        ∃ (sc ps : Thunk (Std.HashSet String)) (Cq : Expression.TyContext)
          (Tq Tq' : Expression.TyEnv) (proc' : Procedure),
          Procedure.typeCheckIn sc ps Cq Tq p proc md = .ok (proc', Tq')
            ∧ decl' = .proc proc' md := by
  obtain ⟨check, hd⟩ | hnone := (decl.propCheck? C).eq_none_or_eq_some.symm
  · rw [Program.typeCheck.goWith] at h
    obtain ⟨_, _, _, -, hcheck, hrec⟩ :=
      Program.typeCheck.stepThen_prop_inversion p C T C.idents decl _ _ hd h
    obtain ⟨hnames, hkind, hnk⟩ := Decl.propCheck?_names_kind hd hcheck
    refine ⟨_, _, _, _, hrec, hnames, hnk, hkind, ?_⟩
    intro proc md hproc
    subst hproc
    simp [Decl.propCheck?] at hd
  cases decl with
  | ax _ _ | lemma _ _ => simp [Decl.propCheck?] at hnone
  | distinct l es md =>
    rw [Program.typeCheck.goWith] at h
    obtain ⟨_, _, _, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_distinct_route p C T l es md _ _ h
    exact ⟨_, _, _, _, hrec, by simp [Decl.names, Decl.name], rfl, rfl, fun _ _ hne => nomatch hne⟩
  | proc proc md =>
    rw [Program.typeCheck.goWith] at h
    obtain ⟨idents, proc', Env2, htc, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_proc_inversion p C T C.idents proc md _ _ h
    have hn := (Procedure.typeCheckIn_env_eq_and_name_eq _ _ _ _ _ _ _ _ _ htc).2
    refine ⟨_, _, _, _, hrec, by simp [Decl.names, Decl.name, hn], rfl, rfl, ?_⟩
    intro proc2 md2 heq
    cases heq
    exact ⟨_, _, _, _, _, proc', htc, rfl⟩
  | func func md =>
    rw [Program.typeCheck.goWith] at h
    obtain ⟨idents, renamed, func', -, -, -, htc, hrec⟩ :=
      WF.Program.typeCheck.stepThen_func_inversion p C T C.idents func md _ _ h
    exact ⟨_, _, _, _, hrec, by
      simp [Decl.names, Decl.name,
        (Function.typeCheckIn_copies_untouched_fields _ _ _ _ _ _ htc).1],
      rfl, rfl, fun _ _ hne => nomatch hne⟩
  | recFuncBlock funcs md =>
    rw [Program.typeCheck.goWith] at h
    obtain ⟨idents, funcs', C2, E2, S', htc, -, -, -, hrec⟩ :=
      Program.typeCheck.stepThen_recFuncBlock_inversion p C T C.idents funcs md _ _ h
    refine ⟨Decl.recFuncBlock funcs' md, _, E2.popSubstScope, _, hrec, ?_, rfl, rfl,
      fun _ _ hne => nomatch hne⟩
    simp only [Decl.names]
    exact RecFuncBlock.typeCheckIn_names_eq _ _ _ _ _ _ _ _ htc
  | type td md =>
    cases td with
    | con tc =>
      rw [Program.typeCheck.goWith] at h
      obtain ⟨idents, ctx, -, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_con_inversion p C T C.idents tc md _ _ h
      exact ⟨_, _, _, _, hrec, rfl, rfl, rfl, fun _ _ hne => nomatch hne⟩
    | syn ts =>
      rw [Program.typeCheck.goWith] at h
      obtain ⟨idents, v, storedTy, Env_ra, -, -, -, -, -, -, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_syn_inversion p C T C.idents ts md _ _ h
      exact ⟨Decl.type (.syn { ts with type := storedTy }) md, _, _, _, hrec, rfl, rfl, rfl,
        fun _ _ hne => nomatch hne⟩
    | data block =>
      rw [Program.typeCheck.goWith] at h
      obtain ⟨idents, block_r, C', -, hres, -, -, hrec⟩ :=
        Program.typeCheck.stepThen_type_data_inversion p C T C.idents block md _ _ h
      refine ⟨_, _, _, _, hrec, ?_, rfl, rfl, fun _ _ hne => nomatch hne⟩
      have hnames := MutualDatatype.resolveAliases_names_map block block_r T T hres
      have h2 := congrArg
        (List.map (fun s : String => ({ name := s, metadata := () } : Expression.Ident))) hnames
      simpa only [List.map_map, Function.comp_def, Decl.names, TypeDecl.names] using h2

/-- For any per-declaration list `g` determined by a declaration's names and kind, a successful
    walk's output gives the accumulator's lists in source order, then the remaining
    declarations' lists. -/
private theorem Program.typeCheck.goWith_names_preserved (p : Program)
    (g : Decl → List Expression.Ident)
    (hg : ∀ d d', d'.names = d.names → declNameKind d' = declNameKind d → g d' = g d)
    (PS : Thunk (Std.HashSet String)) :
    ∀ (S : Std.HashSet String) (C : Expression.TyContext) (T : Expression.TyEnv)
      (remaining : List Decl) (acc : Decls) (out : Decls) (T' : Expression.TyEnv),
      Program.typeCheck.goWith p PS S C T remaining acc = .ok (out, T') →
      out.flatMap g = acc.reverse.flatMap g ++ remaining.flatMap g := by
  intro S C T remaining
  induction remaining generalizing S C T with
  | nil =>
    intro acc out T' h
    simp only [Program.typeCheck.goWith] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp [List.flatMap]
  | cons decl drest IH =>
    intro acc out T' h
    obtain ⟨decl', C2, Env2, S2, hrec, hnames, hkind, -, -⟩ :=
      Program.typeCheck.goWith_step_shape p C T decl drest acc out T' h
    rw [IH S2 C2 Env2 (decl' :: acc) out T' hrec]
    simp only [List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.append_assoc, hg decl decl' hnames hkind]

/-- In a successful walk, every output declaration satisfies `Q` when every accumulated one does,
    every non-procedure declaration satisfies `Q`, and `Procedure.typeCheckIn` takes any
    procedure to one satisfying `Q`, for any name sets. -/
private theorem Program.typeCheck.goWith_out_forall (p : Program) (Q : Decl → Prop)
    (hnonProc : ∀ d, (d.kind == DeclKind.proc) = false → Q d)
    (hproc : ∀ sc ps C Env Env' proc proc' md,
      Procedure.typeCheckIn sc ps C Env p proc md = .ok (proc', Env') → Q (.proc proc' md))
    (PS : Thunk (Std.HashSet String)) :
    ∀ (S : Std.HashSet String) (C : Expression.TyContext) (T : Expression.TyEnv)
      (remaining : List Decl) (acc : Decls) (out : Decls) (T' : Expression.TyEnv),
      Program.typeCheck.goWith p PS S C T remaining acc = .ok (out, T') →
      (∀ d ∈ acc, Q d) → ∀ d ∈ out, Q d := by
  intro S C T remaining
  induction remaining generalizing S C T with
  | nil =>
    intro acc out T' h hacc
    simp only [Program.typeCheck.goWith, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simpa only [List.mem_reverse] using hacc
  | cons decl drest IH =>
    intro acc out T' h hacc
    obtain ⟨decl', C2, Env2, S2, hrec, -, -, hkind, hproc'⟩ :=
      Program.typeCheck.goWith_step_shape p C T decl drest acc out T' h
    refine IH S2 C2 Env2 (decl' :: acc) out T' hrec ?_
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · cases decl with
      | proc proc md =>
        obtain ⟨sc, ps, Cq, Tq, Tq', proc', htc, rfl⟩ := hproc' proc md rfl
        exact hproc sc ps Cq Tq Tq' proc proc' md htc
      | _ =>
        exact hnonProc _ (by rw [hkind]; rfl)
    · exact hacc d hd

/-- If the declaration loop accepts every declaration of a program from an empty accumulator,
    the program's declared names are distinct. -/
private theorem Program.typeCheck.goWith_getNames_nodup_in
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.goWith program PS S C Env program.decls [] = .ok (out, Env')) :
    program.getNames.Nodup := by
  have hnd := WF.Program.typeCheck.goWith_names_nodup h
  simpa [Program.getNames] using hnd

/-- If the declaration loop accepts every declaration of a program, no declared name of the
    program is among the starting context's identifiers. -/
private theorem Program.typeCheck.goWith_getNames_notin_idents
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (acc out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.goWith program PS S C Env program.decls acc = .ok (out, Env')) :
    ∀ n ∈ program.getNames, n.name ∉ C.idents := by
  intro n hn hmem
  have hnot := WF.Program.typeCheck.goWith_names_disjoint h n hn
  rw [Identifiers.contains_eq_containsName_unit,
    Identifiers.containsName_eq_true_iff_mem] at hnot
  exact hnot hmem

/-! ### Call agreement between the input program and its elaboration -/

/-- Every procedure of `program` has its elaborated counterpart in `acc`, if any, related to it by
    `R`. -/
abbrev ElaboratedPrefixRel (R : Procedure → Procedure → Prop) (program : Program) (acc : Decls) :
    Prop :=
  ∀ (x : Expression.Ident) q1 q2, Program.Procedure.find? program x = some q1 →
    Program.Procedure.find? { decls := acc.reverse } x = some q2 → R q1 q2

/-- The prefix relation holds for an empty accumulator. -/
private theorem ElaboratedPrefixRel.init (R : Procedure → Procedure → Prop) (program : Program) :
    ElaboratedPrefixRel R program [] := by
  intro x q1 q2 _ h2
  rw [List.reverse_nil, Program.Procedure.find?_nil] at h2
  simp at h2

/-- Pushing a non-procedure declaration keeps the prefix relation, moving to any weaker relation. -/
private theorem ElaboratedPrefixRel.step_of_kind_ne_proc {R R' : Procedure → Procedure → Prop}
    {program : Program} {acc : Decls} {d : Decl}
    (hmono : ∀ q1 q2, R q1 q2 → R' q1 q2) (hkind : d.kind ≠ DeclKind.proc)
    (h : ElaboratedPrefixRel R program acc) :
    ElaboratedPrefixRel R' program (d :: acc) := by
  intro x q1 q2 h1 h2
  rw [List.reverse_cons,
      Program.Procedure.find?_append_singleton_not_proc acc.reverse d hkind x] at h2
  exact hmono _ _ (h x q1 q2 h1 h2)

/-- Pushing an elaborated procedure that keeps its name and is related by `R` to the program's
    procedure keeps the prefix relation. -/
private theorem ElaboratedPrefixRel.step_proc {R : Procedure → Procedure → Prop}
    {program : Program} {acc : Decls} {proc proc' : Procedure} {md : MetaData Expression}
    (hnameEq : proc'.header.name = proc.header.name)
    (hdeclared : Program.Procedure.find? program proc.header.name = some proc)
    (hnew : R proc proc')
    (h : ElaboratedPrefixRel R program acc) :
    ElaboratedPrefixRel R program (Decl.proc proc' md :: acc) := by
  intro x q1 q2 h1 h2
  rw [List.reverse_cons] at h2
  cases hpre : Program.Procedure.find? { decls := acc.reverse } x with
  | some qp =>
    rw [Program.Procedure.find?_append_of_some acc.reverse [Decl.proc proc' md] x qp hpre] at h2
    have hq : qp = q2 := by simpa using h2
    subst hq
    exact h x q1 qp h1 hpre
  | none =>
    rw [Program.Procedure.find?_append_of_none acc.reverse [Decl.proc proc' md] x hpre] at h2
    obtain ⟨hx, hq2⟩ := Program.Procedure.find?_singleton_proc proc' md x q2 h2
    subst hq2
    rw [hx, hnameEq, hdeclared] at h1
    have hq1 : proc = q1 := by simpa using h1
    subst hq1
    exact hnew

/-- `q2` is a procedure the checker can return for `q1`: it has the resolved signature, against
    the aliases `A`, of a renaming of `q1`'s type parameters (`ProcAlphaVariant`). -/
abbrev ProcSigRenamedResolved (A : List TypeAlias) (q1 q2 : Procedure) : Prop :=
  ∃ (C : LContext CoreLParams) (Γ : TContext Unit) (q' : Procedure),
    TypeSpec.ProcAlphaVariant C Γ q1 q' ∧ ProcSigResolved A q' q2

/-- A procedure with distinct type parameters and the resolved signature of its reserved type
    parameters renamed is a procedure the checker can return for it. -/
private theorem ProcSigRenamedResolved.of_resolved {A : List TypeAlias} {q1 q2 : Procedure}
    {avoid : Unit → List String} (hnd : q1.header.typeArgs.Nodup)
    (h : ProcSigResolved A (q1.renameReservedTypeArgs avoid fun _ => procAnnotTys q1) q2) :
    ProcSigRenamedResolved A q1 q2 := by
  have hnil : (LContext.default : Expression.TyContext).rigidTypeVars ++
      ({} : TContext Unit).knownTypeVars = [] := rfl
  have hsub : ∀ v ∈ (LContext.default : Expression.TyContext).rigidTypeVars ++
      ({} : TContext Unit).knownTypeVars, v ∈ avoid () := by
    intro v hv
    rw [hnil] at hv
    exact absurd hv List.not_mem_nil
  exact ⟨_, _, _, Procedure.renameReservedTypeArgs_alphaVariant avoid q1 hnd hsub, h⟩

/-- A call typed against a procedure's resolved signature is typed against a procedure the
    checker can return for it, when the aliases are well formed. -/
private theorem ProcSigRenamedResolved.instOf {A : List TypeAlias} {q1 q2 : Procedure}
    (hA : TContext.AliasesWF ({ aliases := A } : TContext Unit))
    (h : ProcSigRenamedResolved A q1 q2) :
    ProcSigInstOf (q1.resolveSig { aliases := A }) q2 := by
  obtain ⟨_, _, _, ⟨_, hren, rfl⟩, hres⟩ := h
  exact ProcSigResolved.instOf_renameTypeArgs hA hren.1 hres

/-- A procedure the checker can return for `q1` has `q1`'s parameter names. -/
private theorem ProcSigRenamedResolved.keys {A : List TypeAlias} {q1 q2 : Procedure}
    (h : ProcSigRenamedResolved A q1 q2) :
    q1.header.inputs.keys = q2.header.inputs.keys ∧
      q1.header.outputs.keys = q2.header.outputs.keys := by
  obtain ⟨_, _, _, ⟨ren, -, rfl⟩, hres⟩ := h
  obtain ⟨-, hin, hout⟩ := Procedure.renameTypeArgs_names q1 ren
  exact ⟨hin ▸ hres.inputsKeys, hout ▸ hres.outputsKeys⟩

/-- `q2` is a procedure the checker can return for `q1` (`ProcSigRenamedResolved`), with every
    parameter type registered in `ks`. -/
abbrev ProcSigResolvedKnown (A : List TypeAlias) (ks : Lambda.KnownTypes) (q1 q2 : Procedure) :
    Prop :=
  ProcSigRenamedResolved A q1 q2 ∧ ∀ ty ∈ q2.header.inputs.values ++ q2.header.outputs.values,
    LMonoTy.knownInstance ty ks = true

/-- A resolved signature with registered types stays one across a fresh extension of the aliases
    by names the table does not register, and a larger table. -/
private theorem ProcSigResolvedKnown.extend {A A' : List TypeAlias} {ks ks' : Lambda.KnownTypes}
    {q1 q2 : Procedure} (h : ProcSigResolvedKnown A ks q1 q2)
    (hext : TypeAlias.FreshExtension A A')
    (hnew : ∀ al ∈ A', al ∉ A → KnownTypes.containsName ks al.name = false)
    (hks : KnownTypesExtends ks ks') : ProcSigResolvedKnown A' ks' q1 q2 := by
  have hlist : ∀ us vs : LMonoTys, vs = us.map ({ aliases := A } : TContext Unit).resolveTy →
      (∀ ty ∈ vs, LMonoTy.knownInstance ty ks = true) →
      vs = us.map ({ aliases := A' } : TContext Unit).resolveTy := by
    intro us vs hvs hk
    rw [hvs]
    refine List.map_congr_left fun t ht => ?_
    have hmem : ({ aliases := A } : TContext Unit).resolveTy t ∈ vs := by
      rw [hvs]
      exact List.mem_map_of_mem ht
    exact (TContext.resolveTy_eq_of_FreshExtension (T := CoreLParams)
      (Γ := { aliases := A }) (Γ' := { aliases := A' }) hext hnew (hk _ hmem)).symm
  obtain ⟨⟨C0, Γ0, q', halpha, hres⟩, hk⟩ := h
  exact ⟨⟨C0, Γ0, q', halpha, hres.typeArgs, hres.inputsKeys, hres.outputsKeys,
      hlist _ _ hres.inputsVals fun ty hty => hk ty (List.mem_append_left _ hty),
      hlist _ _ hres.outputsVals fun ty hty => hk ty (List.mem_append_right _ hty)⟩,
    fun ty hty => knownInstance_mono ty ks ks' hks (hk ty hty)⟩

/-- Every procedure of `program` has its name in the elaborated prefix or is still pending in
    `ds`. -/
def RemainingDeclarationsCoverProcedures (program : Program) (acc ds : Decls) : Prop :=
  ∀ (x : Expression.Ident) q1, Program.Procedure.find? program x = some q1 →
    (Program.Procedure.find? { decls := acc.reverse } x).isSome
    ∨ (∃ md, Decl.proc q1 md ∈ ds)

/-- Every procedure is pending before the walk starts. -/
private theorem RemainingDeclarationsCoverProcedures.init (program : Program) :
    RemainingDeclarationsCoverProcedures program [] program.decls := by
  intro x q1 h
  obtain ⟨md, hmem, _⟩ := Program.Procedure.find?_mem_decls program x q1 h
  exact Or.inr ⟨md, hmem⟩

/-- Moving a non-procedure declaration to the accumulator keeps every procedure covered. -/
private theorem RemainingDeclarationsCoverProcedures.step_of_kind_ne_proc {program : Program}
    {acc ds : Decls} {d d' : Decl} (hkind : d.kind ≠ DeclKind.proc)
    (h : RemainingDeclarationsCoverProcedures program acc (d :: ds)) :
    RemainingDeclarationsCoverProcedures program (d' :: acc) ds := by
  intro x q1 h1
  rcases h x q1 h1 with hpre | ⟨md, hmem⟩
  · left
    rw [List.reverse_cons]
    obtain ⟨qp, hqp⟩ := Option.isSome_iff_exists.mp hpre
    rw [Program.Procedure.find?_append_of_some acc.reverse [d'] x qp hqp]
    simp
  · right
    rcases List.mem_cons.mp hmem with heq | htl
    · exact absurd (heq ▸ hkind) (by simp [Decl.kind])
    · exact ⟨md, htl⟩

/-- When the program's procedure named `x` is the declared `proc`, any `proc'` named like `proc`
    is named `x`. -/
private theorem procName_of_find?_eq {program : Program} {x : Expression.Ident}
    {q1 proc proc' : Procedure} {md md1 : MetaData Expression}
    (h1 : Program.Procedure.find? program x = some q1)
    (heq : Decl.proc q1 md1 = Decl.proc proc md)
    (hnameEq : proc'.header.name = proc.header.name) :
    q1 = proc ∧ proc'.header.name = x := by
  have hq1 : q1 = proc := by
    simp only [Decl.proc.injEq] at heq; exact heq.1
  obtain ⟨-, -, hname⟩ := Program.Procedure.find?_mem_decls program x q1 h1
  exact ⟨hq1, by rw [hnameEq, ← hq1]; exact hname⟩

/-- Moving a procedure to the accumulator under the same name keeps every procedure covered. -/
private theorem RemainingDeclarationsCoverProcedures.step_proc {program : Program} {acc ds : Decls}
    {proc proc' : Procedure} {md : MetaData Expression}
    (hnameEq : proc'.header.name = proc.header.name)
    (h : RemainingDeclarationsCoverProcedures program acc (Decl.proc proc md :: ds)) :
    RemainingDeclarationsCoverProcedures program (Decl.proc proc' md :: acc) ds := by
  intro x q1 h1
  rcases h x q1 h1 with hpre | ⟨md1, hmem⟩
  · left
    rw [List.reverse_cons]
    obtain ⟨qp, hqp⟩ := Option.isSome_iff_exists.mp hpre
    rw [Program.Procedure.find?_append_of_some acc.reverse [Decl.proc proc' md] x qp hqp]
    simp
  · rcases List.mem_cons.mp hmem with heq | htl
    · left
      have hx := (procName_of_find?_eq h1 heq hnameEq).2
      rw [List.reverse_cons]
      cases hpre : Program.Procedure.find? { decls := acc.reverse } x with
      | some qp =>
        rw [Program.Procedure.find?_append_of_some acc.reverse [Decl.proc proc' md] x qp hpre]
        simp
      | none =>
        rw [Program.Procedure.find?_append_of_none acc.reverse [Decl.proc proc' md] x hpre]
        rw [← hx, Program.Procedure.find?_cons_proc_self proc' md []]
        simp
    · exact Or.inr ⟨md1, htl⟩

/-- At a procedure step, every named callee of the program has a procedure of its name in the
    elaborated program related to it by `R`. -/
private theorem procedureCalls_of_loop_invariants (R : Procedure → Procedure → Prop)
    (program : Program) (acc ds L out : Decls)
    (proc proc' : Procedure) (md : MetaData Expression) (names : List String)
    (hout : out = acc.reverse ++ Decl.proc proc' md :: L)
    (hnameEq : proc'.header.name = proc.header.name)
    (hcov : RemainingDeclarationsCoverProcedures program acc (Decl.proc proc md :: ds))
    (hpre : ElaboratedPrefixRel R program acc)
    (hself : R proc proc')
    (hforward : ∀ x ∈ names, ∀ q1, Program.Procedure.find? program x = some q1 →
       (∃ md1, Decl.proc q1 md1 ∈ ds) →
       ∃ q2, Program.Procedure.find? { decls := out } x = some q2 ∧ R q1 q2) :
    ProcedureCallsRel R program { decls := out } names := by
  intro x hx q1 h1
  cases hprefix : Program.Procedure.find? { decls := acc.reverse } (x : Expression.Ident) with
  | some qp =>
    refine ⟨qp, ?_, hpre _ q1 qp h1 hprefix⟩
    rw [hout]
    exact Program.Procedure.find?_append_of_some acc.reverse (Decl.proc proc' md :: L) _ qp hprefix
  | none =>
    have hcont :
        Program.Procedure.find? { decls := acc.reverse ++ Decl.proc proc' md :: L }
            (x : Expression.Ident)
          = Program.Procedure.find? { decls := Decl.proc proc' md :: L } (x : Expression.Ident) :=
      Program.Procedure.find?_append_of_none acc.reverse (Decl.proc proc' md :: L) _ hprefix
    rcases hcov (x : Expression.Ident) q1 h1 with hsome | ⟨md1, hmem⟩
    · rw [hprefix] at hsome; simp at hsome
    · rcases List.mem_cons.mp hmem with heq | htl
      · obtain ⟨hq1, hx'⟩ := procName_of_find?_eq h1 heq hnameEq
        refine ⟨proc', ?_, ?_⟩
        · rw [hout, hcont, ← hx']
          exact Program.Procedure.find?_cons_proc_self proc' md L
        · rw [hq1]; exact hself
      · exact hforward x hx q1 h1 ⟨md1, htl⟩

/-! ### Distinct declared names of a whole-program walk -/

/-- The output declarations and environment produced by checking every declaration of a program
    from an empty accumulator, with some type-name sets. -/
def IsWholeProgramWalkResult (program : Program) (out : Decls) (Env' : Expression.TyEnv) : Prop :=
  ∃ (C0 : Expression.TyContext) (Env0 : Expression.TyEnv) (i0 : Identifiers Unit)
    (PS : Thunk (Std.HashSet String)) (S : Std.HashSet String),
    Program.typeCheck.goWith program PS S { C0 with idents := i0 } Env0 program.decls []
      = .ok (out, Env')

/-- The output of a whole-program walk declares the program's names, in order. -/
private theorem getNames_out_of_IsWholeProgramWalkResult
    (program : Program) (out : Decls) (Env' : Expression.TyEnv)
    (hwalk : IsWholeProgramWalkResult program out Env') :
    ({ decls := out } : Program).getNames = program.getNames := by
  obtain ⟨C0, Env0, i0, PS, S, hgo⟩ := hwalk
  have hpres := Program.typeCheck.goWith_names_preserved program Decl.names (fun _ _ hn _ => hn)
    PS S _ Env0 program.decls [] out Env' hgo
  simp only [List.reverse_nil, List.flatMap_nil, List.nil_append] at hpres
  simpa only [Program.getNames, Program.getNames.go] using hpres

/-- The names a program declares of kind `k`, as one list per declaration. -/
private theorem programNamesOfKind_eq_flatMap (P : Program) (k : DeclKind) :
    programNamesOfKind P k
      = P.decls.flatMap fun d => if declNameKind d == k then d.names else [] := by
  simp only [programNamesOfKind]
  induction P.decls with
  | nil => rfl
  | cons d ds ih =>
    cases hk : declNameKind d == k
    · simp only [List.filter_cons, hk, Bool.false_eq_true, ite_false, List.flatMap_cons,
        List.nil_append, ih]
    · simp only [List.filter_cons, hk, ite_true, List.flatMap_cons, ih]

/-- Resolving procedure signatures keeps the names a program declares of each kind. -/
private theorem programNamesOfKind_resolveSigs (A : List TypeAlias) (P : Program) (k : DeclKind) :
    programNamesOfKind (P.resolveSigs A) k = programNamesOfKind P k := by
  have hd : ∀ d : Decl, (if declNameKind (d.resolveSig { aliases := A }) == k
      then (d.resolveSig { aliases := A }).names else [])
      = if declNameKind d == k then d.names else [] := by
    intro d
    cases d <;> rfl
  rw [programNamesOfKind_eq_flatMap, programNamesOfKind_eq_flatMap]
  simp only [Program.resolveSigs, List.flatMap_map, hd]

/-- The output of a whole-program walk declares the same names of each kind as the program. -/
private theorem programNamesOfKind_out_of_IsWholeProgramWalkResult
    (program : Program) (out : Decls) (Env' : Expression.TyEnv)
    (hwalk : IsWholeProgramWalkResult program out Env') (k : DeclKind) :
    programNamesOfKind { decls := out } k = programNamesOfKind program k := by
  obtain ⟨C0, Env0, i0, PS, S, hgo⟩ := hwalk
  have hpres := Program.typeCheck.goWith_names_preserved program
    (fun d => if declNameKind d == k then d.names else [])
    (fun _ _ hn hk => by simp only [hn, hk]) PS S _ Env0 program.decls [] out Env' hgo
  simp only [List.reverse_nil, List.flatMap_nil, List.nil_append] at hpres
  rw [programNamesOfKind_eq_flatMap, programNamesOfKind_eq_flatMap]
  exact hpres

/-- The output of a whole-program walk has distinct declared names. -/
private theorem getNames_nodup_out_of_IsWholeProgramWalkResult
    (program : Program) (out : Decls) (Env' : Expression.TyEnv)
    (hwalk : IsWholeProgramWalkResult program out Env') :
    (Program.getNames.go out).Nodup := by
  have hnames := getNames_out_of_IsWholeProgramWalkResult program out Env' hwalk
  obtain ⟨C0, Env0, i0, PS, S, hgo⟩ := hwalk
  have hnd := Program.typeCheck.goWith_getNames_nodup_in program _ Env0 out Env' hgo
  simp only [Program.getNames] at hnames
  rw [hnames]
  simpa only [Program.getNames] using hnd

/-- If the declaration loop accepts every declaration of a program from an empty accumulator
    and a fresh global substitution scope, its output declarations have distinct declared names. -/
private theorem Program.typeCheck.goWith_getNames_nodup_out
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.goWith program PS S C (Program.typeCheck.startEnv Env)
          program.decls [] = .ok (out, Env')) :
    ({ decls := out } : Program).getNames.Nodup :=
  getNames_nodup_out_of_IsWholeProgramWalkResult program out Env' ⟨C, _, C.idents, PS, S, h⟩

/-- The input of a whole-program walk has distinct declared names. -/
private theorem getNames_nodup_decls_of_IsWholeProgramWalkResult
    (program : Program) (out : Decls) (Env' : Expression.TyEnv)
    (hwalk : IsWholeProgramWalkResult program out Env') :
    (Program.getNames.go program.decls).Nodup := by
  obtain ⟨C0, Env0, i0, PS, S, hgo⟩ := hwalk
  simpa only [Program.getNames] using
    Program.typeCheck.goWith_getNames_nodup_in program _ Env0 out Env' hgo

/-! ### Call agreement at a procedure step -/

/-- At a procedure declaration of a walk whose scope type-name set holds every type name in
    scope, every procedure it calls has a procedure of its name in the elaborated program
    related to it by `R`. -/
private theorem procedureCalls_of_loop_position (R : Procedure → Procedure → Prop)
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (i : Identifiers Unit) (proc : Procedure) (md : MetaData Expression)
    (ds acc out : Decls)
    [WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hdecl : ∀ d ∈ ds, ∀ n ∈ d.names, DeclaredProgramName program n.name)
    (hpre : ElaboratedPrefixRel R program acc)
    (hcov : RemainingDeclarationsCoverProcedures program acc (Decl.proc proc md :: ds))
    (hnodup : (Program.getNames.go out).Nodup)
    (hR : ∀ q q', ProcSigRenamedResolved Env.context.aliases q q' → R q q')
    (hforwardCallee : ∀ (x : String), x ∈ Procedure.calledProcedureNames proc →
      ∀ (q q' : Procedure) (mdq : MetaData Expression) (sc ps : Thunk (Std.HashSet String))
        (Cq : Expression.TyContext) (Envq Envq' : Expression.TyEnv),
      Program.Procedure.find? program (x : Expression.Ident) = some q →
      Decl.proc q mdq ∈ ds →
      Procedure.typeCheckIn sc ps Cq Envq program q mdq = .ok (q', Envq') →
      AliasStepFresh program C Env Envq →
      R q q')
    (hscope : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env
          (Decl.proc proc md :: ds) acc = .ok (out, Env')) :
    ProcedureCallsRel R program { decls := out } (Procedure.calledProcedureNames proc) := by
  obtain ⟨idents, proc', Env2, L, htc, hout, hregmono, hrec⟩ :=
    Program.typeCheck.goWith_out_eq_at_proc program C Env Env' i proc md ds acc out h
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have hctxeq : TEnv.context Env2.popSubstScope = TEnv.context Env :=
    Procedure.typeCheckIn_context_eq _ _ { C with idents := idents } Env.pushEmptySubstScope Env2
      program proc proc' md htc
  have hinv2 : TypeCheckLoopInvariantOutput Q C Env2.popSubstScope idents :=
    TypeCheckLoopInvariantOutput.proc_step _ _ C Env Env2 idents program proc proc' md hinv
      hregmono htc
  have hself := Procedure.typeCheckIn_sigResolved _ _ _ _ _ program proc proc' md htc
  rw [TEnv.pushEmptySubstScope_context_eq Env] at hself
  refine procedureCalls_of_loop_invariants R program acc ds L out
    proc proc' md (Procedure.calledProcedureNames proc) hout
    ((Procedure.typeCheckIn_env_eq_and_name_eq _ _ _ _ _ _ _ _ _ htc).2) hcov hpre
    (hR _ _ (ProcSigRenamedResolved.of_resolved (Procedure.typeCheckIn_typeArgs_nodup htc)
      hself)) ?_
  · intro x hx q1 hfind hpending
    obtain ⟨md1, hmem⟩ := hpending
    obtain ⟨sc, ps, Cq, Envq, Envq', q1', pre, post, htcq, houtq, hfreshq⟩ :=
      Program.typeCheck.goWith_pending_procedure_elaborated program PS ds S C Env2.popSubstScope
        idents (Decl.proc proc' md :: acc) out Env' hrec
        (scopeTyNames_cover_of_context_eq hctxeq hscope) hinv2 hdecl q1 md1 hmem
    have hfreshq' : AliasStepFresh program C Env Envq :=
      AliasStepFresh.of_aliases_eq_left (by rw [hctxeq]) hfreshq
    have hname : q1.header.name = (x : Expression.Ident) := by
      obtain ⟨-, -, hn⟩ := Program.Procedure.find?_mem_decls program _ q1 hfind
      exact hn
    have hnameq : q1'.header.name = q1.header.name :=
      (Procedure.typeCheckIn_env_eq_and_name_eq _ _ _ _ _ _ _ _ _ htcq).2
    have hmemout : Decl.proc q1' md1 ∈ out := by
      rw [houtq]
      exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons_self ..))
    refine ⟨q1', ?_,
      hforwardCallee x hx q1 q1' md1 sc ps Cq Envq Envq' hfind hmem htcq hfreshq'⟩
    have hf := Program.Procedure.find?_of_mem_of_getNames_nodup out q1' md1 hnodup hmemout
    rw [hnameq, hname] at hf
    exact hf

/-- At an accepted procedure declaration of a whole-program walk whose sets hold every type name
    in scope and every type name of the procedure signatures, every procedure it calls has a
    procedure of its name in the elaborated program related to it by `R`. -/
private theorem procedureCalls_of_whole_program_walk (R : Procedure → Procedure → Prop)
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (i : Identifiers Unit) (proc : Procedure) (md : MetaData Expression)
    (ds acc out : Decls)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (hdecl : ∀ d ∈ ds, ∀ n ∈ d.names, DeclaredProgramName program n.name)
    (hwalk : IsWholeProgramWalkResult program out Env')
    (hR : ∀ q q', ProcSigRenamedResolved Env.context.aliases q q' → R q q')
    (hpre : ElaboratedPrefixRel R program acc)
    (hcov : RemainingDeclarationsCoverProcedures program acc (Decl.proc proc md :: ds))
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get)
    (hscope : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env
          (Decl.proc proc md :: ds) acc = .ok (out, Env')) :
    ProcedureCallsRel R program { decls := out } (Procedure.calledProcedureNames proc) := by
  refine procedureCalls_of_loop_position R program C Env Env' i proc md ds acc out
    hinv hdecl hpre hcov
    (getNames_nodup_out_of_IsWholeProgramWalkResult program out Env' hwalk) hR ?_ hscope h
  intro x hx q q' mdq sc ps Cq Envq Envq' hfind hmem htcq hstep
  obtain ⟨idents, proc', Env2, L, htc, hout, -, hrec⟩ :=
    Program.typeCheck.goWith_out_eq_at_proc program C Env Env' i proc md ds acc out h
  have hstep' : AliasStepFresh program ({ C with idents := idents } : Expression.TyContext)
      Env.pushEmptySubstScope Envq :=
    AliasStepFresh.of_aliases_eq_left (by rw [TEnv.pushEmptySubstScope_context_eq Env])
      (AliasStepFresh.of_knownTypes_eq (C := C) rfl hstep)
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have hcl_push : LExpr.checkContextTypesClosed (T := CoreLParams) Env.pushEmptySubstScope := by
    simp only [LExpr.checkContextTypesClosed] at hinv ⊢
    rw [TEnv.pushEmptySubstScope_context_eq Env]
    exact hinv.ctxClosed
  have hres := Procedure.typeCheckIn_forwardCalleeSigResolved _ _ sc ps program
    ({ C with idents := idents }) Env.pushEmptySubstScope Env2 proc proc' md
    Cq Envq Envq' q q' mdq x htc hP hx hfind htcq hstep'.extension
    hstep'.newNotKnown' hstep'.newDeclared hwf_push (hQ.sigWF _ hinv.factory) hcl_push
  rw [TEnv.pushEmptySubstScope_context_eq Env] at hres
  exact hR _ _
    (ProcSigRenamedResolved.of_resolved (Procedure.typeCheckIn_typeArgs_nodup htcq) hres)

/-! ### Procedure signatures of accepted programs -/

/-- In an accepted walk, every declared procedure satisfies `R` when every procedure
    `Procedure.typeCheckIn` accepts, for any name sets, does. -/
private theorem Program.typeCheck.goWith_procs_of_typeCheck (program : Program)
    (R : Procedure → Prop)
    (hR : ∀ sc ps C Env Env' proc proc' md,
      Procedure.typeCheckIn sc ps C Env program proc md = .ok (proc', Env') → R proc)
    (PS : Thunk (Std.HashSet String)) :
    ∀ (ds : Decls) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env Env' : Expression.TyEnv) (acc out : Decls),
      Program.typeCheck.goWith program PS S C Env ds acc = .ok (out, Env') →
      ∀ proc md, Decl.proc proc md ∈ ds → R proc := by
  intro ds
  induction ds with
  | nil => intro _ _ _ _ _ _ _ proc md hmem; exact absurd hmem List.not_mem_nil
  | cons d rest ih =>
    intro S C Env Env' acc out h proc md hmem
    rcases List.mem_cons.mp hmem with heq | hmem'
    · subst heq
      rw [Program.typeCheck.goWith] at h
      obtain ⟨_, proc', _, htc, -, -, -⟩ :=
        Program.typeCheck.stepThen_proc_inversion program C Env C.idents proc md _ _ h
      exact hR _ _ _ _ _ proc proc' md htc
    · obtain ⟨C2, Env2, d2, S2, hrec, -⟩ :=
        Program.typeCheck.goWith_cons_step program C Env Env' d rest acc out h
      exact ih S2 C2 Env2 Env' (d2 :: acc) out hrec proc md hmem'

/-- After an accepted walk over a program's declarations, every procedure the program finds by
    name satisfies `R` when every procedure `Procedure.typeCheckIn` accepts, for any name sets,
    does. -/
private theorem Program.typeCheck.goWith_find?_of_typeCheck (program : Program)
    (R : Procedure → Prop)
    (hR : ∀ sc ps C Env Env' proc proc' md,
      Procedure.typeCheckIn sc ps C Env program proc md = .ok (proc', Env') → R proc)
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String} {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {acc out : Decls}
    (h : Program.typeCheck.goWith program PS S C Env program.decls acc = .ok (out, Env')) :
    ∀ nm proc, Program.Procedure.find? program nm = some proc → R proc := by
  intro nm proc hfind
  obtain ⟨md, hmem, -⟩ := Program.Procedure.find?_mem_decls program nm proc hfind
  exact Program.typeCheck.goWith_procs_of_typeCheck program R hR PS program.decls S C Env Env' acc
    out h proc md hmem

/-- After an accepted walk over a program's declarations, every procedure signature's free type
    variables are among its type parameters. -/
private theorem Program.typeCheck.goWith_procSigsDeclared {program : Program}
    {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String} {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {acc out : Decls}
    (h : Program.typeCheck.goWith program PS S C Env program.decls acc = .ok (out, Env')) :
    ProcSigsDeclared program :=
  Program.typeCheck.goWith_find?_of_typeCheck program _
    (fun sc ps C Env Env' => Procedure.typeCheckIn_noUndeclaredVars sc ps C Env Env' program) h

/-- A procedure step accepted against sets holding every type name in scope and every type name
    of the procedure signatures preserves the output invariant and, given registered ambient
    types and resolved earlier signatures, types its declaration over the alias-resolved scopes
    with valid names; the walk continues with the same scope type-name set. -/
private theorem proc_declWellTyped_output
    (program : Program) {PS : Thunk (Std.HashSet String)} {S : Std.HashSet String}
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (proc : Procedure) (md : MetaData Expression)
    (ds : List Decl) (acc out : Decls) (Env' : Expression.TyEnv) (i : Identifiers Unit)
    [hQ : WalkFactoryClosed Q]
    (hinv : TypeCheckLoopInvariantOutput Q C Env i)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (hdecl : ∀ d ∈ ds, ∀ n ∈ d.names, DeclaredProgramName program n.name)
    (hwalk : IsWholeProgramWalkResult program out Env')
    (hcov : RemainingDeclarationsCoverProcedures program acc (Decl.proc proc md :: ds))
    (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get)
    (hscope : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Program.typeCheck.goWith program PS S { C with idents := i } Env
          (Decl.proc proc md :: ds) acc = .ok (out, Env')) :
    ∃ (i' : Identifiers Unit) (C2 : Expression.TyContext) (Env2 : Expression.TyEnv) (d' : Decl),
      (ElaboratedPrefixRel (ProcSigRenamedResolved Env.context.aliases) program acc →
          AmbientTypesKnown C.knownTypes Env →
          DeclWellTyped { decls := out } C Env.context.dealias.types d' C2
          ∧ DeclNamesWF { decls := out } d')
        ∧ TypeCheckLoopInvariantOutput Q C2 Env2 i'
        ∧ C2 = C
        ∧ AliasStepFresh program C Env Env2
        ∧ (∀ n : String, n ∈ C.knownTypes → n ∈ C2.knownTypes)
        ∧ (AmbientTypesKnown C.knownTypes Env → AmbientTypesKnown C2.knownTypes Env2)
        ∧ Env2.context = Env.context
        ∧ (∃ proc' : Procedure, d' = Decl.proc proc' md
            ∧ proc'.header.name = proc.header.name
            ∧ ProcSigResolvedKnown Env.context.aliases C.knownTypes proc proc')
        ∧ Program.typeCheck.goWith program PS S { C2 with idents := i' } Env2 ds
            (d' :: acc) = .ok (out, Env') := by
  have hcallsR : ElaboratedPrefixRel (ProcSigRenamedResolved Env.context.aliases) program acc →
      ProcedureCallsRel (ProcSigRenamedResolved Env.context.aliases) program { decls := out }
        (Procedure.calledProcedureNames proc) := fun hpreR =>
    procedureCalls_of_whole_program_walk _ program C Env Env' i proc md ds acc out
      hinv hdecl hwalk (fun _ _ hres => hres) hpreR hcov hP hscope h
  rw [Program.typeCheck.goWith] at h
  obtain ⟨idents, proc', Env2, htc, hctxeq, hregmono, hrec⟩ :=
    Program.typeCheck.stepThen_proc_inversion program C Env i proc md _ _ h
  have hwf_push : LExpr.TEnvWF (T := CoreLParams) Env.pushEmptySubstScope :=
    pushEmptySubstScope_preserves_TEnvWF (T := CoreLParams) Env hinv.envWF
  have hready := hinv.ready
  have hbodies : AliasBodiesKnown { C with idents := idents } Env.pushEmptySubstScope.context :=
    AliasBodiesKnown.of_extends C { C with idents := idents } Env.context _
      (by rw [TEnv.pushEmptySubstScope_context_eq Env]) (KnownTypesExtends.refl _)
      hinv.aliasBodies
  have haliasFresh : ∀ al ∈ Env.pushEmptySubstScope.context.aliases,
      ({ C with idents := idents } : Expression.TyContext).knownTypes.containsName al.name
        = false := by
    rw [TEnv.pushEmptySubstScope_context_eq Env]
    exact (AliasNamesFresh.containsName_eq_false hinv.coherent.freshForKnownTypes)
  have haliasEq : (TEnv.context Env2.popSubstScope).aliases = Env.context.aliases := by
    rw [hctxeq]
  have hselfR := Procedure.typeCheckIn_sigResolved _ _ _ _ _ program proc proc' md htc
  rw [TEnv.pushEmptySubstScope_context_eq Env] at hselfR
  have hself : ProcSigResolvedKnown Env.context.aliases C.knownTypes proc proc' :=
    ⟨ProcSigRenamedResolved.of_resolved (Procedure.typeCheckIn_typeArgs_nodup htc) hselfR,
      Procedure.typeCheckIn_paramTypes_knownInstance _ _ ({ C with idents := idents } :
      Expression.TyContext) _ _ program proc proc' md htc⟩
  have hagreeJ : ElaboratedPrefixRel (ProcSigRenamedResolved Env.context.aliases) program acc →
      AmbientTypesKnown C.knownTypes Env →
      DeclWellTyped { decls := out } C Env.context.dealias.types (Decl.proc proc' md) C
      ∧ DeclNamesWF { decls := out } (Decl.proc proc' md) := by
    intro hpreR hk
    have hagreeCalls : ProcedureCallsRel ProcSigInstOf (program.resolveSigs Env.context.aliases)
        { decls := out } (Procedure.calledProcedureNames proc') := by
      intro x hx q1r hf
      rw [Program.resolveSigs_find?] at hf
      obtain ⟨q1, hf1, rfl⟩ := Option.map_eq_some_iff.mp hf
      rw [Procedure.typeCheckIn_calledProcedureNames_eq _ _ _ _ _ _ _ _ _ htc] at hx
      obtain ⟨q2, hf2, hres⟩ := hcallsR hpreR x hx q1 hf1
      exact ⟨q2, hf2, hres.instOf hinv.envWF.aliasesWF⟩
    have hfix : FactorySigsFixed Env.context.aliases
        ({ C with idents := idents } : Expression.TyContext).functions := h_sigsFixed
    have hsound := Procedure.typeCheckIn_sound_output _ _ { C with idents := idents }
      Env.pushEmptySubstScope Env2 program proc proc' md htc
      (scopeTyNames_cover_idents_push idents hscope) hP hwf_push (hQ.sigWF _ hinv.factory)
      (hbodies.aliasesResolved haliasFresh) hinv.mono
      haliasFresh hfix hready.arrow hready.literals
      (TEnv.RangeKnown_pushEmptySubstScope Env _ hready.substRange) hinv.ctxClosed
      (AmbientTypesKnown.of_context_eq (TEnv.pushEmptySubstScope_context_eq Env) hk)
    rw [TEnv.pushEmptySubstScope_context_eq Env, LContext.resolveTable_eq_self hfix] at hsound
    have hnames : ∀ n ∈ ({ decls := out } : Program).getNames,
        n ∈ (program.resolveSigs Env.context.aliases).getNames := by
      rw [Program.resolveSigs_getNames, getNames_out_of_IsWholeProgramWalkResult program out Env'
        hwalk]
      exact fun n hn => hn
    have htypeNames : ∀ n ∈ programNamesOfKind { decls := out } .type,
        n ∈ programNamesOfKind (program.resolveSigs Env.context.aliases) .type := by
      rw [programNamesOfKind_resolveSigs,
        programNamesOfKind_out_of_IsWholeProgramWalkResult program out Env' hwalk]
      exact fun n hn => hn
    exact ⟨DeclWellTyped.proc C Env.context.dealias.types proc' md
        (TypeSpec.ProcWellTyped.program_congr_calls htypeNames hagreeCalls hsound.1.withIdents),
      ProcNamesWF.mono hnames hsound.2⟩
  refine ⟨idents, C, Env2.popSubstScope, Decl.proc proc' md, hagreeJ,
    TypeCheckLoopInvariantOutput.proc_step _ _ C Env Env2 idents program proc proc' md hinv
      hregmono htc, rfl,
    AliasStepFresh.of_aliases_eq haliasEq, fun n hn => hn,
    fun hk => AmbientTypesKnown.of_context_eq hctxeq hk, hctxeq,
    ⟨proc', rfl, (Procedure.typeCheckIn_env_eq_and_name_eq _ _ _ _ _ _ _ _ _ htc).2, hself⟩,
    hrec⟩

/-! ### Output soundness of the declaration walk -/

/-- Every successful declaration walk from the output invariant, with a scope type-name set
    holding every type name in scope and a procedure-signature set holding every type name of
    the procedure signatures, types the emitted suffix over the alias-resolved variable scopes
    and gives it valid names. -/
private theorem goWith_sound_output_generalized (program : Program)
    (PS : Thunk (Std.HashSet String)) (hP : ∀ n ∈ Program.procSigTyNames program, n ∈ PS.get) :
    ∀ (decls : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (Env : Expression.TyEnv) (i : Identifiers Unit) (acc out : Decls) (Env' : Expression.TyEnv),
      Program.typeCheck.goWith program PS S { C with idents := i } Env decls acc
        = .ok (out, Env') →
      (∀ n ∈ scopeTyNames C Env, n ∈ S) →
      TypeCheckLoopInvariantOutput FactorySigWF C Env i →
      FactorySigsKnown C.knownTypes C.functions → C.DatatypesKnown →
      AmbientTypesKnown C.knownTypes Env →
      IsWholeProgramWalkResult program out Env' →
      decls <:+ program.decls →
      ElaboratedPrefixRel (ProcSigResolvedKnown Env.context.aliases C.knownTypes) program acc →
      RemainingDeclarationsCoverProcedures program acc decls →
      ∃ L C', out = acc.reverse ++ L
        ∧ DeclsWellTyped { decls := out } C Env.context.dealias.types L C'
        ∧ DeclsNamesWF { decls := out } L := by
  intro decls
  induction decls with
  | nil =>
    intro _ C Env i acc out Env' h _ _ _ _ _ _ _ _ _
    simp only [Program.typeCheck.goWith, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hout, _⟩ := h
    exact ⟨[], C, by simp [← hout], DeclsWellTyped.nil _ _, trivial⟩
  | cons d ds IH =>
    intro S C Env i acc out Env' h hscope hinv hsigs hdts hk hwalk hsuffix hpreR hcov
    have hsuffixTail : ds <:+ program.decls := (List.suffix_cons d ds).trans hsuffix
    have hdecl : ∀ d' ∈ d :: ds, ∀ n ∈ d'.names, DeclaredProgramName program n.name :=
      declaredProgramName_of_suffix hsuffix
    have hdeclTail : ∀ d' ∈ ds, ∀ n ∈ d'.names, DeclaredProgramName program n.name :=
      declaredProgramName_of_suffix hsuffixTail
    cases d with
    | proc proc md =>
      have hdeclared : Program.Procedure.find? program proc.header.name = some proc :=
        Program.Procedure.find?_of_mem_of_suffix program (Decl.proc proc md :: ds) proc md
          (getNames_nodup_decls_of_IsWholeProgramWalkResult program out Env' hwalk) hsuffix
          (List.mem_cons_self ..)
      obtain ⟨i', C2, Env2, d', hstep, hinv2, hC2, -, -, hamb, hctx2,
          ⟨proc', hd'eq, hnameEq, hself⟩, hrec⟩ :=
        proc_declWellTyped_output program C Env proc md ds acc out Env' i hinv
          (hsigs.sigsFixed (AliasNamesFresh.containsName_eq_false hinv.coherent.freshForKnownTypes))
          hdeclTail hwalk hcov hP hscope h
      subst hd'eq hC2
      have hpreR2 : ElaboratedPrefixRel (ProcSigResolvedKnown Env2.context.aliases C2.knownTypes)
          program (Decl.proc proc' md :: acc) := by
        rw [hctx2]
        exact ElaboratedPrefixRel.step_proc hnameEq hdeclared hself hpreR
      obtain ⟨hJ, hJnames⟩ := hstep (fun x q1 q2 h1 h2 => (hpreR x q1 q2 h1 h2).1) hk
      obtain ⟨L, C3, houtL, hrest, hrestNames⟩ :=
        IH S C2 Env2 i' (Decl.proc proc' md :: acc) out Env' hrec
          (scopeTyNames_cover_of_context_eq hctx2 hscope) hinv2 hsigs hdts
          (hamb hk)
          hwalk hsuffixTail hpreR2 (hcov.step_proc hnameEq)
      rw [hctx2] at hrest
      exact ⟨Decl.proc proc' md :: L, C3, by simpa using houtL, .cons _ _ _ _ _ _ hJ hrest,
        hJnames, hrestNames⟩
    | _ =>
      obtain ⟨i', C2, Env2, d', hstepA, hinv2, hfresh, hext, hamb, -, htabs, hkind, S2, hrec,
          hdet⟩ :=
        decl_declWellTyped_output_of_ne_proc program C Env _ ds acc out Env' i hinv hscope
          (hdecl _ (List.mem_cons_self ..)) (by simp [Decl.kind]) h
      rw [Program.typeCheck.goWith] at h
      obtain ⟨hsigs2, hdts2⟩ := htabs hsigs hdts
      obtain ⟨hJ, hJnames, hfe⟩ := hstepA hsigs hdts hk { decls := out }
      obtain ⟨L, C3, houtL, hrest, hrestNames⟩ := IH S2 C2 Env2 i' (d' :: acc) out Env' hrec
        (Program.typeCheck.stepThen_next_cover program _ _ h hscope hdet) hinv2 hsigs2 hdts2
        (hamb hk) hwalk hsuffixTail
        (ElaboratedPrefixRel.step_of_kind_ne_proc
          (fun _ _ hq => hq.extend hfresh.extension hfresh.newNotKnown' hext) hkind hpreR)
        (hcov.step_of_kind_ne_proc (by simp [Decl.kind]))
      have hfind : ∀ y, Env.context.dealias.types.find? y = Env2.context.dealias.types.find? y :=
        fun y => (hfe.1 y).symm
      exact ⟨d' :: L, C3, by simpa using houtL, .cons _ _ _ _ _ _ hJ (hrest.of_find? hfind),
        hJnames, hrestNames⟩

/-- Output soundness of the whole-program walk from an empty substitution and accumulator,
    against a set `S` holding every type name in scope: the output declarations are well typed
    against the alias-resolved table over the alias-resolved variable scopes, and their names
    are valid. -/
private theorem Program.typeCheck.goWith_sound_output
    (program : Program) (S : Std.HashSet String) (C : Expression.TyContext)
    (Env : Expression.TyEnv) (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.goWith program (procSigTyNameThunk program) S C
          (Program.typeCheck.startEnv Env) program.decls [] = .ok (out, Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_coh : AliasRegistryCoherent C Env C.idents)
    (h_sigsKnown : FactorySigsKnown C.knownTypes C.functions) (h_dts : C.DatatypesKnown)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_ambient : AmbientTypesKnown C.knownTypes Env) :
    (∃ C', DeclsWellTyped { decls := out } (C.resolveTable Env.context.aliases)
        Env.context.dealias.types out C')
      ∧ DeclsNamesWF { decls := out } out := by
  have hinv : TypeCheckLoopInvariantOutput FactorySigWF C
      (Program.typeCheck.startEnv Env) C.idents := by
    refine ⟨⟨TEnv.updateSubst_globalScope_preserves_TEnvWF (T := CoreLParams) Env h_env, h_fac,
      (TEnv.updateSubst_checkContextTypesClosed (T := CoreLParams) Env _).trans h_closed,
      ?_, ?_,
      AliasRegistryCoherent.of_aliases_eq
        (congrArg (·.aliases) (Program.typeCheck.startEnv_context Env)) h_coh,
      AmbientClear.start Env⟩, ⟨h_sigsKnown.1, h_bool, h_lit, ?_⟩⟩
    · rw [Program.typeCheck.startEnv_context]; exact h_aliasBodies
    · rw [Program.typeCheck.startEnv_context]; exact h_mono
    · exact Subst.RangeKnown_push_empty C.knownTypes _ (Subst.RangeKnown_empty C.knownTypes)
  obtain ⟨L, C', houtL, hA, hN⟩ :=
    goWith_sound_output_generalized program (procSigTyNameThunk program)
      (procSigTyNameThunk_cover program) program.decls _ C _ C.idents [] out Env' h
      (scopeTyNames_cover_of_context_eq (Program.typeCheck.startEnv_context Env) hcov)
      hinv h_sigsKnown h_dts
      (AmbientTypesKnown.of_context_eq (Program.typeCheck.startEnv_context Env)
        h_ambient)
      ⟨C, _, C.idents, _, _, h⟩ (List.suffix_refl program.decls)
      (ElaboratedPrefixRel.init _ program) (RemainingDeclarationsCoverProcedures.init program)
  simp only [List.reverse_nil, List.nil_append] at houtL
  subst houtL
  rw [Program.typeCheck.startEnv_context] at hA
  have hfix :=
    h_sigsKnown.sigsFixed (AliasNamesFresh.containsName_eq_false hinv.coherent.freshForKnownTypes)
  rw [Program.typeCheck.startEnv_context] at hfix
  rw [LContext.resolveTable_eq_self hfix]
  exact ⟨⟨C', hA⟩, hN⟩

/-- Output soundness of the whole-program walk from an empty substitution and accumulator: the
    output declarations are well typed against the alias-resolved table over the alias-resolved
    variable scopes, and their names are valid. The ambient context must be well formed as for
    input soundness. In addition, the types the function signatures, datatypes, `bool`,
    primitive literals and ambient variables use are registered. -/
theorem Program.typeCheck.go_sound_output
    (program : Program) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (out : Decls) (Env' : Expression.TyEnv)
    (h : Program.typeCheck.go program C (Program.typeCheck.startEnv Env) program.decls []
          = .ok (out, Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_coh : AliasRegistryCoherent C Env C.idents)
    (h_sigsKnown : FactorySigsKnown C.knownTypes C.functions) (h_dts : C.DatatypesKnown)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_ambient : AmbientTypesKnown C.knownTypes Env) :
    (∃ C', DeclsWellTyped { decls := out } (C.resolveTable Env.context.aliases)
        Env.context.dealias.types out C')
      ∧ DeclsNamesWF { decls := out } out :=
  Program.typeCheck.goWith_sound_output program _ C Env out Env' h (scopeTyNameThunk_cover C Env)
    h_env h_fac h_closed h_aliasBodies h_mono h_coh h_sigsKnown h_dts h_bool h_lit h_ambient

/-! ### Decomposing an accepted program check -/

/-- A successful program check against the scope type-name set `S` walked the declarations,
    from an empty substitution, to the program it returns. -/
private theorem Program.typeCheckIn_ok_inv (S : Std.HashSet String)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheckIn S C Env program = .ok (program', Env')) :
    ∃ out, Program.typeCheck.goWith program (procSigTyNameThunk program) S C
        (Program.typeCheck.startEnv Env) program.decls [] = .ok (out, Env') ∧
      program' = { decls := out } := by
  unfold Program.typeCheckIn Program.typeCheck.withStart at h
  simp only [bind, Except.bind] at h
  elim_err h with v hgo
  obtain ⟨out, envOut⟩ := v
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨out, hgo, rfl⟩

/-! ### Top-level soundness -/

/-- Input soundness: a program `Program.typeCheckIn` accepts, against a set `S` holding every
    type name in scope, is typed by the typechecker spec. The ambient context and environment
    must be well formed: the function signatures are well formed, stored types are closed, the
    scope holds only monotypes, every alias body uses registered types, and no alias is a
    registered type or missing from the identifier registry. -/
theorem Program.typeCheckIn_sound (S : Std.HashSet String)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheckIn S C Env program = .ok (program', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context) :
    ProgramHasType C Env.context program := by
  obtain ⟨out, hgo, -⟩ := Program.typeCheckIn_ok_inv S C Env Env' program program' h
  refine ⟨?_, Program.typeCheck.goWith_getNames_notin_idents program C _ [] out Env' hgo, ?_⟩
  · exact Program.typeCheck.goWith_getNames_nodup_in program C _ out Env' hgo
  · have hd := Program.typeCheck.goWith_sound program S C _ program.decls out Env' hgo
      (scopeTyNames_cover_of_context_eq (Program.typeCheck.startEnv_context Env) hcov)
      (TEnv.updateSubst_globalScope_preserves_TEnvWF (T := CoreLParams) Env h_env) h_fac
      ((TEnv.updateSubst_checkContextTypesClosed (T := CoreLParams) Env _).trans h_closed)
      (Program.typeCheck.startEnv_context Env ▸ h_aliasBodies)
      (Program.typeCheck.startEnv_context Env ▸ h_mono)
      (AliasRegistryCoherent.of_aliases_eq
        (congrArg (·.aliases) (Program.typeCheck.startEnv_context Env)) h_coh)
      (AmbientClear.start Env) (Program.typeCheck.goWith_procSigsDeclared hgo)
    rw [Program.typeCheck.startEnv_context] at hd
    exact hd

/-- Input soundness: a program `Program.typeCheck` accepts is typed by the typechecker spec. The
    ambient context and environment must be well formed: the function signatures are well
    formed, stored types are closed, the scope holds only monotypes, every alias body uses
    registered types, and no alias is a registered type or missing from the identifier
    registry. -/
theorem Program.typeCheck_sound
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheck C Env program = .ok (program', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context) :
    ProgramHasType C Env.context program :=
  Program.typeCheckIn_sound _ C Env Env' program program' h (scopeTyNameThunk_cover C Env) h_env
    h_fac h_closed h_coh h_aliasBodies h_mono

/-- In a successful walk, each remaining procedure has in the output a procedure that
    `Procedure.typeCheckIn` returns for it under some name sets. -/
private theorem Program.typeCheck.goWith_proc_elaborated (p : Program)
    (PS : Thunk (Std.HashSet String)) :
    ∀ (remaining : List Decl) (S : Std.HashSet String) (C : Expression.TyContext)
      (T : Expression.TyEnv) (acc out : Decls) (T' : Expression.TyEnv),
      Program.typeCheck.goWith p PS S C T remaining acc = .ok (out, T') →
      ∀ q md, Decl.proc q md ∈ remaining →
        ∃ (sc ps : Thunk (Std.HashSet String)) (Cq : Expression.TyContext)
          (Tq Tq' : Expression.TyEnv) (q' : Procedure),
          Procedure.typeCheckIn sc ps Cq Tq p q md = .ok (q', Tq') ∧ Decl.proc q' md ∈ out := by
  intro remaining
  induction remaining with
  | nil => intro _ _ _ _ _ _ _ q md hmem; simp at hmem
  | cons d ds IH =>
    intro S C T acc out T' h q md hmem
    obtain ⟨d', C2, T2, S2, hrec, -, -, -, hproc⟩ :=
      Program.typeCheck.goWith_step_shape p C T d ds acc out T' h
    rcases List.mem_cons.mp hmem with rfl | htl
    · obtain ⟨sc, ps, Cq, Tq, Tq', q', htc, rfl⟩ := hproc q md rfl
      obtain ⟨L, rfl, -⟩ :=
        Program.typeCheck.goWith_out_eq_reverse_acc_append p PS ds S2 C2 T2 _ out T' hrec
      exact ⟨sc, ps, Cq, Tq, Tq', q', htc, by simp⟩
    · exact IH S2 C2 T2 (d' :: acc) out T' hrec q md htl

/-- Every call of a CFG body in the program `Program.typeCheckIn` returns, against any scope
    type-name set, is well formed in that program. -/
theorem Program.typeCheckIn_cfgCallsWellFormed {S : Std.HashSet String}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {program program' : Program}
    (h : Program.typeCheckIn S C Env program = .ok (program', Env')) :
    ∀ q md (g : DetCFG) (o : Bool), Decl.proc q md ∈ program'.decls → q.body = .cfg g o →
      ∀ cs ∈ q.callSites, WF.WFcallProp program' cs.procName cs.args := by
  obtain ⟨out, hgo, rfl⟩ := Program.typeCheckIn_ok_inv S C Env Env' program program' h
  intro q md g o hmem hg cs hcs
  have hnonProc : ∀ d : Decl, (d.kind == DeclKind.proc) = false →
      ∀ q md (g : DetCFG) (o : Bool), d = .proc q md → q.body = .cfg g o →
        ∀ cs ∈ q.callSites, callError? program cs.procName cs.args = none := by
    intro d hk q md g o hd
    subst hd
    simp [Decl.kind] at hk
  have hproc : ∀ (sc ps : Thunk (Std.HashSet String)) (Cq : Expression.TyContext)
      (Tq Tq' : Expression.TyEnv) (proc proc' : Procedure) (mdp : MetaData Expression),
      Procedure.typeCheckIn sc ps Cq Tq program proc mdp = .ok (proc', Tq') →
      ∀ q md (g : DetCFG) (o : Bool), Decl.proc proc' mdp = .proc q md → q.body = .cfg g o →
        ∀ cs ∈ q.callSites, callError? program cs.procName cs.args = none := by
    intro _ _ _ _ _ _ _ _ htc q md g o hd hg
    cases hd
    exact Procedure.typeCheckIn_cfgCallsChecked htc hg
  have hacc : ∀ d ∈ ([] : Decls), ∀ q md (g : DetCFG) (o : Bool), d = .proc q md →
      q.body = .cfg g o → ∀ cs ∈ q.callSites, callError? program cs.procName cs.args = none :=
    fun _ hd => absurd hd List.not_mem_nil
  have hchecked := Program.typeCheck.goWith_out_forall program
    (fun d => ∀ q md (g : DetCFG) (o : Bool), d = .proc q md → q.body = .cfg g o →
      ∀ cs ∈ q.callSites, callError? program cs.procName cs.args = none)
    hnonProc hproc _ _ C _ program.decls [] out Env' hgo hacc _ hmem q md g o rfl hg cs hcs
  have hwf := (callError?_eq_none_iff program cs.procName cs.args).mp hchecked
  obtain ⟨q1, hq1⟩ := Option.isSome_iff_exists.mp hwf.defined
  obtain ⟨md1, hmem1, hname1⟩ := Program.Procedure.find?_mem_decls program _ q1 hq1
  obtain ⟨_, _, _, _, _, q2, htc, hmem2⟩ :=
    Program.typeCheck.goWith_proc_elaborated program _ program.decls _ C _ [] out Env' hgo q1 md1
      hmem1
  obtain ⟨hkIn, hkOut⟩ := ProcSigRenamedResolved.keys
    (ProcSigRenamedResolved.of_resolved (Procedure.typeCheckIn_typeArgs_nodup htc)
      (Procedure.typeCheckIn_sigResolved _ _ _ _ _ _ _ _ _ htc))
  have hq2 : Program.Procedure.find? { decls := out } cs.procName = some q2 := by
    rw [← hname1, ← (Procedure.typeCheckIn_env_eq_and_name_eq _ _ _ _ _ _ _ _ _ htc).2]
    exact Program.Procedure.find?_of_mem_of_getNames_nodup out q2 md1
      (Program.typeCheck.goWith_getNames_nodup_out program C Env out Env' hgo) hmem2
  exact WF.WFcallProp.transfer default hwf hq1 hq2 hkIn hkOut rfl

/-- Output soundness: the program `Program.typeCheckIn` returns, against a set `S` holding
    every type name in scope, is well typed against the alias-resolved table over the
    alias-resolved variable scopes, and its names are valid. The ambient context must be well
    formed as for input soundness. In addition, the types the function signatures, datatypes,
    `bool`, primitive literals and ambient variables use are registered. -/
theorem Program.typeCheckIn_sound_output (S : Std.HashSet String)
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheckIn S C Env program = .ok (program', Env'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_sigsKnown : FactorySigsKnown C.knownTypes C.functions) (h_dts : C.DatatypesKnown)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_ambient : AmbientTypesKnown C.knownTypes Env) :
    ProgramWellTyped (C.resolveTable Env.context.aliases) Env.context.dealias.types program' ∧
    ProgramNamesWF (C.resolveTable Env.context.aliases) program' := by
  obtain ⟨out, hgo, rfl⟩ := Program.typeCheckIn_ok_inv S C Env Env' program program' h
  obtain ⟨⟨C', hA⟩, hN⟩ :=
    Program.typeCheck.goWith_sound_output program S C Env out Env' hgo hcov h_env h_fac
      h_closed h_aliasBodies h_mono h_coh h_sigsKnown h_dts h_bool h_lit h_ambient
  have hfresh : ∀ n ∈ ({ decls := out } : Program).getNames,
      n.name ∉ (C.resolveTable Env.context.aliases).idents := by
    rw [getNames_out_of_IsWholeProgramWalkResult program out Env' ⟨C, _, C.idents, _, _, hgo⟩]
    exact Program.typeCheck.goWith_getNames_notin_idents program C _ [] out Env' hgo
  have hnodup := Program.typeCheck.goWith_getNames_nodup_out program C Env out Env' hgo
  have hnodupDecls : (out.flatMap Decl.names).Nodup := hnodup
  refine ⟨⟨fun _ => (List.filter_sublist.flatMap_of_sublist _).nodup hnodupDecls, C', hA⟩,
    hnodup, hfresh, hN⟩

/-- Output soundness: the program `Program.typeCheck` returns is well typed against the
    alias-resolved table over the alias-resolved variable scopes, and its names are valid. The
    ambient context must be well formed as for input soundness. In addition, the types the
    function signatures, datatypes, `bool`, primitive literals and ambient variables use are
    registered. -/
theorem Program.typeCheck_sound_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (program program' : Program)
    (h : Program.typeCheck C Env program = .ok (program', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_coh : AliasRegistryCoherent C Env C.idents) (h_aliasBodies : AliasBodiesKnown C Env.context)
    (h_mono : MonoScope Env.context)
    (h_sigsKnown : FactorySigsKnown C.knownTypes C.functions) (h_dts : C.DatatypesKnown)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_ambient : AmbientTypesKnown C.knownTypes Env) :
    ProgramWellTyped (C.resolveTable Env.context.aliases) Env.context.dealias.types program' ∧
    ProgramNamesWF (C.resolveTable Env.context.aliases) program' :=
  Program.typeCheckIn_sound_output _ C Env Env' program program' h (scopeTyNameThunk_cover C Env)
    h_env h_fac h_closed h_coh h_aliasBodies h_mono h_sigsKnown h_dts h_bool h_lit h_ambient

end Core

end -- public section
