/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.TypeSpecShared
public import Strata.Languages.Core.Typing.Spec.FactoryRegistration
public import Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.KnownTypesProps
import Strata.DL.Lambda.TypeFactoryProps
import Strata.DL.Lambda.DatatypeFactoryWFProps
import Strata.Languages.Core.DatatypeTypeSpecProps

/-! ## Registering functions and datatype blocks

Registering factory functions and mutual datatype blocks keeps the factory
signatures allowed (`FactorySigsAllowed`) and registered (`FactorySigsKnown`)
and keeps alias names unregistered (`AliasNamesFresh`); factory extensions
(`FactoryExtendedBy`) compose. Key theorems:
`FactorySigsAllowed.addMutualBlock`, `FactorySigsKnown.addMutualBlock`,
`AliasNamesFresh.addMutualBlock` and `factoryExtendedBy_append`. -/

namespace Core

open Lambda Imperative

public section

/-! ### Allowed factory signatures -/

/-- Adding a function whose input and output types name only type constructors
    without a reserved prefix keeps every factory signature free of such
    names. -/
theorem FactorySigsAllowed.addFactoryFunction {C : Expression.TyContext}
    {fn : LFunc CoreLParams} (hC : FactorySigsAllowed C)
    (hfn : ∀ ty ∈ fn.output :: fn.inputs.values,
      mtyAllTyConsNames isAllowedName ty = true) :
    FactorySigsAllowed (C.addFactoryFunction fn) := by
  intro lf hlf
  rcases mem_addFactoryFunction C fn lf hlf with hold | rfl
  · exact hC lf hold
  · exact hfn

/-! ### Keeping alias names unregistered -/

/-- When no alias name is a registered type, every registered type name differs
    from every alias name. -/
private theorem AliasNamesFresh.knownTypesAll {C : Expression.TyContext}
    {Γ : TContext Unit} (h : AliasNamesFresh C Γ) :
    LContext.KnownTypesAll (fun n => ∀ al ∈ Γ.aliases, al.name ≠ n) C := by
  intro n hn al hal heq
  exact absurd (heq ▸ hn) (h al hal)

/-- Registering a type whose name no alias has keeps every alias name
    unregistered. -/
theorem AliasNamesFresh.addKnownTypeWithError {C C' : Expression.TyContext}
    {Γ : TContext Unit} {k : KnownType} {msg : Strata.Message}
    (hk : ∀ al ∈ Γ.aliases, al.name ≠ k.name)
    (hadd : C.addKnownTypeWithError k msg = .ok C')
    (h : AliasNamesFresh C Γ) :
    AliasNamesFresh C' Γ := by
  have hall := h.knownTypesAll
  intro al hal hmem
  exact KnownTypesAll_addKnownTypeWithError C C' k msg hk hadd hall al.name
    hmem al hal rfl

/-- Registering a datatype block naming no alias keeps every alias name
    unregistered. -/
theorem AliasNamesFresh.addMutualBlock {C C' : Expression.TyContext}
    {Γ : TContext Unit} {block : List (LDatatype Unit)}
    (hnames : ∀ d ∈ block, ∀ al ∈ Γ.aliases, al.name ≠ d.name)
    (hadd : C.addMutualBlock block = .ok C') (h : AliasNamesFresh C Γ) :
    AliasNamesFresh C' Γ := by
  have hall := h.knownTypesAll
  intro al hal hmem
  exact KnownTypesAll_addMutualBlock C C' block hnames hadd hall al.name hmem
    al hal rfl

end -- public section

namespace TypeSpec

public section

/-! ### Composing factory extensions -/

/-- Factory extension under one agreement relation holds under any weaker
    one. -/
theorem FactoryExtendedBy.mono
    {agrees agrees' : LFunc CoreLParams → LFunc CoreLParams → Prop}
    {C C' : Expression.TyContext} {newFuncs : List (LFunc CoreLParams)}
    (himp : ∀ f g, agrees f g → agrees' f g)
    (h : FactoryExtendedBy agrees C C' newFuncs) :
    FactoryExtendedBy agrees' C C' newFuncs :=
  { h with
    contains_new := fun f hf =>
      let ⟨g, hg, hagree⟩ := h.contains_new f hf
      ⟨g, hg, himp f g hagree⟩ }

/-- Factory extension is transitive, with the newly added function lists
    concatenated. -/
theorem factoryExtendedBy_append
    {agrees : LFunc CoreLParams → LFunc CoreLParams → Prop}
    {C C1 C2 : Expression.TyContext} {xs ys : List (LFunc CoreLParams)}
    (h1 : FactoryExtendedBy agrees C C1 xs)
    (h2 : FactoryExtendedBy agrees C1 C2 ys) :
    FactoryExtendedBy agrees C C2 (xs ++ ys) := by
  refine { knownTypes_eq := ?_, datatypes_eq := ?_, idents_eq := ?_,
           rigidTypeVars_eq := ?_, preserves_old := ?_, contains_new := ?_,
           no_other := ?_ }
  · rw [h2.knownTypes_eq, h1.knownTypes_eq]
  · rw [h2.datatypes_eq, h1.datatypes_eq]
  · rw [h2.idents_eq, h1.idents_eq]
  · rw [h2.rigidTypeVars_eq, h1.rigidTypeVars_eq]
  · intro nm g h; exact h2.preserves_old nm g (h1.preserves_old nm g h)
  · intro f hf
    rcases List.mem_append.mp hf with hx | hy
    · obtain ⟨g, hg, hagree⟩ := h1.contains_new f hx
      exact ⟨g, h2.preserves_old _ g hg, hagree⟩
    · exact h2.contains_new f hy
  · intro nm h
    rcases h2.no_other nm h with h1c | hys
    · rcases h1.no_other nm h1c with hC | hxs
      · exact Or.inl hC
      · rw [List.map_append]
        exact Or.inr (List.mem_append.mpr (Or.inl hxs))
    · rw [List.map_append]
      exact Or.inr (List.mem_append.mpr (Or.inr hys))

end -- public section

end TypeSpec

public section

/-! ### Registering a mutual block: generated signatures and known types -/

/-- Registering a mutual datatype block keeps every factory signature naming
    only type constructors without a reserved prefix, when the block's datatype
    names and constructor argument types have none. -/
theorem FactorySigsAllowed.addMutualBlock {C C' : Expression.TyContext}
    {block : List (LDatatype Unit)} (hC : FactorySigsAllowed C)
    (hnames : ∀ d ∈ block, isAllowedName d.name = true)
    (hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      mtyAllTyConsNames isAllowedName arg.2 = true)
    (h : C.addMutualBlock block = .ok C') :
    FactorySigsAllowed C' := by
  obtain ⟨-, ds, fgen, fs, ks, -, hfgen, hfs, -, rfl⟩ :=
    LContext.addMutualBlock_ok_eq C C' block h
  intro lf hlf
  simp only [Factory.addFactory, Factory.tryAddAll] at hfs
  rw [← Array.foldlM_toList] at hfs
  rcases Factory.mem_foldlM_tryPush _ C.functions fs hfs lf hlf with
    hold | hnew
  · exact hC lf hold
  · have hnew' : lf ∈ fgen.toArray := by simpa using hnew
    exact genBlockFactory_sigsAllowed block fgen hnames hargs hfgen lf hnew'

end -- public section

end Core

namespace Lambda

open Core Core.TypeSpec

public section

/-- Registering a mutual block appends to the function table only functions
    whose input and output types are registered instances of the new
    known-types table, when the incoming table registers `arrow` and `bool` and
    the incoming context's datatypes are registered. -/
private theorem addMutualBlock_newSigsKnown {C C' : Expression.TyContext}
    {block : List (LDatatype Unit)}
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_bool : C.knownTypes["bool"]? = some 0) (hdts : C.DatatypesKnown)
    (h : C.addMutualBlock block = .ok C') :
    ∃ fgen : Lambda.Factory CoreLParams,
      C.functions.addFactory fgen = .ok C'.functions ∧
      ∀ f ∈ fgen.toArray, ∀ ty ∈ f.output :: f.inputs.values,
        LMonoTy.knownInstance ty C'.knownTypes = true := by
  have hwf := Datatype.addMutualBlock_sound h
  have hextC := KnownTypesExtends.of_addMutualBlock C C' block h
  obtain ⟨-, ds, fgen, fs, ks', -, hfgen, hfs, hks, rfl⟩ :=
    LContext.addMutualBlock_ok_eq C _ block h
  have hblock : ∀ d ∈ block, ks'[d.name]? = some d.typeArgs.length :=
    knownTypes_foldlM_add_mem C.knownTypes ks' block hks
  have hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      LMonoTy.knownInstance arg.2 ks' = true := by
    intro d hd c hc arg harg
    refine LMonoTy.wellKinded_knownInstance arg.2 ks' ?_
    intro ref n hn
    rcases hwf.argsWellKinded d hd c hc arg harg ref n hn with
      hk | ⟨d', hd', rfl, rfl⟩ | ⟨d', hd', rfl, rfl⟩
    · exact hextC _ _ hk
    · exact hextC _ _ (hdts d' hd')
    · exact hblock d' hd'
  exact ⟨fgen, hfs, genBlockFactory_sigsKnown block fgen (hextC _ _ h_arrow)
    (hextC _ _ h_bool) hblock hargs hfgen⟩

/-- Registering a mutual datatype block keeps `arrow` registered at arity 2 and
    every factory signature built from registered type constructors at their
    arities, provided the incoming context has this property, registers `bool`
    at arity 0, and registers each of its datatypes at its number of type
    parameters. -/
theorem FactorySigsKnown.addMutualBlock {C C' : Expression.TyContext}
    {block : List (LDatatype Unit)}
    (hC : FactorySigsKnown C.knownTypes C.functions)
    (h_bool : C.knownTypes["bool"]? = some 0)
    (hdts : C.DatatypesKnown) (h : C.addMutualBlock block = .ok C') :
    FactorySigsKnown C'.knownTypes C'.functions := by
  obtain ⟨fgen, hfs, hnew⟩ := addMutualBlock_newSigsKnown hC.1 h_bool hdts h
  exact FactorySigsKnown.tryAddAll hfs
    (hC.mono (KnownTypesExtends.of_addMutualBlock C C' block h)) hnew

end -- public section

end Lambda
