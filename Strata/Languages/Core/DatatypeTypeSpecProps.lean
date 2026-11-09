/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.DatatypeTypeSpec
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.TypeFactoryProps
import Strata.Util.ListUtilsProps

/-! ## Soundness of the datatype checker

`Datatype.addMutualBlock_sound`: when the checker accepts a mutual datatype block, the block
satisfies the declarative well-formedness `MutualADTWF`. `MutualADTWF.refsKnown`: in a
well-formed block, every referenced type name is known. -/

namespace Core
namespace TypeSpec

open Lambda

public section

/-- In a well-formed mutual datatype block, every type name referenced in a constructor argument
    is a known type of the context, an existing datatype of the context, or a datatype of the
    block. This follows from every reference being applied at its arity. -/
theorem MutualADTWF.refsKnown {C : Expression.TyContext} {block : List (LDatatype Unit)}
    (hwf : MutualADTWF C block) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ ref ∈ getTypeRefs arg.2,
      ref ∈ C.knownTypes.keywords ∨ ref ∈ C.datatypes.allTypeNames ∨ ref ∈ block.map (·.name) := by
  intro d hd c hc arg harg ref href
  obtain ⟨n, hn⟩ := (mem_getTypeRefs_iff arg.2 ref).mp href
  rcases hwf.argsWellKinded d hd c hc arg harg ref n hn with
    hbase | ⟨e, he, hek, -⟩ | ⟨e, he, hek, -⟩
  · refine Or.inl ?_
    simp only [Lambda.KnownTypes.keywords]
    have hsome : (C.knownTypes[ref]?).isSome = true := by rw [hbase]; rfl
    exact Std.HashMap.mem_keys.mpr (Std.HashMap.mem_iff_isSome_getElem?.mpr hsome)
  · exact Or.inr (Or.inl (hek ▸ List.mem_map_of_mem he))
  · exact Or.inr (Or.inr (hek ▸ List.mem_map_of_mem he))

/-- When registering a mutual datatype block in a context succeeds, the block is well-formed in
    that context (`MutualADTWF`). -/
theorem Datatype.addMutualBlock_sound
    {C : Expression.TyContext} {block : List (LDatatype Unit)} {C' : Expression.TyContext}
    (h : C.addMutualBlock block = .ok C') :
    MutualADTWF C block := by
  obtain ⟨hfresh, hds⟩ := LContext.addMutualBlock_ok_inv C C' block h
  obtain ⟨hval, hargswf, hvars, hnew, hrefs, hinhab⟩ :=
    TypeFactory.addMutualBlock_ok_inv C.datatypes C'.datatypes block C.knownTypes hds
  obtain ⟨hne, hnames, hagree, hnodup, hreserved⟩ := validateMutualBlock_sound block hval
  refine
    { nonempty := hne
      namesNodup := hnames
      typeArgsAgree := hagree
      typeArgsNodup := hnodup
      typeArgsNotReserved := hreserved
      namesFresh := hfresh
      namesNew := hnew
      argVarsScoped := checkConstructorArgVarsScoped_sound block hvars
      argsWF := checkConstructorArgsWF_sound block hargswf
      argsWellKinded := ?_
      inhabited := checkMutualBlockInhab_sound _ block hinhab }
  intro d hd c hc arg harg ref n hn
  have hlk := validateTypeReferences_arities C.datatypes block C.knownTypes hrefs
    d hd c hc arg harg ref n hn
  rcases foldl_insert_lookup (C.datatypes.allDatatypes ++ block) (fun e => e.name)
    (fun e => e.typeArgs.length) C.knownTypes ref n hlk with ⟨e, he, hek, hev⟩ | hbase
  · rcases List.mem_append.mp he with hAll | hBlk
    · exact Or.inr (Or.inl ⟨e, hAll, hek, hev⟩)
    · exact Or.inr (Or.inr ⟨e, hBlk, hek, hev⟩)
  · exact Or.inl hbase

end -- public section

end TypeSpec
end Core
