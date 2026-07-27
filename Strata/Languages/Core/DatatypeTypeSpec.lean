/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.DatatypeWF
public import Strata.Languages.Core.Expressions

/-! ## Declarative Well-Formedness of a Mutual Datatype Block (Core view)

Bundles the `Lambda`-level datatype relations (`Strata.DL.Lambda.DatatypeWF`)
into `MutualADTWF`, the Core-facing well-formedness predicate for a mutual
datatype block in an ambient `LContext CoreLParams`. This is the declarative
counterpart of `LContext.addMutualBlock` (→ `TypeFactory.addMutualBlock`).
-/

namespace Core
namespace TypeSpec

open Lambda

public section

/--
Declarative well-formedness of a mutual datatype block `block` in ambient
context `C`. Bundles the obligations discharged by `LContext.addMutualBlock`
(→ `TypeFactory.addMutualBlock`), each stated declaratively:

The inhabitance obligation is checked against `C.datatypes.push block`, the
factory extended with the new block, so that mutual and forward references
resolve (matching the checker, which inhabits after pushing the block).
-/
structure MutualADTWF (C : LContext CoreLParams) (block : MutualDatatype Unit) : Prop where
  /-- The block is non-empty (`validateMutualBlock`). -/
  nonempty : block ≠ []
  /-- Datatype names in the block are distinct (`validateMutualBlock`). -/
  namesNodup : (block.map (·.name)).Nodup
  /-- The block's names do not clash with existing known types (the
      known-type guard of `addMutualBlock`). -/
  namesFresh : ∀ d ∈ block, ¬ C.knownTypes.containsName d.name
  /-- The block's names do not redefine existing datatypes (the redefinition
      guard of `addMutualBlock`). -/
  namesNew : ∀ d ∈ block, C.datatypes.getType d.name = none
  /-- Every constructor argument type is not-nested and strictly-positive/uniform
      (`checkConstructorArgsWF`). -/
  argsWF : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2
  /-- Every type name referenced in a constructor argument is a known type of
      `C`, an existing datatype of `C`, or a name declared in the block
      (`validateTypeReferences`). -/
  refsKnown : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ ref ∈ getTypeRefs arg.2,
      ref ∈ C.knownTypes.keywords ∨ ref ∈ C.datatypes.allTypeNames ∨ ref ∈ block.map (·.name)
  /-- Every datatype in the block is inhabited (`checkMutualBlockInhab`, which
      calls `adt_inhab d.name = typesym_inhab adts [] d.name`). -/
  inhabited : ∀ d ∈ block, TySymInhab (C.datatypes.push block) d.name

end -- public section

end TypeSpec
end Core
