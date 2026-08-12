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
datatype block in an ambient `LContext CoreLParams`.
-/

namespace Core
namespace TypeSpec

open Lambda

public section

/--
Declarative well-formedness of a mutual datatype block `block` in ambient
context `C`.

Inhabitance is required against `C.datatypes.push block`, the factory extended
with the new block, so that mutual and forward references between the block's
datatypes resolve.
-/
structure MutualADTWF (C : LContext CoreLParams) (block : MutualDatatype Unit) : Prop where
  /-- The block is non-empty. -/
  nonempty : block ≠ []
  /-- Datatype names in the block are distinct. -/
  namesNodup : (block.map (·.name)).Nodup
  /-- The block's names do not clash with existing known types. -/
  namesFresh : ∀ d ∈ block, ¬ C.knownTypes.containsName d.name
  /-- The block's names do not redefine existing datatypes. -/
  namesNew : ∀ d ∈ block, C.datatypes.getType d.name = none
  /-- Every free type variable of a constructor argument is one of the enclosing
      datatype's own `typeArgs` (constructor arguments introduce no fresh type
      variables). -/
  argVarsScoped : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs
  /-- Every constructor argument type is not-nested and strictly-positive/uniform. -/
  argsWF : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2
  /-- Every type name referenced in a constructor argument is a known type of
      `C`, an existing datatype of `C`, or a name declared in the block. -/
  refsKnown : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ∀ ref ∈ getTypeRefs arg.2,
      ref ∈ C.knownTypes.keywords ∨ ref ∈ C.datatypes.allTypeNames ∨ ref ∈ block.map (·.name)
  /-- Every datatype in the block is inhabited. -/
  inhabited : ∀ d ∈ block, TySymInhab (C.datatypes.push block) d.name

end -- public section

end TypeSpec
end Core
