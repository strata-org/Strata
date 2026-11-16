/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.DatatypeWF
public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.LExprTypeSpec

/-! ## Datatype blocks (Core view)

A resolved constructor, datatype or mutual datatype block corresponds to its source when names
and type parameters agree and argument types are alias-equivalent.
`MutualADTWF` bundles the `Lambda`-level datatype relations into the well-formedness of a mutual
datatype block in an ambient `LContext CoreLParams`. -/

namespace Core
namespace TypeSpec

open Lambda

public section

/-- A resolved constructor matches its source: the same name, tester name and argument names,
    with argument types alias-equivalent in `Γ`. -/
def ConstrTyCompat (Γ : TContext Unit)
    (c_r c : LConstr Unit) : Prop :=
  c_r.name = c.name ∧ c_r.testerName = c.testerName ∧
  List.Rel₂ (fun ar a => ar.1 = a.1 ∧ AliasEquiv Γ.aliases ar.2 a.2) c_r.args c.args

/-- A resolved datatype corresponds to its source: the same name and type parameters, with
    constructors related pointwise. -/
def DatatypeTyCompat (Γ : TContext Unit)
    (d_r d : LDatatype Unit) : Prop :=
  d_r.name = d.name ∧ d_r.typeArgs = d.typeArgs ∧
  List.Rel₂ (ConstrTyCompat Γ) d_r.constrs d.constrs

/-- `block_r` is an alias-equivalent copy of `block`: they correspond datatype by datatype. -/
def MutualBlockTyCompat (Γ : TContext Unit)
    (block_r block : List (LDatatype Unit)) : Prop :=
  List.Rel₂ (DatatypeTyCompat Γ) block_r block

/--
Declarative well-formedness of a mutual datatype block `block` in ambient
context `C`.

Inhabitance is required against `C.datatypes.push block`, the factory extended
with the new block, so that mutual and forward references between the block's
datatypes resolve.

Every block that `LContext.addMutualBlock` accepts satisfies `MutualADTWF`
(`Datatype.addMutualBlock_sound`).
-/
structure MutualADTWF (C : LContext CoreLParams) (block : MutualDatatype Unit) : Prop where
  /-- The block is non-empty. -/
  nonempty : block ≠ []
  /-- Datatype names in the block are distinct. -/
  namesNodup : (block.map (·.name)).Nodup
  /-- All datatypes in the block declare the same type parameters, ignoring order. -/
  typeArgsAgree : ∀ d ∈ block, ∀ d' ∈ block, ∀ v, v ∈ d.typeArgs ↔ v ∈ d'.typeArgs
  /-- No datatype declares a type parameter twice. -/
  typeArgsNodup : ∀ d ∈ block, d.typeArgs.Nodup
  /-- No declared type parameter starts with a reserved prefix. -/
  typeArgsNotReserved : ∀ d ∈ block, ∀ v ∈ d.typeArgs, isAllowedName v = true
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
  /-- Every type-constructor reference in a constructor argument is applied at the
      right arity: its argument count equals the referenced type's arity — a known
      type's registered arity, or a datatype's number of `typeArgs` (an existing
      datatype of `C` or one declared in the block). -/
  argsWellKinded : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ∀ ref n, (ref, n) ∈ getTypeConsArities arg.2 →
        C.knownTypes[ref]? = some n ∨
        (∃ d' ∈ C.datatypes.allDatatypes, d'.name = ref ∧ d'.typeArgs.length = n) ∨
        (∃ d' ∈ block, d'.name = ref ∧ d'.typeArgs.length = n)
  /-- Every datatype in the block is inhabited. -/
  inhabited : ∀ d ∈ block, TySymInhab (C.datatypes.push block) d.name

end -- public section

end TypeSpec
end Core
