/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics

namespace Strata.Laurel

public section

/-- The kind (constructor tag) of a `ResolvedNode`, used to assert that a reference
    resolves to the expected sort of definition. -/
inductive ResolvedNodeKind where
  | var
  | parameter
  | staticProcedure
  | instanceProcedure
  | field
  | compositeType
  | constrainedType
  | datatypeDefinition
  | datatypeConstructor
  | datatypeDestructor
  | typeAlias
  | constant
  | quantifierVar
  | coroutineType
  | typeParameter
  | unresolved
  deriving Repr, BEq

def ResolvedNodeKind.name : ResolvedNodeKind → String
  | .var               => "variable"
  | .parameter         => "parameter"
  | .staticProcedure   => "static procedure"
  | .instanceProcedure => "instance procedure"
  | .field             => "field"
  | .compositeType     => "composite type"
  | .constrainedType   => "constrained type"
  | .datatypeDefinition => "datatype definition"
  | .datatypeConstructor => "datatype constructor"
  | .datatypeDestructor => "datatype destructor"
  | .typeAlias         => "type alias"
  | .constant          => "constant"
  | .quantifierVar     => "quantifier variable"
  | .coroutineType     => "coroutine type"
  | .typeParameter     => "type parameter"
  | .unresolved        => "unresolved"

/-- A definition-site AST node that a reference can resolve to. -/
inductive ResolvedNode where
  /-- A local variable declaration. -/
  | var (name : Identifier) (type : HighTypeMd)
  /-- A procedure parameter. -/
  | parameter (param : Parameter)
  /-- A static procedure. -/
  | staticProcedure (proc : Procedure)
  /-- An instance procedure (method) on a composite type. -/
  | instanceProcedure (typeName : Identifier) (proc : Procedure)
  /-- A field on a composite type. -/
  | field (typeName : Identifier) (fld : Field)
  /-- A composite type definition. -/
  | compositeType (ty : CompositeType)
  /-- A constrained type definition. -/
  | constrainedType (ty : ConstrainedType)
  /-- A datatype definition. -/
  | datatypeDefinition (ty : DatatypeDefinition)
  /-- A datatype constructor. -/
  | datatypeConstructor (typeName : Identifier) (ctor : DatatypeConstructor)
  /-- An auto-generated destructor (or unsafe `!`-destructor) for a datatype field.
      `typeName` is the resolved Identifier of the parent datatype (with its
      `uniqueId`), and `field` is the underlying constructor parameter. -/
  | datatypeDestructor (typeName : Identifier) (field : Parameter)
  /-- A type alias. -/
  | typeAlias (ty : TypeAlias)
  /-- A constant. -/
  | constant (c : Constant)
  /-- A quantifier-bound variable. -/
  | quantifierVar (name : Identifier) (type : HighTypeMd)
  /-- A coroutine type definition. The coroutine name is dual: it names a
      type (`co: c`) whose values are coroutine instances, and a constructor
      (`c(args)` spawns one). Later lowered to a state composite `<c>State`
      plus a spawn procedure. -/
  | coroutineType (proc : Procedure)
  /-- A datatype's type parameter (a type variable), in scope only while resolving
      that datatype's constructor argument types. Registering it lets a reference
      to a type parameter resolve through the normal scope lookup — like any other
      type name — instead of being special-cased by name via a threaded list. -/
  | typeParameter (name : Identifier)
  | unresolved (referenceSource: FileRange)
  deriving Repr

instance : Inhabited ResolvedNode where
  default := ResolvedNode.unresolved default

/-- Return the constructor tag of a `ResolvedNode`. -/
def ResolvedNode.kind : ResolvedNode → ResolvedNodeKind
  | .var ..               => .var
  | .parameter ..         => .parameter
  | .staticProcedure ..   => .staticProcedure
  | .instanceProcedure .. => .instanceProcedure
  | .field ..             => .field
  | .compositeType ..     => .compositeType
  | .constrainedType ..   => .constrainedType
  | .datatypeDefinition .. => .datatypeDefinition
  | .datatypeConstructor .. => .datatypeConstructor
  | .datatypeDestructor .. => .datatypeDestructor
  | .typeAlias ..         => .typeAlias
  | .constant ..          => .constant
  | .quantifierVar ..     => .quantifierVar
  | .coroutineType ..     => .coroutineType
  | .typeParameter ..     => .typeParameter
  | .unresolved _          => .unresolved

def ResolvedNode.getType (node: ResolvedNode): HighTypeMd := match node with
 | .var _ type => type
 | .parameter p => p.type
 | .field _ f => f.type
 | .datatypeConstructor type _ => ⟨ .UserDefined type, type.source ⟩
 | .datatypeDestructor _ fld => fld.type
 | .constant c => c.type
 | .quantifierVar _ type => type
 -- A type parameter (`T` in `procedure f<T>` / `datatype D<T>`) carries the
 -- polymorphism substrate: it resolves to `HighType.TVar`, not erased to
 -- `Unknown`.
 | .typeParameter name => ⟨ .TVar name, name.source ⟩
 | .unresolved source => ⟨ .Unknown, source ⟩
 | .staticProcedure proc => ⟨ .Unknown, proc.name.source ⟩
 | .instanceProcedure _ proc => ⟨ .Unknown, proc.name.source ⟩
 | .compositeType ty => ⟨ .Unknown, ty.name.source ⟩
 | .constrainedType ty => ⟨ .Unknown, ty.name.source ⟩
 | .datatypeDefinition ty => ⟨ .Unknown, ty.name.source ⟩
 | .typeAlias ty => ⟨ .Unknown, ty.name.source ⟩
 | .coroutineType proc => ⟨ .Unknown, proc.name.source ⟩

/-! ## Resolution result -/

structure SemanticModel where
  nextId: Nat
  compositeCount: Nat
  refToDef: Std.HashMap Nat ResolvedNode
  /-- Procedures that (transitively) read the heap, keyed by `uniqueId`. Computed
      once by `HeapAnalysis` during resolution so downstream checks can decide
      whether a call reads the heap without re-running the call-graph analysis. -/
  heapReaders: Std.HashSet Nat := {}
  /-- Procedures that (transitively) write the heap, keyed by `uniqueId`. See `heapReaders`. -/
  heapWriters: Std.HashSet Nat := {}
  /-- UniqueIds of static procedures whose registration was rejected as a
      duplicate (conflicting signature with an existing overload). These must
      not be renamed by `UniqueOverloadNames`. -/
  conflictingOverloads: Std.HashSet Nat := {}
  deriving Repr

/-- Look up the resolved node for an identifier, returning `none` if the identifier
    has no `uniqueId` or is not in the model. -/
def SemanticModel.get? (model: SemanticModel) (iden: Identifier): Option ResolvedNode :=
  iden.uniqueId.bind model.refToDef.get?

def SemanticModel.get (model: SemanticModel) (iden: Identifier): ResolvedNode :=
  (model.get? iden).getD default

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (model: SemanticModel) (name : Identifier) : Except String (List CompositeType) := do
  let rec go (fuel : Nat) (current : Identifier) : List CompositeType :=
    match fuel with
    | 0 =>
      match model.get current with
      | .compositeType (ty : CompositeType) => [ty]
      | _ => []
    | fuel' + 1 =>
      match model.get current with
        | .compositeType (ty : CompositeType) =>
          -- `extending` is `List HighTypeMd`; ancestry keys on the parent NAME (an
          -- instantiation `Base<T>` shares `Base`'s ancestor chain), so peel the base.
          [ty] ++ ty.extending.flatMap (fun parent =>
            match highBaseName? parent.val with | some n => go fuel' n | none => [])
        | _ => []
  let mut seen : Std.HashSet Nat := {}
  let mut acc : List CompositeType := []
  for ct in go model.compositeCount name do
    let uid ← Identifier.getUniqueId ct.name
    if !seen.contains uid then
      acc := acc ++ [ct]
      seen := seen.insert uid
  pure acc
