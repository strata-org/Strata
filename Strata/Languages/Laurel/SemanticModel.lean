
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import Strata.Util.Tactics
import Strata.Languages.Python.PythonLaurelCorePrelude

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
  | unresolved (referenceSource: Option FileRange)
  deriving Repr

instance : Inhabited ResolvedNode where
  default := ResolvedNode.unresolved none

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
  | .unresolved _          => .unresolved

def ResolvedNode.getType (node: ResolvedNode): HighTypeMd := match node with
 | .var _ type => type
 | .parameter p => p.type
 | .field _ f => f.type
 | .datatypeConstructor type _ => ⟨ .UserDefined type, none ⟩
 | .datatypeDestructor _ fld => fld.type
 | .constant c => c.type
 | .quantifierVar _ type => type
 | .unresolved source => ⟨ .Unknown, source ⟩
 | .staticProcedure _ | .instanceProcedure _ _ | .compositeType _
 | .constrainedType _ | .datatypeDefinition _ | .typeAlias _ => ⟨ .Unknown, none ⟩

/-! ## Resolution result -/

structure SemanticModel where
  nextId: Nat
  compositeCount: Nat
  refToDef: Std.HashMap Nat ResolvedNode
  deriving Repr

/-- Look up the resolved node for an identifier, returning `none` if the identifier
    has no `uniqueId` or is not in the model. -/
def SemanticModel.get? (model: SemanticModel) (iden: Identifier): Option ResolvedNode :=
  iden.uniqueId.bind model.refToDef.get?

def SemanticModel.get (model: SemanticModel) (iden: Identifier): ResolvedNode :=
  (model.get? iden).getD default

def SemanticModel.isFunction (model: SemanticModel) (id: Identifier): Bool :=
  match model.get id with
      | .staticProcedure proc => proc.isFunctional
      | .parameter _ => true
      | .datatypeConstructor _ _ => true
      | .datatypeDestructor _ _ => true
      | .constant _ => true
      | .unresolved _ => true -- functions calls are more permissive, so true avoids possibly incorrect errors
      | node =>
          dbg_trace s!"Sound but incomplete BUG! id: {repr id}, is not a procedure, but a node {repr node}"
          false

/--
Compute the flattened set of ancestors for a composite type, including itself.
Traverses the `extending` list transitively.
-/
def computeAncestors (model: SemanticModel) (name : Identifier) : List CompositeType :=
  let rec go (fuel : Nat) (current : Identifier) : List CompositeType :=
    match fuel with
    | 0 =>
      match model.get current with
      | .compositeType (ty : CompositeType) => [ty]
      | _ => []
    | fuel' + 1 =>
      match model.get current with
        | .compositeType (ty : CompositeType) =>
          [ty] ++ ty.extending.flatMap (fun parent => go fuel' parent)
        | _ => []
  let seen : List Identifier := []
  (go model.compositeCount name).foldl (fun (acc, seen) ct =>
    if seen.contains ct.name then (acc, seen)
    else (acc ++ [ct], seen ++ [ct.name])) ([], seen) |>.1
