/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData
public import Strata.Languages.Core.Expressions
public import Strata.Languages.Core.Procedure
import Strata.Util.Tactics
import Strata.DDM.Util.Decimal

/-
Documentation for Laurel can be found in docs/verso/LaurelDoc.lean
-/
namespace Strata
namespace Laurel

public section

abbrev MetaData := Imperative.MetaData Core.Expression
-- Explicit instance needed for deriving Repr in the mutual block
instance : Repr MetaData := inferInstance

/-- A name-introduction site (variable declaration, procedure, field, type, etc.).
    Carries a mandatory unique ID assigned by the resolution pass. -/
structure Identifier where
  /-- The declared name. -/
  text : String
  /-- Unique ID assigned by the resolution pass. -/
  uniqueId : Option Nat := none
  /-- Source-level metadata (locations, annotations). -/
  md : MetaData
  deriving Repr

-- Temporary hack because the Python through Laurel pipeline doesn't resolve
instance : BEq Identifier where
  beq a b := a.text == b.text

instance : Inhabited Identifier where
 default := { text := "defaultIdentifier", md := .empty }

instance : ToString Identifier where
  toString id := id.text

instance : Coe String Identifier where
  coe s := { text := s, md := .empty }

def mkId (name: String): Identifier := { text := name, md := .empty }

/--
Primitive operations available in Laurel expressions.

Operations are grouped into boolean operations (`Eq`, `Neq`, `And`, `Or`,
`Not`, `Implies`), arithmetic operations (`Neg`, `Add`, `Sub`, `Mul`, `Div`,
`Mod`, `DivT`, `ModT`), and comparison operations (`Lt`, `Leq`, `Gt`, `Geq`).

Equality on composite types uses reference equality for impure types and
structural equality for pure ones.
-/
inductive Operation : Type where
  /-- Equality test. Uses reference equality for impure composite types, structural equality for pure ones. -/
  | Eq
  /-- Inequality test. -/
  | Neq
  /-- Logical conjunction (eager). -/
  | And
  /-- Logical disjunction (eager). -/
  | Or
  /-- Logical negation. -/
  | Not
  /-- Logical implication (short-circuit). -/
  | Implies
  /-- Short-circuit logical conjunction. Only evaluates the second argument if the first is true. -/
  | AndThen
  /-- Short-circuit logical disjunction. Only evaluates the second argument if the first is false. -/
  | OrElse
  /-- Arithmetic negation. Works on `Int` and `Float64`. -/
  | Neg
  /-- Addition. Works on `Int` and `Float64`. -/
  | Add
  /-- Subtraction. Works on `Int` and `Float64`. -/
  | Sub
  /-- Multiplication. Works on `Int` and `Float64`. -/
  | Mul
  /-- Euclidean division. Works on `Int` and `Float64`. -/
  | Div
  /-- Euclidean modulus. Works on `Int` and `Float64`. -/
  | Mod
  /-- Truncation division. -/
  | DivT
  /-- Truncation modulus. -/
  | ModT
  /-- Less than. Works on `Int` and `Real`. -/
  | Lt
  /-- Less than or equal. Works on `Int` and `Real`. -/
  | Leq
  /-- Greater than. Works on `Int` and `Real`. -/
  | Gt
  /-- Greater than or equal. Works on `Int` and `Real`. -/
  | Geq
  /-- String concatenation. -/
  | StrConcat
  deriving Repr

/--
A wrapper that pairs a value with source-level metadata such as source
locations and annotations. All Laurel AST nodes are wrapped in
`AstNode` so that error messages and verification conditions can
refer back to the original source.
-/
structure AstNode (t : Type) : Type where
  /-- The wrapped value. -/
  val : t
  /-- Source location for this AST node. -/
  source : Option FileRange
  /-- Source-level metadata (locations, annotations). -/
  md : MetaData := .empty
  deriving Repr

/--
The type system for Laurel programs.

`HighType` covers primitive types (`TVoid`, `TBool`, `TInt`, `TReal`, `TFloat64`,
`TString`), internal types used by the heap parameterization pass (`THeap`,
`TTypedField`), collection types (`TSet`), user-defined types (`UserDefined`),
generic applications (`Applied`), value types (`Pure`), and intersection types
(`Intersection`).
-/
inductive HighType : Type where
  /-- The void type, used for statements that produce no value. -/
  | TVoid
  /-- Boolean type. -/
  | TBool
  /-- Arbitrary-precision integer type. -/
  | TInt
  /-- 64-bit floating point type. Required for JavaScript (`number`), also used by Python (`float`) and Java (`double`). -/
  | TFloat64
  /-- Mathematical real type. Maps to Core's `real` type. -/
  | TReal
  /-- String type for text data. -/
  | TString
  /-- Internal type representing the heap. Introduced by the heap parameterization pass; not accessible via grammar. -/
  | THeap
  /-- Internal type for a field constant with a known value type. Introduced by the heap parameterization pass; not accessible via grammar. -/
  | TTypedField (valueType : AstNode HighType)
  /-- Set type, e.g. `Set int`. -/
  | TSet (elementType : AstNode HighType)
  /-- Map type. -/
  | TMap (keyType : AstNode HighType) (valueType : AstNode HighType)
  /-- A Identifier to a user-defined composite or constrained type by name. -/
  | UserDefined (name : Identifier)
  /-- A generic type application, e.g. `List<Int>`. -/
  | Applied (base : AstNode HighType) (typeArguments : List (AstNode HighType))
  /-- A pure (value) variant of a composite type that uses structural equality instead of reference equality. -/
  | Pure (base : AstNode HighType)
  /-- An intersection of types. Used for implicit intersection types, e.g. `Scientist & Scandinavian`. -/
  | Intersection (types : List (AstNode HighType))
  /-- Bitvector type of a given width. -/
  | TBv (size : Nat)
  /-- Temporary construct meant to aid the migration of Python->Core to Python->Laurel.
  Type "passed through" from Core. Intended to allow translations to Laurel to refer directly to Core. -/
  | TCore (s: String)
  /-- Type used internally by the Laurel compilation pipeline.
  This type is used when a resolution error occurs,
  to continue compilation without producing superfluous errors
  Any type can be assigned to unknown and unknown can be assigned to any type.
  The unknown type can not be represented in Core so its occurence will abort compilation before evaluating Core -/
  | Unknown
  deriving Repr

mutual

/--
A procedure in Laurel. Procedures are the main unit of specification and
verification. Unlike separate functions and methods, Laurel uses a single
general concept that covers both.
-/
structure Procedure : Type where
  /-- The procedure's name. -/
  name : Identifier
  /-- Input parameters with their types. -/
  inputs : List Parameter
  /-- Output parameters with their types. Multiple outputs are supported. -/
  outputs : List Parameter
  /-- The preconditions that callers must satisfy. -/
  preconditions : List Condition
  -- TODO: add back determinism together with an implementation
  /-- Optional termination measure for recursive procedures. -/
  decreases : Option (AstNode StmtExpr) -- optionally prove termination
  /-- If true, the body may only have functional constructs, so no destructive assignments or loops. -/
  isFunctional : Bool
  /-- The procedure body: transparent, opaque, or abstract. -/
  body : Body
  /-- Optional trigger for auto-invocation. When present, the translator also emits an axiom
      whose body is the ensures clause universally quantified over the procedure's inputs,
      with this expression as the SMT trigger. -/
  invokeOn : Option (AstNode StmtExpr) := none

/--
A typed parameter for a procedure.
-/
structure Parameter where
  /-- The parameter name. -/
  name : Identifier
  /-- The parameter type. -/
  type : AstNode HighType

/--
A condition with an optional human-readable summary.
Used for assertions, preconditions, and postconditions.
-/
structure Condition where
  /-- The boolean condition expression. -/
  condition : AstNode StmtExpr
  /-- Optional human-readable summary describing the property being checked. -/
  summary : Option String := none

/--
The body of a procedure. A body can be transparent (with a visible
implementation), opaque (with a postcondition and optional implementation),
or abstract (requiring overriding in extending types).
-/
inductive Body where
  /-- A transparent body whose implementation is visible to callers. -/
  | Transparent (body : AstNode StmtExpr)
  /-- An opaque body with a postcondition, optional implementation, and modifies clause. Without an implementation the postcondition is assumed. -/
  | Opaque
      (postconditions : List Condition)
      (implementation : Option (AstNode StmtExpr))
      (modifies : List (AstNode StmtExpr))
  /-- An abstract body that must be overridden in extending types. A type containing any members with abstract bodies cannot be instantiated. -/
  | Abstract (postconditions : List Condition)
  /-- An external body for procedures that are not translated to Core (e.g., built-in primitives). -/
  | External

/--
The unified statement-expression type for Laurel programs.

`StmtExpr` contains both statement-like constructs (conditionals, loops,
assignments, returns) and expression-like constructs (literals, identifiers,
operations, calls). Using a single type avoids duplication of shared concepts
such as conditionals and variable declarations.
-/
inductive StmtExpr : Type where
  /-- Conditional with a then-branch and optional else-branch. -/
  | IfThenElse (cond : AstNode StmtExpr) (thenBranch : AstNode StmtExpr) (elseBranch : Option (AstNode StmtExpr))
  /-- A sequence of statements with an optional label for `Exit`. -/
  | Block (statements : List (AstNode StmtExpr)) (label : Option String)
  /-- A local variable declaration with a type and optional initializer. The initializer must be set if this `StmtExpr` is pure. -/
  | LocalVariable (name : Identifier) (type : AstNode HighType) (initializer : Option (AstNode StmtExpr))
  /-- A while loop with a condition, invariants, optional termination measure, and body. Only allowed in impure contexts. -/
  | While (cond : AstNode StmtExpr) (invariants : List (AstNode StmtExpr))
    (decreases : Option (AstNode StmtExpr))
    (body : AstNode StmtExpr)
  /-- Exit a labelled block. Models `break` and `continue` statements. -/
  | Exit (target : String)
  /-- Return from the enclosing procedure with an optional value. -/
  | Return (value : Option (AstNode StmtExpr))
  /-- An integer literal. -/
  | LiteralInt (value : Int)
  /-- A boolean literal. -/
  | LiteralBool (value : Bool)
  /-- A string literal. -/
  | LiteralString (value : String)
  /-- A decimal literal. -/
  | LiteralDecimal (value : Decimal)
  /-- A variable reference by name. -/
  | Identifier (name : Identifier)
  /-- Assignment to one or more targets. Multiple targets are only allowed when the value is a `StaticCall` to a procedure with multiple outputs. -/
  | Assign (targets : List (AstNode StmtExpr)) (value : AstNode StmtExpr)
  /-- Read a field from a target expression. Combined with `Assign` for field writes. -/
  | FieldSelect (target : AstNode StmtExpr) (fieldName : Identifier)
  /-- Update a field on a pure (value) type, producing a new value. -/
  | PureFieldUpdate (target : AstNode StmtExpr) (fieldName : Identifier) (newValue : AstNode StmtExpr)
  /-- Call a static procedure by name with the given arguments. -/
  | StaticCall (callee : Identifier) (arguments : List (AstNode StmtExpr))
  /-- Apply a primitive operation to the given arguments. -/
  | PrimitiveOp (operator : Operation) (arguments : List (AstNode StmtExpr))
  /-- Create new object (`new`). -/
  | New (ref : Identifier)
  /-- Identifier to the current object (`this`/`self`). -/
  | This
  /-- Reference equality test between two expressions. -/
  | ReferenceEquals (lhs : AstNode StmtExpr) (rhs : AstNode StmtExpr)
  /-- Type cast: treat the target as the given type. -/
  | AsType (target : AstNode StmtExpr) (targetType : AstNode HighType)
  /-- Type test: check whether the target is an instance of the given type. -/
  | IsType (target : AstNode StmtExpr) (type : AstNode HighType)
  /-- Call an instance method on a target object. -/
  | InstanceCall (target : AstNode StmtExpr) (callee : Identifier) (arguments : List (AstNode StmtExpr))
  /-- Universal quantification over a typed parameter with an optional trigger. -/
  | Forall (param : Parameter) (trigger : Option (AstNode StmtExpr)) (body : AstNode StmtExpr)
  /-- Existential quantification over a typed parameter with an optional trigger. -/
  | Exists (param : Parameter) (trigger : Option (AstNode StmtExpr)) (body : AstNode StmtExpr)
  /-- Check whether a variable has been assigned. -/
  | Assigned (name : AstNode StmtExpr)
  /-- Refer to the pre-state value of an expression in a postcondition. -/
  | Old (value : AstNode StmtExpr)
  /-- Check whether a reference is freshly allocated. May only target impure composite types. -/
  | Fresh (value : AstNode StmtExpr)
  /-- Assert a condition, generating a proof obligation. -/
  | Assert (condition : Condition)
  /-- Assume a condition, restricting the state space. -/
  | Assume (condition : AstNode StmtExpr)
  /-- Attach a proof hint to a value. The semantics are those of `value`, but `proof` helps discharge assertions in `value`. -/
  | ProveBy (value : AstNode StmtExpr) (proof : AstNode StmtExpr)
  /-- Extract the contract (reads, modifies, precondition, or postcondition) of a function. -/
  | ContractOf (type : ContractType) (function : AstNode StmtExpr)
  /-- Marker for abstract contracts. Makes the containing type abstract. -/
  | Abstract
  /-- Refers to all objects in the heap. Used in reads or modifies clauses. -/
  | All
  /-- A hole representing an unknown expression.
      - `deterministic`: if true, the hole represents a deterministic unknown
        (translated as an uninterpreted function); if false, a nondeterministic
        unknown (translated as a havoced variable). Nondeterministic holes are
        not allowed in functions.
      - `type`: inferred by the hole type inference pass; `none` means not yet inferred. -/
  | Hole (deterministic : Bool := true) (type : Option (AstNode HighType) := none)

inductive ContractType where
  | Reads | Modifies | Precondition | PostCondition
end

@[expose] abbrev HighTypeMd := AstNode HighType
@[expose] abbrev StmtExprMd := AstNode StmtExpr

theorem AstNode.sizeOf_val_lt {t : Type} [SizeOf t] (e : AstNode t) : sizeOf e.val < sizeOf e := by
  cases e; grind

theorem Condition.sizeOf_condition_lt (c : Condition) : sizeOf c.condition < 1 + sizeOf c := by
  cases c; grind

/-- Apply a monadic transformation to the condition expression, preserving the summary. -/
def Condition.mapM [Monad m] (f : AstNode StmtExpr → m (AstNode StmtExpr)) (c : Condition) : m Condition :=
  return { c with condition := ← f c.condition }

/-- Apply a pure transformation to the condition expression, preserving the summary. -/
def Condition.mapCondition (f : AstNode StmtExpr → AstNode StmtExpr) (c : Condition) : Condition :=
  { c with condition := f c.condition }

/-- Build Core metadata from an optional source location and Laurel metadata. -/
def fileRangeToCoreMd (source : Option FileRange) (md : Imperative.MetaData Core.Expression) : Imperative.MetaData Core.Expression :=
  match source with
  | some fr => md.pushElem Imperative.MetaData.fileRange (.fileRange fr)
  | none => md

/-- Build Core metadata from an AstNode's source location and any extra metadata. -/
def astNodeToCoreMd (node : AstNode α) : Imperative.MetaData Core.Expression :=
  fileRangeToCoreMd node.source node.md

instance : Inhabited StmtExpr where
  default := .Hole

instance : Inhabited HighTypeMd where
  default := { val := HighType.Unknown, source := none }

instance : Inhabited StmtExprMd where
  default := { val := default, source := none }

def highEq (a : HighTypeMd) (b : HighTypeMd) : Bool := match _a: a.val, _b: b.val with
  | HighType.TVoid, HighType.TVoid => true
  | HighType.TBool, HighType.TBool => true
  | HighType.TInt, HighType.TInt => true
  | HighType.TFloat64, HighType.TFloat64 => true
  | HighType.TReal, HighType.TReal => true
  | HighType.TString, HighType.TString => true
  | HighType.THeap, HighType.THeap => true
  | HighType.TBv n1, HighType.TBv n2 => n1 == n2
  | HighType.TTypedField t1, HighType.TTypedField t2 => highEq t1 t2
  | HighType.TSet t1, HighType.TSet t2 => highEq t1 t2
  | HighType.TMap k1 v1, HighType.TMap k2 v2 => highEq k1 k2 && highEq v1 v2
  | HighType.UserDefined r1, HighType.UserDefined r2 => r1.text == r2.text
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.attach.zip args2 |>.all (fun (a1, a2) => highEq a1.1 a2))
  | HighType.Pure b1, HighType.Pure b2 => highEq b1 b2
  | HighType.Intersection ts1, HighType.Intersection ts2 =>
      ts1.length == ts2.length && (ts1.attach.zip ts2 |>.all (fun (t1, t2) => highEq t1.1 t2))
  | HighType.Unknown, HighType.Unknown => true
  | _, _ => false
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    . cases a1; term_by_mem
    . cases t1; term_by_mem

instance : BEq HighTypeMd where
  beq := highEq

deriving instance BEq for HighType

def HighType.isBool : HighType → Bool
  | TBool => true
  | _ => false

def Body.isExternal : Body → Bool
  | .External => true
  | _ => false

def Body.isTransparent : Body → Bool
  | .Transparent _ => true
  | _ => false

def HighTypeMd.isBool (t : HighTypeMd) : Bool := t.val.isBool

/--
A field in a composite type. Fields declare their name, mutability, and type.
Mutability affects what permissions are needed to access the field.
-/
structure Field where
  /-- The field name. -/
  name : Identifier
  /-- Whether the field is mutable. Mutable fields require write permission. -/
  isMutable : Bool
  /-- The field's type. -/
  type : HighTypeMd

/--
A composite defines a type with fields and instance procedures.

Composite types may extend other composite types, forming a type hierarchy
that affects the results of `IsType` and `AsType` operations.
-/
structure CompositeType where
  /-- The type name. -/
  name : Identifier
  /-- Names of composite types this type extends. The type hierarchy affects `IsType` and `AsType` results. -/
  extending : List Identifier
  /-- The fields of this type. -/
  fields : List Field
  /-- Instance procedures (methods) defined on this type. -/
  instanceProcedures : List Procedure
  deriving Inhabited

/--
A constrained (refinement) type defined by a base type and a predicate.

Algebraic datatypes can be encoded using composite and constrained types.
For example, `Option<T>` can be defined as a constrained type over `Dynamic`
with the constraint `value is Some<T> || value is Unit`.
-/
structure ConstrainedType where
  /-- The constrained type's name. -/
  name : Identifier
  /-- The base type being refined. -/
  base : HighTypeMd
  /-- The name bound to the value in the constraint expression. -/
  valueName : Identifier
  /-- The predicate that values of this type must satisfy. -/
  constraint : StmtExprMd
  /-- A witness value proving the type is inhabited. -/
  witness : StmtExprMd

/-- A constructor of a Laurel datatype, with a name and typed arguments. -/
structure DatatypeConstructor where
  name : Identifier
  args : List Parameter

/-- A Laurel datatype definition with optional type parameters.
    Zero constructors produces an opaque (abstract) type in Core.

    The use-case of this type is to enable incremental translation to Core.
    Core features datatypes and having these in Laurel allows Laurel->Laurel passes
    to already translate to datatypes.
     -/
structure DatatypeDefinition where
  name : Identifier
  typeArgs : List Identifier
  constructors : List DatatypeConstructor

/-- Canonical resolution name for the tester of constructor `ctor` in this datatype.
    Matches the override name used by `Resolution.resolveTypeDefinition`. -/
def DatatypeDefinition.testerName (dt : DatatypeDefinition) (ctor : DatatypeConstructor) : String :=
  s!"{dt.name}..is{ctor.name}"

/-- Canonical resolution name for the destructor of field `field` in this datatype. -/
def DatatypeDefinition.destructorName (dt : DatatypeDefinition) (field : Parameter) : String :=
  s!"{dt.name.text}..{field.name.text}"

/-- Canonical resolution name for the unsafe (bang) destructor of field `field`. -/
def DatatypeDefinition.unsafeDestructorName (dt : DatatypeDefinition) (field : Parameter) : String :=
  s!"{dt.name.text}..{field.name.text}!"

/-- A type alias, mapping a name to an existing type. Eliminated by the
    `TypeAliasElim` pass after the first resolution. -/
structure TypeAlias where
  name : Identifier
  target : HighTypeMd
  deriving Repr

/--
A user-defined type, either a composite type, a constrained type, an algebraic datatype,
or a type alias.

Algebriac datatypes can also be encoded uses composite and constrained types. Here are two examples:

Example 1:
`composite Some<T> { value: T }`
`constrained Option<T> = value: Dynamic | value is Some<T> || value is Unit`

Example 2:
`composite Cons<T> { head: T, tail: List<T> }`
`constrained List<T> = value: Dynamic | value is Cons<T> || value is Unit`
-/
inductive TypeDefinition where
  /-- A composite (class-like) type with fields and methods. -/
  | Composite (ty : CompositeType)
  /-- A constrained (refinement) type with a base type and predicate. -/
  | Constrained (ty : ConstrainedType)
  /-- An algebriac datatype. -/
  | Datatype (ty : DatatypeDefinition)
  /-- A type alias (e.g. `MyInt = int`). Eliminated before Core translation. -/
  | Alias (ty : TypeAlias)
  deriving Inhabited

def TypeDefinition.name : TypeDefinition → Identifier
  | .Composite ty => ty.name
  | .Constrained ty => ty.name
  | .Datatype ty => ty.name
  | .Alias ty => ty.name

structure Constant where
  name : Identifier
  type : HighTypeMd
  initializer : Option StmtExprMd := none

/--
A Laurel program consisting of static procedures, static fields, type
definitions, and constants.
-/
structure Program where
  /-- Top-level procedures not attached to any type. -/
  staticProcedures : List Procedure
  /-- Top-level fields (global variables). -/
  staticFields : List Field
  /-- User-defined type definitions (composite and constrained). -/
  types : List TypeDefinition
  /-- Named constants. -/
  constants : List Constant := []
  deriving Inhabited

end
