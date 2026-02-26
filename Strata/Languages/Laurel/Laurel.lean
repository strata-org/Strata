/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.MetaData
import Strata.Languages.Core.Expressions
import Strata.Languages.Core.Procedure
import Strata.Util.Tactics

/-
Documentation for Laurel can be found in docs/verso/LaurelDoc.lean
-/
namespace Strata
namespace Laurel

abbrev Identifier := String /- Potentially this could be an Int to save resources. -/

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
  /-- Logical conjunction. -/
  | And
  /-- Logical disjunction. -/
  | Or
  /-- Logical negation. -/
  | Not
  /-- Logical implication. -/
  | Implies
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
  /-- Less than. Works on `Int` and `Float64`. -/
  | Lt
  /-- Less than or equal. Works on `Int` and `Float64`. -/
  | Leq
  /-- Greater than. Works on `Int` and `Float64`. -/
  | Gt
  /-- Greater than or equal. Works on `Int` and `Float64`. -/
  | Geq
  /-- String concatenation. -/
  | StrConcat
  deriving Repr

/--
A wrapper that pairs a value with source-level metadata such as source
locations and annotations. All Laurel AST nodes are wrapped in
`WithMetadata` so that error messages and verification conditions can
refer back to the original source.
-/
structure WithMetadata (t : Type) : Type where
  /-- The wrapped value. -/
  val : t
  /-- Source-level metadata (locations, annotations). -/
  md : Imperative.MetaData Core.Expression

/--
The type system for Laurel programs.

`HighType` covers primitive types (`TVoid`, `TBool`, `TInt`, `TFloat64`,
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
  /-- String type for text data. -/
  | TString
  /-- Internal type representing the heap. Introduced by the heap parameterization pass; not accessible via grammar. -/
  | THeap
  /-- Internal type for a field constant with a known value type. Introduced by the heap parameterization pass; not accessible via grammar. -/
  | TTypedField (valueType : WithMetadata HighType)
  /-- Set type, e.g. `Set int`. -/
  | TSet (elementType : WithMetadata HighType)
  /-- Map type. -/
  | TMap (keyType : WithMetadata HighType) (valueType : WithMetadata HighType)
  /-- A reference to a user-defined composite or constrained type by name. -/
  | UserDefined (name : Identifier)
  /-- A generic type application, e.g. `List<Int>`. -/
  | Applied (base : WithMetadata HighType) (typeArguments : List (WithMetadata HighType))
  /-- A pure (value) variant of a composite type that uses structural equality instead of reference equality. -/
  | Pure (base : WithMetadata HighType)
  /-- An intersection of types. Used for implicit intersection types, e.g. `Scientist & Scandinavian`. -/
  | Intersection (types : List (WithMetadata HighType))
  /-- Temporary construct meant to aid the migration of Python->Core to Python->Laurel.
  Type "passed through" from Core. Intended to allow translations to Laurel to refer directly to Core. -/
  | TCore (s: String)

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
  /-- The precondition that callers must satisfy. -/
  precondition : WithMetadata StmtExpr
  /-- Whether the procedure is deterministic or nondeterministic. -/
  determinism : Determinism
  /-- Optional termination measure for recursive procedures. -/
  decreases : Option (WithMetadata StmtExpr) -- optionally prove termination
  /-- The procedure body: transparent, opaque, or abstract. -/
  body : Body
  /-- Source-level metadata. -/
  md : Imperative.MetaData Core.Expression

/--
Specifies whether a procedure is deterministic or nondeterministic.

For deterministic procedures with a non-empty reads clause, the result can be
assumed unchanged if the read references are the same.
-/
inductive Determinism where
  /-- A deterministic procedure. The optional reads clause lists the heap locations the procedure may read. -/
  | deterministic (reads : Option (WithMetadata StmtExpr))
  /-- A nondeterministic procedure. They can read from the heap but there is no benefit from specifying a reads clause. -/
  | nondeterministic

/--
A typed parameter for a procedure.
-/
structure Parameter where
  /-- The parameter name. -/
  name : Identifier
  /-- The parameter type. -/
  type : WithMetadata HighType

/--
The body of a procedure. A body can be transparent (with a visible
implementation), opaque (with a postcondition and optional implementation),
or abstract (requiring overriding in extending types).
-/
inductive Body where
  /-- A transparent body whose implementation is visible to callers. -/
  | Transparent (body : WithMetadata StmtExpr)
  /-- An opaque body with a postcondition, optional implementation, and modifies clause. Without an implementation the postcondition is assumed. -/
  | Opaque
      (postcondition : List (WithMetadata StmtExpr))
      (implementation : Option (WithMetadata StmtExpr))
      (modifies : List (WithMetadata StmtExpr))
  /-- An abstract body that must be overridden in extending types. A type containing any members with abstract bodies cannot be instantiated. -/
  | Abstract (postcondition : WithMetadata StmtExpr)

/--
The unified statement-expression type for Laurel programs.

`StmtExpr` contains both statement-like constructs (conditionals, loops,
assignments, returns) and expression-like constructs (literals, identifiers,
operations, calls). Using a single type avoids duplication of shared concepts
such as conditionals and variable declarations.
-/
inductive StmtExpr : Type where
  /-- Conditional with a then-branch and optional else-branch. -/
  | IfThenElse (cond : WithMetadata StmtExpr) (thenBranch : WithMetadata StmtExpr) (elseBranch : Option (WithMetadata StmtExpr))
  /-- A sequence of statements with an optional label for `Exit`. -/
  | Block (statements : List (WithMetadata StmtExpr)) (label : Option Identifier)
  /-- A local variable declaration with a type and optional initializer. The initializer must be set if this `StmtExpr` is pure. -/
  | LocalVariable (name : Identifier) (type : WithMetadata HighType) (initializer : Option (WithMetadata StmtExpr))
  /-- A while loop with a condition, invariants, optional termination measure, and body. Only allowed in impure contexts. -/
  | While (cond : WithMetadata StmtExpr) (invariants : List (WithMetadata StmtExpr))
    (decreases : Option (WithMetadata StmtExpr))
    (body : WithMetadata StmtExpr)
  /-- Exit a labelled block. Models `break` and `continue` statements. -/
  | Exit (target : Identifier)
  /-- Return from the enclosing procedure with an optional value. -/
  | Return (value : Option (WithMetadata StmtExpr))
  /-- An integer literal. -/
  | LiteralInt (value : Int)
  /-- A boolean literal. -/
  | LiteralBool (value : Bool)
  /-- A string literal. -/
  | LiteralString (value : String)
  /-- A variable reference by name. -/
  | Identifier (name : Identifier)
  /-- Assignment to one or more targets. Multiple targets are only allowed when the value is a `StaticCall` to a procedure with multiple outputs. -/
  | Assign (targets : List (WithMetadata StmtExpr)) (value : WithMetadata StmtExpr)
  /-- Read a field from a target expression. Combined with `Assign` for field writes. -/
  | FieldSelect (target : WithMetadata StmtExpr) (fieldName : Identifier)
  /-- Update a field on a pure (value) type, producing a new value. -/
  | PureFieldUpdate (target : WithMetadata StmtExpr) (fieldName : Identifier) (newValue : WithMetadata StmtExpr)
  /-- Call a static procedure by name with the given arguments. -/
  | StaticCall (callee : Identifier) (arguments : List (WithMetadata StmtExpr))
  /-- Apply a primitive operation to the given arguments. -/
  | PrimitiveOp (operator : Operation) (arguments : List (WithMetadata StmtExpr))
  /-- Create new object (`new`). -/
  | New (name: Identifier)
  /-- Reference to the current object (`this`/`self`). -/
  | This
  /-- Reference equality test between two expressions. -/
  | ReferenceEquals (lhs : WithMetadata StmtExpr) (rhs : WithMetadata StmtExpr)
  /-- Type cast: treat the target as the given type. -/
  | AsType (target : WithMetadata StmtExpr) (targetType : WithMetadata HighType)
  /-- Type test: check whether the target is an instance of the given type. -/
  | IsType (target : WithMetadata StmtExpr) (type : WithMetadata HighType)
  /-- Call an instance method on a target object. -/
  | InstanceCall (target : WithMetadata StmtExpr) (callee : Identifier) (arguments : List (WithMetadata StmtExpr))
  /-- Universal quantification over a typed variable. -/
  | Forall (name : Identifier) (type : WithMetadata HighType) (body : WithMetadata StmtExpr)
  /-- Existential quantification over a typed variable. -/
  | Exists (name : Identifier) (type : WithMetadata HighType) (body : WithMetadata StmtExpr)
  /-- Check whether a variable has been assigned. -/
  | Assigned (name : WithMetadata StmtExpr)
  /-- Refer to the pre-state value of an expression in a postcondition. -/
  | Old (value : WithMetadata StmtExpr)
  /-- Check whether a reference is freshly allocated. May only target impure composite types. -/
  | Fresh (value : WithMetadata StmtExpr)
  /-- Assert a condition, generating a proof obligation. -/
  | Assert (condition : WithMetadata StmtExpr)
  /-- Assume a condition, restricting the state space. -/
  | Assume (condition : WithMetadata StmtExpr)
  /-- Attach a proof hint to a value. The semantics are those of `value`, but `proof` helps discharge assertions in `value`. -/
  | ProveBy (value : WithMetadata StmtExpr) (proof : WithMetadata StmtExpr)
  /-- Extract the contract (reads, modifies, precondition, or postcondition) of a function. -/
  | ContractOf (type : ContractType) (function : WithMetadata StmtExpr)
  /-- Marker for abstract contracts. Makes the containing type abstract. -/
  | Abstract
  /-- Refers to all objects in the heap. Used in reads or modifies clauses. -/
  | All
  /-- A hole with dynamic type, useful for partially available programs. -/
  | Hole

inductive ContractType where
  | Reads | Modifies | Precondition | PostCondition
end

abbrev HighTypeMd := WithMetadata HighType
abbrev StmtExprMd := WithMetadata StmtExpr

theorem WithMetadata.sizeOf_val_lt {t : Type} [SizeOf t] (e : WithMetadata t) : sizeOf e.val < sizeOf e := by
  cases e; grind

instance : Inhabited StmtExpr where
  default := .Hole

instance : Inhabited StmtExprMd where
  default := ⟨ .Hole, .empty ⟩

instance : Inhabited HighTypeMd where
  default := { val := HighType.TVoid, md := default }

instance : Inhabited StmtExprMd where
  default := { val := default, md := default }

def highEq (a : HighTypeMd) (b : HighTypeMd) : Bool := match _a: a.val, _b: b.val with
  | HighType.TVoid, HighType.TVoid => true
  | HighType.TBool, HighType.TBool => true
  | HighType.TInt, HighType.TInt => true
  | HighType.TFloat64, HighType.TFloat64 => true
  | HighType.TString, HighType.TString => true
  | HighType.THeap, HighType.THeap => true
  | HighType.TTypedField t1, HighType.TTypedField t2 => highEq t1 t2
  | HighType.TSet t1, HighType.TSet t2 => highEq t1 t2
  | HighType.TMap k1 v1, HighType.TMap k2 v2 => highEq k1 k2 && highEq v1 v2
  | HighType.UserDefined n1, HighType.UserDefined n2 => n1 == n2
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.attach.zip args2 |>.all (fun (a1, a2) => highEq a1.1 a2))
  | HighType.Pure b1, HighType.Pure b2 => highEq b1 b2
  | HighType.Intersection ts1, HighType.Intersection ts2 =>
      ts1.length == ts2.length && (ts1.attach.zip ts2 |>.all (fun (t1, t2) => highEq t1.1 t2))
  | _, _ => false
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    . cases a1; term_by_mem
    . cases t1; term_by_mem

instance : BEq HighTypeMd where
  beq := highEq


def HighType.isBool : HighType → Bool
  | TBool => true
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
  args : List (Identifier × HighTypeMd)

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

/--
A user-defined type, either a composite type, a constrained type, or an algebraic datatype.

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
