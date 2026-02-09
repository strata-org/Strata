/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.MetaData
import Strata.Languages.Core.Expressions
import Strata.Languages.Core.Procedure

/-
The Laurel language is supposed to serve as an intermediate verification language for at least Java, Python, JavaScript.

It enables doing various forms of verification:
- Deductive verification
- Property based testing
- Data-flow analysis

Features currently not present:
- Type inference. The source program needs to specify enough types so that no inference is needed.
- Type checking. We assume types have already been checked before.
- Namespaces. All definition and reference names consist of a single Identifier

Design choices:
- Pure contracts: contracts may only contain pure code. Pure code does not modify the heap, neither by modifying existing objects are creating new ones.
- Procedures: instead of functions and methods we have a single more general concept called a 'procedure'.
- Determinism: procedures can be marked as deterministic or not. For deterministic procedures with a non-empty reads clause, we can assume the result is unchanged if the read references are the same.
- Opacity: procedures can have a body that's transparant or opaque. Only an opaque body may declare a postcondition.
- StmtExpr: Statements and expressions are part of the same type. This reduces duplication since the same concepts are needed in both, such as conditions and variable declarations.
- Loops: The only loop is a while, but this can be used to compile do-while and for loops to as well.
- Jumps: Instead of break and continue statements, there is a labelled block that can be exited from using an exit statement inside of it.
  This can be used to model break statements and continue statements for both while and for loops.

- User defined types consist of two categories: composite types and constrained types.
- Composite types have fields and procedures, and may extend other composite types.
  - Fields state whether they are mutable, which impacts what permissions are needed to access them
  - Fields state their type, which is needed to know the resulting type when reading a field.
- Constrained types are defined by a base type and a constraint over that type.
  - Algebraic datatypes do not exist directly but can be encoded using composite and constrained types.

- For now there is no type polymorphism

- Construction of composite types is WIP. It needs a design first.

-/
namespace Strata
namespace Laurel

abbrev Identifier := String /- Potentially this could be an Int to save resources. -/

inductive Operation: Type where
  /- Works on Bool -/
    /- Equality on composite types uses reference equality for impure types, and structural equality for pure ones -/
  | Eq | Neq
  | And | Or | Not
  /- Works on Int/Float64 -/
  | Neg | Add | Sub | Mul | Div | Mod
  | Lt | Leq | Gt | Geq
  deriving Repr

-- Explicit instance needed for deriving Repr in the mutual block
instance : Repr (Imperative.MetaData Core.Expression) := inferInstance


mutual
/-- A wrapper that adds metadata to any type -/
structure HighTypeMd where
  val : HighType
  md : Imperative.MetaData Core.Expression
  deriving Repr

/-- A wrapper that adds metadata to any type -/
structure StmtExprMd where
  val : StmtExpr
  md : Imperative.MetaData Core.Expression
  deriving Repr

structure Procedure: Type where
  name : Identifier
  inputs : List Parameter
  outputs : List Parameter
  precondition : StmtExprMd
  determinism : Determinism
  decreases : Option StmtExprMd -- optionally prove termination
  body : Body

inductive Determinism where
  | deterministic (reads: Option StmtExprMd)
  | nondeterministic

structure Parameter where
  name : Identifier
  type : HighTypeMd

inductive HighType : Type where
  | TVoid
  | TBool
  | TInt
  | TFloat64 /- Required for JavaScript (number). Used by Python (float) and Java (double) as well -/
  | THeap /- Internal type for heap parameterization pass. Not accessible via grammar. -/
  | TTypedField (valueType : HighTypeMd) /- Field constant with known value type. Not accessible via grammar. -/
  | UserDefined (name: Identifier)
  | Applied (base : HighTypeMd) (typeArguments : List HighTypeMd)
  /- Pure represents a composite type that does not support reference equality -/
  | Pure(base: HighTypeMd)
  /- Java has implicit intersection types.
     Example: `<cond> ? RustanLeino : AndersHejlsberg` could be typed as `Scientist & Scandinavian`-/
  | Intersection (types : List HighTypeMd)
  deriving Repr

/- No support for something like function-by-method yet -/
inductive Body where
  | Transparent (body : StmtExprMd)
/- Without an implementation, the postcondition is assumed -/
  | Opaque (postcondition : StmtExprMd) (implementation : Option StmtExprMd) (modifies : Option StmtExprMd)
/- An abstract body is useful for types that are extending.
    A type containing any members with abstract bodies can not be instantiated. -/
  | Abstract (postcondition : StmtExprMd)

/-
A StmtExpr contains both constructs that we typically find in statements and those in expressions.
By using a single datatype we prevent duplication of constructs that can be used in both contexts,
such a conditionals and variable declarations
-/
/-
It would be nice to replace `Type` on the next line with `(isPure: Bool) -> Type`,
so that we can prevent certain constructors from being used for pure StmtExpr's,
but when trying that Lean complained about parameters being used in a nested inductive,
for example in `Option (StmtExpr isPure)`
-/
inductive StmtExpr : Type where
/- Statement like -/
  | IfThenElse (cond : StmtExprMd) (thenBranch : StmtExprMd) (elseBranch : Option StmtExprMd)
  | Block (statements : List StmtExprMd) (label : Option Identifier)
  /- The initializer must be set if this StmtExpr is pure -/
  | LocalVariable (name : Identifier) (type : HighTypeMd) (initializer : Option StmtExprMd)
  /- While is only allowed in an impure context
    The invariant and decreases are always pure
  -/
  | While (cond : StmtExprMd) (invariant : Option StmtExprMd) (decreases: Option StmtExpr) (body : StmtExprMd)
  | Exit (target: Identifier)
  | Return (value : Option StmtExprMd)
/- Expression like -/
  | LiteralInt (value: Int)
  | LiteralBool (value: Bool)
  | Identifier (name : Identifier)
  /- For single target assignments, use a single-element list.
     Multiple targets are only allowed when the value is a StaticCall to a procedure
     with multiple outputs, and the number of targets must match the number of outputs. -/
  | Assign (targets : List StmtExprMd) (value : StmtExprMd)
  /- Used by itself for fields reads and in combination with Assign for field writes -/
  | FieldSelect (target : StmtExprMd) (fieldName : Identifier)
  /- PureFieldUpdate is the only way to assign values to fields of pure types -/
  | PureFieldUpdate (target : StmtExprMd) (fieldName : Identifier) (newValue : StmtExprMd)
  | StaticCall (callee : Identifier) (arguments : List StmtExprMd)
  | PrimitiveOp (operator: Operation) (arguments : List StmtExprMd)
/- Instance related -/
  | This
  | ReferenceEquals (lhs: StmtExprMd) (rhs: StmtExprMd)
  | AsType (target: StmtExprMd) (targetType: HighTypeMd)
  | IsType (target : StmtExprMd) (type: HighTypeMd)
  | InstanceCall (target : StmtExprMd) (callee : Identifier) (arguments : List StmtExprMd)

/- Verification specific -/
  | Forall (name: Identifier) (type: HighTypeMd) (body: StmtExprMd)
  | Exists (name: Identifier) (type: HighTypeMd) (body: StmtExprMd)
  | Assigned (name : StmtExprMd)
  | Old (value : StmtExprMd)
  /- Fresh may only target impure composite types -/
  | Fresh(value : StmtExprMd)

/- Related to proofs -/
  | Assert (condition: StmtExprMd)
  | Assume (condition: StmtExprMd)
  /-
ProveBy allows writing proof trees. Its semantics are the same as that of the given `value`,
but the `proof` is used to help prove any assertions in `value`.
Example:
ProveBy(
  someCall(arg1, arg2),
  ProveBy(
    aLemmaToHelpProveThePreconditionOfTheCall(),
    anotherLemmaToProveThePreconditionOfTheFirstLemma()
  )
)
-/
  | ProveBy (value: StmtExprMd) (proof: StmtExprMd)

-- ContractOf allows extracting the contract of a function
  | ContractOf (type: ContractType) (function: StmtExprMd)
/-
Abstract can be used as the root expr in a contract for reads/modifies/precondition/postcondition. For example: `reads(abstract)`
It can only be used for instance procedures and it makes the containing type abstract, meaning it can not be instantiated.
An extending type can become concrete by redefining all procedures that had abstract contracts and providing non-abstract contracts.
-/
  | Abstract
  | All -- All refers to all objects in the heap. Can be used in a reads or modifies clause
/- Hole has a dynamic type and is useful when programs are only partially available -/
  | Hole

inductive ContractType where
  | Reads | Modifies | Precondition | PostCondition
end

instance : Inhabited StmtExpr where
  default := .Hole

partial def highEq (a: HighTypeMd) (b: HighTypeMd) : Bool := match a.val, b.val with
  | HighType.TVoid, HighType.TVoid => true
  | HighType.TBool, HighType.TBool => true
  | HighType.TInt, HighType.TInt => true
  | HighType.TFloat64, HighType.TFloat64 => true
  | HighType.THeap, HighType.THeap => true
  | HighType.TTypedField t1, HighType.TTypedField t2 => highEq t1 t2
  | HighType.UserDefined n1, HighType.UserDefined n2 => n1 == n2
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.zip args2 |>.all (fun (a1, a2) => highEq a1 a2))
  | HighType.Pure b1, HighType.Pure b2 => highEq b1 b2
  | HighType.Intersection ts1, HighType.Intersection ts2 =>
      ts1.length == ts2.length && (ts1.zip ts2 |>.all (fun (t1, t2) => highEq t1 t2))
  | _, _ => false

instance : BEq HighTypeMd where
  beq := highEq

def HighType.isBool : HighType → Bool
  | TBool => true
  | _ => false

def HighTypeMd.isBool (t : HighTypeMd) : Bool := t.val.isBool

structure Field where
  name : Identifier
  isMutable : Bool
  type : HighTypeMd

structure CompositeType where
  name : Identifier
  /-
  The type hierarchy affects the results of IsType and AsType,
  and can add checks to the postcondition of procedures that extend another one
  -/
  extending : List Identifier
  fields : List Field
  instanceProcedures : List Procedure

structure ConstrainedType where
  name : Identifier
  base : HighTypeMd
  valueName : Identifier
  constraint : StmtExprMd
  witness : StmtExprMd

/-
Note that there are no explicit 'inductive datatypes'. Typed unions are created by
creating a CompositeType for each constructor, and a ConstrainedType for their union.

Example 1:
`composite SomeT> { value: T }`
`constrained Option<T> = value: Dynamic | value is Some<T> || value is Unit`

Example 2:
`composite Cons<T> { head: T, tail: List<T> }`
`constrained List<T> = value: Dynamic | value is Cons<T> || value is Unit`
 -/
inductive TypeDefinition where
  | Composite (ty : CompositeType)
  | Constrained (ty : ConstrainedType)

structure Constant where
  name : Identifier
  type : HighTypeMd

structure Program where
  staticProcedures : List Procedure
  staticFields : List Field
  types : List TypeDefinition
  constants : List Constant := []
