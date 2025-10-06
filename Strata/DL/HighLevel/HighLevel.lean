/-
The high strata language is supposed to serve as an intermediate verification language for at least Java, Python, JavaScript.

It enables doing various forms of verification:
- Deductive verification
- Property based testing
- Data-flow analysis

Design choices:
- Contracts may only contain pure code. Pure code does not modify the heap, neither by modifying existing objects are creating new ones.
- Naming wise: instead of functions/methods/procudures we have callables.
  They can be mathematical like functions or associated with a type like methods, but they do not have to be.
- Statements and expressions are part of the same type
- User defined types consist of two categories: composite types and constrained types.
  - Composite types have fields and callables, and may extend other composite types.
  - Constrained types are defined by a base type and a constraint over that type.
  - Algebriac datatypes do not exist directly but can be encoded using composited and constrained types.
- The base type for all Composite types is Dynamic, which is a type that can be type tested.
  A type that is not Dynamic, such as a primitive can be autoamatically casted to Dynamic.
  It can be casted back to its original type using a type test.
  This works well for languages such as JavaScript.
- There is no match-case construct, but there are type tests with pattern matching that enable the same functionality but more generally.
- There is no concept of constructors, but there is a partial type that represents an object whose fields
  are not yet assigned and whose type invariants might not hold.
  A partial type can be completed to a full type once all fields are assigned and the type invariants are known to hold.
- There is no concept of namespaces so all references need to be fully qualified.
- Callables can have opaque or transparant bodies, but only the opaque ones may have a postcondition.
-/

structure Program where
  staticCallables : List Callable
  types : List TypeDefinition

abbrev Identifier := String /- Potentially this could be an Int to save resources. -/

mutual
structure Callable: Type where
  name : Identifier
  typeParameters : List TypeParameter
  inputs : List Parameter
  output : HighType
  precondition : StmtExpr
  decreases : StmtExpr
  reads : StmtExpr
  purity : Purity
  body : Body

inductive Purity where
  | Pure
  | Impure (modifies : Expression)

structure Parameter where
  name : Identifier
  type : HighType

inductive HighType : Type where
  | Void
  | Bool
  | Int
  | Real
  | Float64 /- Required for JavaScript (number). Used by Python (float) and Java (double) as well -/
  /- A value of type `Dynamic` is a tuple consisting of a type and an expression.
     Values are automatically casted to and from `Dynamic`
     Example: `var x: Dynamic = 3; return x is Int` returns `True`
   -/
  | Dynamic
  | UserDefined (name: Identifier)
  | Applied (base : TypeBase) (typeArguments : List HighType)
  /- Partial represents a composite type with unassigned fields and whose type invariants might not hold.
     Can be represented as a Map that contains a subset of the fields of the composite type -/
  | Partial (base : TypeBase)
  /- A nullable type is implicitly cast to its base when required,
    such as in a member access or when assigned to a variable of the base type -/
  | Nullable (base : TypeBase)
  /- Java has implicit intersection types.
     Example: `<cond> ? RustanLeino : AndersHejlsberg` could be typed `Scientist & Scandinavian`-/
  | Intersection (types : List HighType)
  | Union (types : List HighType) /- I'm not sure we need Union. Seems like it could be replaced by predicate types -/

structure TypeParameter where
  name : Identifier
  bounds : List HighType /- Java has bounded type parameters -/

/- No support for something like function-by-method yet -/
inductive Body where
  | Transparent (body : StmtExpr)
/- Without an implementation, the postcondition is assumed -/
  | Opaque (postcondition : StmtExpr) (implementation : Option StmtExpr)
/- An abstract body is useful for types that are extending.
    A type containing any members with abstract bodies can not be instantiated. -/
  | Abstract (postcondition : StmtExpr)

/- We will support these operations for dynamic types as well -/
/- The 'truthy' concept from JavaScript should be implemented using a library function -/
inductive Operation: Type where
  /- Works on Bool -/
    /- Equality on composite types uses reference equality for impure types, and structural equality for pure ones -/
  | Eq | Neq
  | And | Or | Not
  /- Works on Int/Real/Float64 -/
  | Neg | Add | Sub | Mul | Div | Mod
  | Lt | Leq | Gt | Geq

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
  | IfThenElse (cond : StmtExpr) (thenBranch : StmtExpr) (elseBranch : Option StmtExpr)
  | Block (statements : List StmtExpr)
  /- The initializer must be set if this StmtExpr is pure -/
  | LocalVariable (name : Identifier) (type : HighType) (initializer : Option StmtExpr)
  /- While is only allowed in an impure context
    The invariant and decreases are always pure
  -/
  | While (label: Option Identifier) (cond : StmtExpr) (invariant : Option StmtExpr) (decreases: Option StmtExpr) (body : StmtExpr)
  | Jump (label : Identifier) (type : JumpType)
  | Return (value : Option StmtExpr)
/- Expression like -/
  | LiteralInt (value: Int)
  | LiteralBool (value: Bool)
  | LiteralReal (value: Real)
  | Identifier (name : Identifier)
  /- Assign is only allowed in an impure context -/
  | Assign (target : StmtExpr) (value : StmtExpr)
  | StaticFieldSelect (target : StmtExpr) (fieldName : Identifier)
  | PureFieldUpdate (target : StmtExpr) (fieldName : Identifier) (newValue : StmtExpr)
  | StaticInvocation (callee : Identifier) (arguments : List StmtExpr)
  | PrimitiveOp (operator: Operation) (arguments : List StmtExpr)
/- Instance related -/
  | This
  /- IsType works both with KnowsType and Composite types
     The newBinding parameter allows bringing a new variable into scope that has the checked type
     The scope where newBinding becomes available depends on where IsType is used
     Example 1: `x is <SomeType> newVar && newVar.someField` here the variable `newVar` became in scope in the RHS of the &&
     Example 2: `if x is <SomeType> newVar then newVar.someField else ...` here the variable `newVar` became in scope in the then branch

     Together with IfThenElse, IsType replaces the need for other pattern matching constructs
  -/
  | IsType (target : StmtExpr) (type: HighType) (newBinding : Option Identifier)
  | InstanceInvocation (target : StmtExpr) (callee : Identifier) (arguments : List StmtExpr)
/- Verification specific -/
  | Assigned (name : StmtExpr)
  | Old (value : StmtExpr)
  /- Fresh may only target impure composite types -/
  | Fresh(value : StmtExpr)

/- Related to creation of objects -/
  /- Create returns a partial type, whose fields are still unassigned and whose type invariants are not guaranteed to hold. -/
  /- In a pure context, may only create pure types -/
  | Create (type : Identifier)
  /- Takes an expression of a partial type, checks that all its fields are assigned and its type invariants hold,
  and return the complete type.
  In case the partial type contained members with partial values, then those are completed as well, recursively.
  This way, you can safely construct cyclic object graphs. -/
  | Complete (value : StmtExpr)

/- Related to dynamic language features -/
  | DynamicInvocation (callable : StmtExpr) (arguments : List StmtExpr)
  /- alternatively, we could have a closure that takes a CompositeType, like Java's inner classes
     This would be more powerful but slightly more of a hassle to use when creating callable closures -/
  | Closure (callable: Callable)
  /- The next two could be defined using a library -/
  | DynamicFieldAccess (target : StmtExpr) (fieldName : StmtExpr)
  | DynamicFieldUpdate (target : StmtExpr) (fieldName : StmtExpr) (newValue : StmtExpr)

/- Related to proofs -/
  | Assert (condition: StmtExpr)
  | Assume (condition: StmtExpr)
  | ProveBy (value: StmtExpr) (proof: StmtExpr)
/- Hole has a dynamic type and is useful when programs are only partially available -/
  | Hole
end

inductive JumpType where | Continue | Break

/-
Note that there are no explicit 'inductive datatypes'. Typed unions are created by
creating a CompositeType for each constructor, and a ConstrainedType for their union.

Example 1:
`composite Some<T> { value: T }`
`constrained Option<T> = value: Dynamic | value is Some<T> || value is Unit`

Example 2:
`composite Cons<T> { head: T, tail: List<T> }`
`constrained List<T> = value: Dynamic | value is Cons<T> || value is Unit`
 -/
inductive TypeDefinition where
  | Composite (ty : CompositeType)
  | Constrainted (ty : ConstrainedType)

structure CompositeType where
  name : Identifier
  typeParameters : List TypeParameter
  extending : List Identifier
  fields : List Field
  isPure : Bool /- A pure type may not have mutable fields, and does not support reference equality -/
  instanceCallables : List Callable

structure PredicateType where
  name : Identifier
  base : HighType
  valueName : Identifier
  constraint : StmtExpr
  witness : StmtExpr

structure Field where
  name : Identifier
  isMutable : Bool
  type : HighType
