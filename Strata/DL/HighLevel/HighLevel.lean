/- TODO figure out the tags on composite types and dynamic interaction -/
/-
The high strata language is supposed to serve as an intermediate verification language for at least Java, Python, JavaScript.

It enables doing various forms of verification:
- Deductive verification
- Property based testing
- Data-flow analysis

Language features:
- An important concept is that of purety, both code and types can be pure or impure.
Code in contracts must always be pure. Inside pure code, only pure types can be instantiated.
- There is no concept of namespaces so all references need to be fully qualified.

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
  precondition : StmtExpr true
  decreases : StmtExpr true
  reads : StmtExpr true
  purity : Purity
  body : Body true /- TODO fix -/

inductive Purity: Type where
  | Pure
  | Impure (modifies : StmtExpr false)

structure Parameter where
  name : Identifier
  type : HighType

inductive HighType : Type where
  | Void
  | Bool
  | Int
  | Real
  | Float64 /- Required for JavaScript (number). Used by Python (float) and Java (double) as well -/
  | UserDefined (name: Identifier)
  | Dynamic /- A value of type `Dynamic` is a tuple consisting of a type and an expression -/
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
inductive Body : (isPure: Bool) -> Type where
  /- Maybe we can allow the body to be impure as well, but for now we don't -/
  | Transparent (body : StmtExpr true): Body true
  /- Without an implementation, the postcondition is assumed -/
  /- | Opaque (postcondition : StmtExpr true) (implementation : Option (StmtExpr isPure)) : Body isPure -/
  /- An abstract body is useful for types that are extending.
    A type containing any members with abstract bodies can not be instantiated. -/
  | Abstract (postcondition : StmtExpr true) : Body isPure

/-
A StmtExpr contains both constructs that we typically find in statements and those in expressions.
By using a single datatype we prevent duplication of constructs that can be used in both contexts,
such a conditionals and variable declarations
-/
inductive StmtExpr : (isPure: Bool) -> Type where
/- Statement like -/
  | IfThenElse (cond : StmtExpr isPure) (thenBranch : StmtExpr isPure) (elseBranch : Option (StmtExpr isPure)): StmtExpr isPure
  | Block (statements : List (StmtExpr isPure)) : StmtExpr isPure
  | LocalVariable (name : Identifier) (type : HighType) (initializer : Option (StmtExpr isPure))
    : StmtExpr (initializer.isSome && isPure)
  /- While is only allowed in an impure context
    The invariant and decreases are always pure
  -/
  | While (label: Option Identifier) (cond : StmtExpr isPure)
    (invariant : Option (StmtExpr true))
    (decreases: Option (StmtExpr true))
    (body : StmtExpr isPure)
    : StmtExpr false
  | Jump (label : Identifier) (type : JumpType): StmtExpr false
  | Return (value : Option (StmtExpr isPure)): StmtExpr isPure
/- Expression like -/
  | Identifier (name : Identifier): StmtExpr isPure
  /- Assign is only allowed in an impure context -/
  | Assign (target : StmtExpr isPure) (value : StmtExpr isPure): StmtExpr false
  | StaticFieldSelect (target : StmtExpr isPure) (fieldName : Identifier): StmtExpr isPure
  | PureFieldUpdate (target : StmtExpr isPure) (fieldName : Identifier) (newValue : StmtExpr isPure): StmtExpr isPure
  | StaticInvocation (callee : Identifier) (arguments : List (StmtExpr isPure)): StmtExpr isPure
  | PrimitiveOp (operator: Operation) (arguments : List (StmtExpr isPure)): StmtExpr isPure
/- Instance related -/
  | This: StmtExpr isPure
  /- IsType works both with dynamic
     The newBinding parameter allows bringing a new variable into scope that has the checked type
     The scope where newBinding becomes available depends on where IsType is used
     Example 1: `x is <SomeType> newVar && newVar.someField` here the variable `newVar` became in scope in the RHS of the &&
     Example 2: `if x is <SomeType> newVar then newVar.someField else ...` here the variable `newVar` became in scope in the then branch

     Together with IfThenElse, IsType replaces the need for other pattern matching constructs
  -/
  | IsType (target : StmtExpr isPure) (type: HighType) (newBinding : Option Identifier): StmtExpr isPure
  | InstanceInvocation (target : StmtExpr isPure) (callee : Identifier) (arguments : List (StmtExpr isPure)): StmtExpr isPure
/- Verification specific -/
  | Assigned (name : StmtExpr isPure): StmtExpr isPure
  | Old (value : StmtExpr isPure): StmtExpr isPure
  /- Fresh may only target impure composite types -/
  | Fresh(value : StmtExpr isPure): StmtExpr isPure

/- Related to creation of objects -/
  /- Create returns a partial type, whose fields are still unassigned and whose type invariants are not guaranteed to hold. -/
  /- In a pure context, may only create pure types -/
  | Create (type : Identifier): StmtExpr isPure
  /- Takes an expression of a partial type, checks that all its fields are assigned and its type invariants hold,
  and return the complete type.
  In case the partial type contained members with partial values, then those are completed as well, recursively.
  This way, you can safely construct cyclic object graphs. -/
  | Complete (value : StmtExpr isPure): StmtExpr isPure

/- Related to dynamic language features -/
  | DynamicInvocation (callable : StmtExpr isPure) (arguments : List (StmtExpr isPure)): StmtExpr isPure
  /- alternatively, we could have a closure that takes a CompositeType, like Java's inner classes
     This would be more powerful but slightly more of a hassle to use when creating callable closures -/
  | Closure (callable: Callable): StmtExpr isPure
  /- The next two could be defined using a library -/
  | DynamicFieldAccess (target : StmtExpr isPure) (fieldName : StmtExpr isPure): StmtExpr isPure
  | DynamicFieldUpdate (target : StmtExpr isPure) (fieldName : StmtExpr isPure) (newValue : StmtExpr isPure): StmtExpr isPure

/- Hole has a dynamic type and is useful when programs are only partially available -/
  | Hole: StmtExpr isPure
end

inductive JumpType where | Continue | Break

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
