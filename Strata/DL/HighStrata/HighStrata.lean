/-
The high strata language is supposed to serve as an intermediate verification language for at least Java, Python, JavaScript.
/
It enables doing various forms of verification:
- Deductive verification
- Property based testing
- Data-flow analysis

Design choices:
- Pure contracts: contracts may only contain pure code. Pure code does not modify the heap, neither by modifying existing objects are creating new ones.
- Callables: instead of functions and methods we have a single more general concept called a 'callable'.
- Purity: Callables can be marked as pure or impure. Pure callables have a reads clause while impure ones have a modifies clause.
  A reads clause is currently not usefulf or impure callables, since reads clauses are used to determine when the output changes, but impure callables can be non-determinismic so the output can always change.
- Opacity: callables can have a body that's transparant or opaque. Only an opaque body may declare a postcondition. A transparant callable must be pure.
- StmtExpr: Statements and expressions are part of the same type. This reduces duplication since the same concepts are needed in both, such as conditions and variable declarations.
- Loops: The only loop is a while, but this can be used to compile do-while and for loops to as well.
- Jumps: Instead of break and continue statements, there is a labelled block that can be exited from using an exit statement inside of it.
  This can be used to model break statements and continue statements for both while and for loops.
- Pattern matching: there is no match-case construct, but there are type tests with pattern matching that enable the same functionality but more generally.

- User defined types consist of two categories: composite types and constrained types.
  - Composite types have fields and callables, and may extend other composite types.
  - Constrained types are defined by a base type and a constraint over that type.
  - Algebriac datatypes do not exist directly but can be encoded using composited and constrained types.
- The base type for all composite types is dynamic, which is a type that can be type tested.
  For all primitive types there is an implicit composite type that wraps around the primitive, so primitives can be boxed to become the Dynamic type. They can be unboxed using a type test. This is useful for source languages such as JavaScript. The operators that work on primitives also work on the dynamic type, although they can error if the types do not align.
- There is no concept of constructors, but each composite type has a partial variant that represents an object of that type whose fields
  are not yet assigned and whose type invariants might not hold.
  A partial type can be completed to a full type once all fields are assigned and the type invariants are known to hold.
- There is no concept of namespaces so all references need to be fully qualified.

-/

abbrev Identifier := String /- Potentially this could be an Int to save resources. -/

mutual
structure Callable: Type where
  name : Identifier
  typeParameters : List TypeParameter
  inputs : List Parameter
  output : HighType
  precondition : StmtExpr
  decreases : StmtExpr
  purity : Purity
  body : Body

structure Parameter where
  name : Identifier
  type : HighType

inductive HighType : Type where
  | TVoid
  | TBool
  | TInt
  | TReal
  | TFloat64 /- Required for JavaScript (number). Used by Python (float) and Java (double) as well -/
  /- A value of type `Dynamic` is a tuple consisting of a type and an expression.
     Values are automatically casted to and from `Dynamic`
     Example: `var x: Dynamic = 3; return x is Int` returns `True`
   -/
  | Dynamic
  | UserDefined (name: Identifier)
  | Applied (base : HighType) (typeArguments : List HighType)
  /- Partial represents a composite type with unassigned fields and whose type invariants might not hold.
     Can be represented as a Map that contains a subset of the fields of the composite type -/
  | Partial (base : HighType)
  /- A nullable type is implicitly cast to its base when required,
    such as in a member access or when assigned to a variable of the base type -/
  | Nullable (base : HighType)
  /- Java has implicit intersection types.
     Example: `<cond> ? RustanLeino : AndersHejlsberg` could be typed as `Scientist & Scandinavian`-/
  | Intersection (types : List HighType)
  deriving Repr

structure TypeParameter where
  name : Identifier
  bounds : List HighType /- Java has bounded type parameters -/

inductive Purity: Type where
/-
Since a reads clause is used to determine when the result of a call changes,
a reads clause is only useful for deterministic callables.
-/
  | Pure (reads : StmtExpr)
  | Impure (modifies : StmtExpr)

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
  | Block (statements : List StmtExpr) (label : Option Identifier)
  /- The initializer must be set if this StmtExpr is pure -/
  | LocalVariable (name : Identifier) (type : HighType) (initializer : Option StmtExpr)
  /- While is only allowed in an impure context
    The invariant and decreases are always pure
  -/
  | While (cond : StmtExpr) (invariant : Option StmtExpr) (decreases: Option StmtExpr) (body : StmtExpr)
  | Exit (target: Identifier)
  | Return (value : Option StmtExpr)
/- Expression like -/
  | LiteralInt (value: Int)
  | LiteralBool (value: Bool)
  -- Commented out since this needs MathLib
  -- | LiteralReal {Rat} (value: Rat)
  | Identifier (name : Identifier)
  /- Assign is only allowed in an impure context -/
  | Assign (target : StmtExpr) (value : StmtExpr)
  | StaticFieldSelect (target : StmtExpr) (fieldName : Identifier)
  /- PureFieldUpdate is the only way to assign values to fields of pure types -/
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

/- Verification specific -/
-- TODO: Add forall and exists
  | Assigned (name : StmtExpr)
  | Old (value : StmtExpr)
  /- Fresh may only target impure composite types -/
  | Fresh(value : StmtExpr)

/- Related to proofs -/
  | Assert (condition: StmtExpr)
  | Assume (condition: StmtExpr)
  | ProveBy (value: StmtExpr) (proof: StmtExpr)
/- Hole has a dynamic type and is useful when programs are only partially available -/
  | Hole
end

partial def highEq (a: HighType) (b: HighType) : Bool := match a, b with
  | HighType.TVoid, HighType.TVoid => true
  | HighType.TBool, HighType.TBool => true
  | HighType.TInt, HighType.TInt => true
  | HighType.TReal, HighType.TReal => true
  | HighType.TFloat64, HighType.TFloat64 => true
  | HighType.Dynamic, HighType.Dynamic => true
  | HighType.UserDefined n1, HighType.UserDefined n2 => n1 == n2
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.zip args2 |>.all (fun (a1, a2) => highEq a1 a2))
  | HighType.Partial b1, HighType.Partial b2 => highEq b1 b2
  | HighType.Nullable b1, HighType.Nullable b2 => highEq b1 b2
  | HighType.Intersection ts1, HighType.Intersection ts2 =>
      ts1.length == ts2.length && (ts1.zip ts2 |>.all (fun (t1, t2) => highEq t1 t2))
  | _, _ => false

instance : BEq HighType where
  beq := highEq

def HighType.isDynamic : HighType → Bool
  | Dynamic => true
  | _ => false

def HighType.isBool : HighType → Bool
  | TBool => true
  | _ => false

structure Field where
  name : Identifier
  isMutable : Bool
  type : HighType

structure CompositeType where
  name : Identifier
  typeParameters : List TypeParameter
  extending : List Identifier
  fields : List Field
  isPure : Bool /- A pure type may not have mutable fields, and does not support reference equality -/
  instanceCallables : List Callable

structure ConstrainedType where
  name : Identifier
  base : HighType
  valueName : Identifier
  constraint : StmtExpr
  witness : StmtExpr

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
  | Constrainted {ConstrainedType} (ty : ConstrainedType)

structure Program where
  staticCallables : List Callable
  staticFields : List Field
  types : List TypeDefinition
