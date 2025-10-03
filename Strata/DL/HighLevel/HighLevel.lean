structure Program where
  staticCallables : List Callable
  types : List TypeDefinition

mutual
structure Callable: Type where
  name : String
  typeParameters : List TypeParameter
  inputs : List Parameter
  output : Parameter
  precondition : StmtExpr
  decreases : StmtExpr
  reads : StmtExpr
  purity : Purity
  body : Body

inductive Purity where
  | Pure
  | Impure (modifies : Expression)

structure Parameter where
  name : String
  type : HighType

inductive HighType : Type where
  | Bool
  | Int
  | Real
  | Float64 /- Required for JavaScript (number). Used by Python (float) and Java (double) as well -/
  | UserDefined (name: String)
  | Dynamic /- Like TypeScript's 'any' -/
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
  name : String
  bounds : List HighType /- Java has bounded type parameters -/

/- No support for something like function-by-method yet -/
inductive Body where
  | Transparent (body : StmtExpr)
/- Without an implementation, the postcondition is assumed -/
  | Opaque (postcondition : StmtExpr) (implementation : Option StmtExpr)
/- An abstract body is useful for types that are extending.
    A type containing any members with abstract bodies can not be instantiated. -/
  | Abstract (postcondition : StmtExpr)

/-
A StmtExpr contains both constructs that we typically find in statements and those in expressions.
By using a single datatype we prevent duplication of constructs that can be used in both contexts,
such a conditionals and variable declarations
-/
inductive StmtExpr : Type where
/- Statement like -/
  | IfThenElse (cond : StmtExpr) (thenBranch : StmtExpr) (elseBranch : StmtExpr)
  | Block (statements : List StmtExpr)
  | LocalVariable (name : String) (type : HighType) (initializer : Option StmtExpr)
  | While (cond : StmtExpr) (invariant : Option StmtExpr) (decreases: Option StmtExpr) (body : StmtExpr)
/- Expression like -/
  | Identifier (name : String)
  | Assign (taregt : StmtExpr) (value : StmtExpr)
  | StaticFieldSelect (target : StmtExpr) (fieldName : String)
  | PureFieldUpdate (target : StmtExpr) (fieldName : String) (newValue : StmtExpr)
  | StaticInvocation (callee : String) (arguments : List StmtExpr)
  | PrimitiveOp (operator: Operation) (arguments : List StmtExpr)
/- Instance related -/
  | This
  /- IsType works both with dynamic and with tagged composite types -/
  | IsType (target : StmtExpr) (typeName : String)
  | InstanceInvocation (target : StmtExpr) (callee : String) (arguments : List StmtExpr)
/- Verification specific -/
  | Assigned (name : StmtExpr)
  | Old (value : StmtExpr)

/- Related to creation of objects -/
  /- Create returns a partial type, whose fields are still unassigned and whose type invariants are not guaranteed to hold. -/
  | Create (type : String)
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

/- Hole has a dynamic type and is useful when programs are only partially available -/
  | Hole
end

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

inductive TypeDefinition where
  | Composite (ty : CompositeType)
  | Predicate (ty : PredicateType)

structure CompositeType where
  name : String
  typeParameters : List TypeParameter
  extending : List String
  fields : List Field
  isPure : Bool /- A pure type may not have mutable fields, and does not support reference equality -/
  instanceCallables : List Callable
  tagged : Bool /- Whether an instance of this composite knows its type -/

structure PredicateType where
  name : String
  base : HighType
  valueName : String
  constraint : StmtExpr
  witness : StmtExpr

structure Field where
  name : String
  isMutable : Bool
  type : HighType
