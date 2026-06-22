/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData
public import Strata.Languages.Core.Expressions
import Strata.Util.Tactics
public import StrataDDM.Util.Decimal
public import Strata.Util.FileRange
open StrataDDM

/-
Documentation for Laurel can be found in docs/verso/LaurelDoc.lean

This module contains the Laurel AST. The high-level Laurel API is in
`Strata.Languages.Laurel`.
-/
namespace Strata
namespace Laurel

public section

/-- A name-introduction site (variable declaration, procedure, field, type, etc.).
    Carries a mandatory unique ID assigned by the resolution pass. -/
structure Identifier where
  /-- The declared name. -/
  text : String
  /-- Unique ID assigned by the resolution pass. -/
  uniqueId : Option Nat := none
  /-- Source location for this identifier. -/
  source : Option FileRange := none
  deriving Repr

-- Temporary hack because the Python through Laurel pipeline doesn't resolve
instance : BEq Identifier where
  beq a b := a.text == b.text

instance : Inhabited Identifier where
 default := { text := "defaultIdentifier" }

instance : ToString Identifier where
  toString id := id.text

instance : Coe String Identifier where
  coe s := { text := s }

def mkId (name: String): Identifier := { text := name }

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

instance : ToString Operation where
  toString
    | .Eq => "=="          | .Neq => "!="
    | .And => "&&"         | .Or => "||"
    | .Not => "!"          | .Implies => "==>"
    | .AndThen => "&&!"    | .OrElse => "||!"
    | .Neg => "-"          | .Add => "+"
    | .Sub => "-"          | .Mul => "*"
    | .Div => "/"          | .Mod => "%"
    | .DivT => "/t"        | .ModT => "%t"
    | .Lt => "<"           | .Leq => "<="
    | .Gt => ">"           | .Geq => ">="
    | .StrConcat => "++"

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
  deriving Repr

/--
The type system for Laurel programs.

`HighType` covers primitive types (`TVoid`, `TBool`, `TInt`, `TReal`, `TFloat64`,
`TString`), collection types (`TSet`), user-defined types (`UserDefined`),
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
  /-- Set type, e.g. `Set int`. -/
  | TSet (elementType : AstNode HighType)
  /-- Map type. -/
  | TMap (keyType : AstNode HighType) (valueType : AstNode HighType)
  /-- A Identifier to a user-defined composite or constrained type by name. -/
  | UserDefined (name : Identifier)
  /-- A bound type variable, e.g. `T` in `procedure f<T>(x: T)`. Introduced by
  resolution when a name in type position matches an in-scope type parameter
  (declared on a procedure, composite, or datatype). Distinct from `UserDefined`,
  which names a concrete type. -/
  | TVar (name : Identifier)
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
  /-- An internal-only type produced by `computeExprType` for multi-output procedure calls.
  Consumed by the resolution arity check and `highEq`. Should never appear in a serialized program. -/
  | MultiValuedExpr (types : List (AstNode HighType))
  deriving Repr

/-- Whether a quantifier is universal or existential. -/
inductive QuantifierMode where
  | Forall
  | Exists
  deriving Repr, BEq, Inhabited

/-- Whether an increment/decrement operator is in prefix or postfix form.
    Prefix form yields the new value; postfix form yields the old value. -/
inductive IncrDecrMode where
  /-- Prefix form: `++x` or `--x`. Yields the new value. -/
  | Pre
  /-- Postfix form: `x++` or `x--`. Yields the old value. -/
  | Post
  deriving Repr, BEq, Inhabited

/-- Whether an increment/decrement operator increments by 1 or decrements by 1. -/
inductive IncrDecrOp where
  /-- `++` — adds 1 to the target. -/
  | Incr
  /-- `--` — subtracts 1 from the target. -/
  | Decr
  deriving Repr, BEq, Inhabited

mutual

/--
A procedure in Laurel. Procedures are the main unit of specification and
verification. Unlike separate functions and methods, Laurel uses a single
general concept that covers both.
-/
structure Procedure : Type where
  /-- The procedure's name. -/
  name : Identifier
  /-- Type parameters, e.g. `T` in `procedure f<T>(...)`. Empty for monomorphic
      procedures (the default keeps every existing construction site compiling).
      Brought into scope by resolution so `T` in a signature resolves to `.TVar`. -/
  typeArgs : List Identifier := []
  /-- Input parameters with their types. -/
  inputs : List Parameter
  /-- Output parameters with their types. Multiple outputs are supported. -/
  outputs : List Parameter
  /-- The preconditions that callers must satisfy. -/
  preconditions : List Condition
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
  /-- Axioms to emit alongside this procedure. Populated by the contract pass from
      `invokeOn` and ensures clauses. -/
  axioms : List (AstNode StmtExpr) := []

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
  /-- When `true`, this condition is *free*: assumed but not checked.
      A free precondition is assumed by the implementation but not asserted at
      call sites. A free postcondition is assumed upon return from calls but
      not checked on exit from implementations. -/
  free : Bool := false

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
      -- TODO: add back non-determinism together with an implementation
      -- deterministic : Bool
  /-- An abstract body that must be overridden in extending types. A type containing any members with abstract bodies cannot be instantiated. -/
  | Abstract (postconditions : List Condition)
  /-- An external body for procedures that are not translated to Core (e.g., built-in primitives). -/
  | External

/--
A variable reference or declaration: a local variable, a field access on an expression, or a local variable declaration.
-/
inductive Variable : Type where
  /-- A local variable reference by name. -/
  | Local (name : Identifier)
  /-- Read a field from a target expression. Combined with `Assign` for field writes. -/
  | Field (target : AstNode StmtExpr) (fieldName : Identifier)
  /-- A local variable declaration with a name and type. -/
  | Declare (parameter : Parameter)

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
  /-- A while loop with a condition, invariants, optional termination measure, and body.
      Only allowed in impure contexts.

      `postTest` selects when the condition is tested relative to the body:
      - `false` (default) — a *pre-test* loop (`while`): the condition is checked
        before the body, so the body may run zero times.
      - `true` — a *post-test* loop (`do … while`): the body runs once before the
        condition is first checked, so it always runs at least once.

      Invariants are checked at the loop head (before each body) in both cases.
      A post-test loop is lowered to the pre-test form by the `EliminateDoWhile` pass. -/
  | While (cond : AstNode StmtExpr) (invariants : List (AstNode StmtExpr))
    (decreases : Option (AstNode StmtExpr))
    (body : AstNode StmtExpr)
    (postTest : Bool := false)
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
  /-- A bitvector literal with value and width. -/
  | LiteralBv (value : Nat) (width : Nat)
  /-- A variable reference or declaration. When `var` is `Variable.Local`, this is a reference
      that evaluates to the variable's value. When `var` is `Variable.Declare`, this is a
      declaration without an initializer (used as a standalone statement in a block). -/
  | Var (var : Variable)
  /-- Assignment to one or more targets. Multiple targets are only supported with identifier targets and a call as the RHS. -/
  | Assign (targets : List (AstNode Variable)) (value : AstNode StmtExpr)
  /-- Java-style increment/decrement operator. The target must be a `Local` or `Field`
      `Variable`. As an expression, prefix form yields the new value (after the update)
      and postfix form yields the old value (before the update). As a statement the
      yielded value is discarded.
      Eliminated by the `EliminateIncrDecr` pass before lifting imperative expressions. -/
  | IncrDecr (mode : IncrDecrMode) (op : IncrDecrOp) (target : AstNode Variable)
  /-- Update a field on a pure (value) type, producing a new value. -/
  | PureFieldUpdate (target : AstNode StmtExpr) (fieldName : Identifier) (newValue : AstNode StmtExpr)
  /-- Call a static procedure by name with the given arguments. -/
  | StaticCall (callee : Identifier) (arguments : List (AstNode StmtExpr))
  /-- Apply a primitive operation to the given arguments.
      The skipProof property is used internally.
      It means that any precondition of the operator, such as division has, should be ignored. -/
  | PrimitiveOp (operator : Operation) (arguments : List (AstNode StmtExpr))
    (skipProof: Bool := false)
  /-- Create new object (`new`). `typeArgs` carries explicit instantiation
      arguments for a generic composite, e.g. `new Box<int>` → `ref = Box`,
      `typeArgs = [int]`. Empty for a non-generic `new C` (the common case and the
      pre-existing surface syntax), so the monomorphizer can read the concrete
      instantiation directly off the allocation site rather than recovering it
      from surrounding context. -/
  | New (ref : Identifier) (typeArgs : List (AstNode HighType) := [])
  /-- Reference to the current object (`this`/`self`). -/
  | This
  /-- Reference equality test between two expressions. -/
  | ReferenceEquals (lhs : AstNode StmtExpr) (rhs : AstNode StmtExpr)
  /-- Type cast: treat the target as the given type. -/
  | AsType (target : AstNode StmtExpr) (targetType : AstNode HighType)
  /-- Type test: check whether the target is an instance of the given type. -/
  | IsType (target : AstNode StmtExpr) (type : AstNode HighType)
  /-- Call an instance method on a target object. -/
  | InstanceCall (target : AstNode StmtExpr) (callee : Identifier) (arguments : List (AstNode StmtExpr))
  /-- Quantification (universal or existential) over a typed parameter with an optional trigger. -/
  | Quantifier (mode : QuantifierMode) (param : Parameter) (trigger : Option (AstNode StmtExpr)) (body : AstNode StmtExpr)
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
  /-- A hole represents an unknown expression.
      This can be used to represent programs that are still under development, for example the program `3 + `
      The defining property of a hole is that interaction with it and other code should not produce any errors.
      Besides representing partial user programs,
      holes can also be used to handle under development parts of compilers that target Laurel.
      - `deterministic`: if true, the hole represents a deterministic unknown
        (translated as an uninterpreted function); if false, a nondeterministic
        unknown (translated as a havoced variable). Nondeterministic holes are
        not allowed in functions.
      - `type`: this property is used internally by Laurel and can be left to its default value.
        Internal usage: inferred by the hole type inference pass; `none` means not yet inferred. -/
  | Hole (deterministic : Bool := true) (type : Option (AstNode HighType) := none)

inductive ContractType where
  | Reads | Modifies | Precondition | PostCondition
end

/-- A short user-facing name for the construct, used in diagnostic messages. -/
def StmtExpr.constrName : StmtExpr → String
  | .IfThenElse ..       => "if"
  | .Block ..            => "block"
  | .While ..            => "while"
  | .Exit ..             => "exit"
  | .Return ..           => "return"
  | .LiteralInt ..       => "integer literal"
  | .LiteralBool ..      => "boolean literal"
  | .LiteralString ..    => "string literal"
  | .LiteralDecimal ..   => "decimal literal"
  | .LiteralBv ..        => "bitvector literal"
  | .Var ..              => "variable"
  | .Assign ..           => ":="
  | .IncrDecr _ .Incr .. => "++"
  | .IncrDecr _ .Decr .. => "--"
  | .PureFieldUpdate ..  => "field update"
  | .StaticCall ..       => "call"
  | .PrimitiveOp op ..   => toString op
  | .New ..              => "new"
  | .This                => "this"
  | .ReferenceEquals ..  => "reference equality"
  | .AsType ..           => "as"
  | .IsType ..           => "is"
  | .InstanceCall ..     => "method call"
  | .Quantifier ..       => "quantifier"
  | .Assigned ..         => "assigned"
  | .Old ..              => "old"
  | .Fresh ..            => "fresh"
  | .Assert ..           => "assert"
  | .Assume ..           => "assume"
  | .ProveBy ..          => "by"
  | .ContractOf ..       => "contractOf"
  | .Abstract            => "abstract"
  | .All                 => "all"
  | .Hole ..             => "hole"

@[expose] abbrev HighTypeMd := AstNode HighType
@[expose] abbrev StmtExprMd := AstNode StmtExpr
@[expose] abbrev VariableMd := AstNode Variable

/-- The base composite NAME of a type reference, for consumers that need the parent
    name rather than its instantiation: `.UserDefined Base` and `.Applied (UserDefined
    Base) args` both peel to `Base`. `none` for a type with no nameable base (a bare
    `.TVar`, a primitive, etc.) — callers treat that as "no inheritable parent". Used by
    the `extending`-list consumers after `extending` became `List HighTypeMd`:
    field-scope inheritance, the subtype `extendingMap`/`ancestors`, and diamond checks
    all key on the parent NAME (field names are instantiation-independent), so peeling to
    the base is correct for them; only prelude dependency-collection needs the full type
    (it recurses the args separately). -/
def highBaseName? : HighType → Option Identifier
  | .UserDefined n => some n
  | .Applied base _ => highBaseName? base.val
  | .TVar n => some n   -- an inherited type-var parent (pre-monomorphization); name-keyed lookups still want it
  | _ => none

/-- Recurse a `HighType`'s structural constructors (`TSet`/`TMap`/`Applied`/`Pure`/
    `Intersection`/`MultiValuedExpr`), rewriting each NAMED leaf via `f` — which receives
    the leaf's constructor (`.UserDefined` or `.TVar`) and its name, and returns the
    replacement. Source metadata is preserved per node. The shared traversal skeleton for
    `substTypeVars` (here) and `tvarizeType` (Resolution); they differ only in `f`.

    Lives here (not in MonomorphizeComposites, where the substitution originated) so the
    subtype checker can reuse `substTypeVars` for remap-aware generic upcast without an
    import cycle — it depends only on `HighType`/`HighTypeMd`/`Std.HashMap`, all above. -/
partial def mapHighTypeNames (f : (Identifier → HighType) → Identifier → HighType)
    (ty : HighTypeMd) : HighTypeMd :=
  let rec go (ty : HighTypeMd) : HighTypeMd :=
    let v := match ty.val with
      | .UserDefined name => f .UserDefined name
      | .TVar name => f .TVar name
      | .TSet et => .TSet (go et)
      | .TMap kt vt => .TMap (go kt) (go vt)
      | .Applied base args => .Applied (go base) (args.map go)
      | .Pure base => .Pure (go base)
      | .Intersection ts => .Intersection (ts.map go)
      | .MultiValuedExpr ts => .MultiValuedExpr (ts.map go)
      | other => other
    { val := v, source := ty.source }
  go ty

/-- Substitute type variables (by name) throughout a `HighType`. A parameter may appear as
    `.TVar name` (when resolution scoped it) or `.UserDefined name` (if it didn't); either
    is replaced by its `subst` entry (by name), or left as-is. -/
partial def substTypeVars (subst : Std.HashMap String HighTypeMd) (ty : HighTypeMd) : HighTypeMd :=
  mapHighTypeNames (fun ctor name =>
    match subst.get? name.text with
    | some replacement => replacement.val
    | none => ctor name) ty

/-- The label of the implicit block that wraps every procedure body.

    `LaurelToCoreTranslator` lowers each procedure body to a single
    `Core.Statement.block bodyLabel …`, and lowers an early `return`
    (or, in the Python frontend, a Python `return`) to `Exit bodyLabel`,
    so that jumping to the end of the body falls through past the block.
    The resolution pass pre-registers this label in scope (via `withLabel`)
    before walking a body, so those `Exit bodyLabel` jumps resolve even
    though the label has no syntactic declaration site.

    Shared here so the translator, the resolver, and frontends agree on the
    exact string rather than each hard-coding it. The leading `$` keeps it
    out of the user-name space (no source identifier can contain `$`). -/
def bodyLabel : String := "$body"

theorem AstNode.sizeOf_val_lt {t : Type} [SizeOf t] (e : AstNode t) : sizeOf e.val < sizeOf e := by
  cases e; grind

theorem Condition.sizeOf_condition_lt (c : Condition) : sizeOf c.condition < 1 + sizeOf c := by
  cases c; grind

/-- The target expression inside a `Variable.Field` is strictly smaller than the `Field` itself.
Useful for termination proofs when recursing into `Variable.Field` targets. -/
theorem Variable.sizeOf_field_target_lt (target : AstNode StmtExpr) (fieldName : Identifier) :
    sizeOf target < sizeOf (Variable.Field target fieldName) := by
  simp; omega

/-- Variant of `sizeOf_field_target_lt` that works directly with an `AstNode Variable`
whose `.val` is known to be a `Field`. Eliminates the common three-line termination proof pattern:
```
have := Variable.sizeOf_field_target_lt target fieldName
have : sizeOf v.val = sizeOf (Variable.Field target fieldName) := by exact congrArg sizeOf h
omega
```
-/
theorem Variable.sizeOf_field_target_lt_of_eq {v : AstNode Variable}
    {target : AstNode StmtExpr} {fieldName : Identifier}
    (h : v.val = Variable.Field target fieldName) :
    sizeOf target < sizeOf v := by
  have := AstNode.sizeOf_val_lt v
  have := Variable.sizeOf_field_target_lt target fieldName
  have : sizeOf v.val = sizeOf (Variable.Field target fieldName) := congrArg sizeOf h
  omega

/-- Apply a monadic transformation to the condition expression, preserving the summary. -/
@[expose]
def Condition.mapM [Monad m] (f : AstNode StmtExpr → m (AstNode StmtExpr)) (c : Condition) : m Condition :=
  return { c with condition := ← f c.condition }

/-- Apply a pure transformation to the condition expression, preserving the summary. -/
def Condition.mapCondition (f : AstNode StmtExpr → AstNode StmtExpr) (c : Condition) : Condition :=
  { c with condition := f c.condition }

/-- Build a provenance from an optional source location. -/
def fileRangeToProvenance (source : Option FileRange) : Provenance :=
  match source with
  | some fr => Provenance.ofSourceRange fr.file fr.range
  | none => .synthesized .laurel

/-- Build Core metadata from an optional source location. -/
def fileRangeToCoreMd (source : Option FileRange) : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofProvenance (fileRangeToProvenance source)

/-- Build Core metadata from an AstNode's source location. -/
def astNodeToCoreMd (node : AstNode α) : Imperative.MetaData Core.Expression :=
  fileRangeToCoreMd node.source

/-- Build Core metadata from an Identifier's source location. -/
def identifierToCoreMd (id : Identifier) : Imperative.MetaData Core.Expression :=
  fileRangeToCoreMd id.source

/-- Create a DiagnosticModel from an optional source location and a message. -/
def diagnosticFromSource (source : Option FileRange) (msg : String) (type : DiagnosticType := .UserError) : DiagnosticModel :=
  match source with
  | some fr => DiagnosticModel.withRange fr msg type
  | none => DiagnosticModel.fromMessage msg type

instance : Inhabited StmtExpr where
  default := .Hole

instance : Inhabited (AstNode Variable) where
  default := { val := .Local default, source := none }

instance : Inhabited HighTypeMd where
  default := { val := HighType.Unknown, source := some { file := .file "HighTypeMd default", range := default} }

instance : Inhabited StmtExprMd where
  default := { val := default, source := none }

def highEq (a : HighTypeMd) (b : HighTypeMd) : Bool := match _a: a.val, _b: b.val with
  | HighType.TVoid, HighType.TVoid => true
  | HighType.TBool, HighType.TBool => true
  | HighType.TInt, HighType.TInt => true
  | HighType.TFloat64, HighType.TFloat64 => true
  | HighType.TReal, HighType.TReal => true
  | HighType.TString, HighType.TString => true
  | HighType.TBv n1, HighType.TBv n2 => n1 == n2
  | HighType.TSet t1, HighType.TSet t2 => highEq t1 t2
  | HighType.TMap k1 v1, HighType.TMap k2 v2 => highEq k1 k2 && highEq v1 v2
  | HighType.UserDefined r1, HighType.UserDefined r2 => r1.text == r2.text
  | HighType.TVar r1, HighType.TVar r2 => r1.text == r2.text
  | HighType.TCore s1, HighType.TCore s2 => s1 == s2
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.attach.zip args2 |>.all (fun (a1, a2) => highEq a1.1 a2))
  | HighType.Pure b1, HighType.Pure b2 => highEq b1 b2
  | HighType.Intersection ts1, HighType.Intersection ts2 =>
      ts1.length == ts2.length && (ts1.attach.zip ts2 |>.all (fun (t1, t2) => highEq t1.1 t2))
  | HighType.Unknown, HighType.Unknown => true
  | HighType.MultiValuedExpr ts1, HighType.MultiValuedExpr ts2 =>
      ts1.length == ts2.length && (ts1.attach.zip ts2 |>.all (fun (t1, t2) => highEq t1.1 t2))
  | _, _ => false
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    . cases a1; term_by_mem
    . cases t1; term_by_mem
    . cases t1; term_by_mem

instance : BEq HighTypeMd where
  beq := highEq

deriving instance BEq for HighType

/-- Lookup tables threaded through subtyping/consistency checks. Built from
    the program's `TypeDefinition`s by the resolution pass:
    - `unfoldMap` maps an alias or constrained type's name to the type it
      unwraps to (alias target / constrained base). Followed transitively to
      reach a non-alias, non-constrained type.
    - `extendingMap` maps a composite type's name to the *direct* parents in
      its `extending` list. Walked transitively for the subtype check.

    Keyed by type-name *text* (`String`), not `Identifier`: this is consistent
    with how `highEq` decides `UserDefined` equality (by `.text`), and is forced
    because the lattice is built from the *unresolved* program in
    `TypeLattice.ofTypes`, before the resolution pass assigns `uniqueId`s.
    Consequence: nominal type identity is by name text, so subtyping
    (`ancestors` walking `extendingMap`) assumes type names are globally unique.
    Safe today (no module system); revisit when modules / namespacing / imports
    land, since two distinct same-named types would otherwise share an
    inheritance chain. -/
structure TypeLattice where
  unfoldMap : Std.HashMap String HighTypeMd := {}
  extendingMap : Std.HashMap String (List String) := {}
  -- Per composite NAME: its type-param names + its parent type
  -- EXPRESSIONS (verbatim, e.g. `Pair<B,A>`). Carries the remap that `extendingMap`
  -- (name-only) discards, so `substitutedAncestors` can compute the TRUE supertypes of
  -- an instantiation. `extendingMap` is kept unchanged for its name-only consumers.
  parentExprMap : Std.HashMap String (List Identifier × List HighTypeMd) := {}
  deriving Inhabited

/-- Unfold aliases and constrained types to their underlying type.
    Composites and primitives are returned unchanged. A `visited` set guards
    against cycles in the alias/constrained graph (already cycle-checked
    elsewhere, but keeps `unfold` safe to call independently). -/
partial def TypeLattice.unfold (ctx : TypeLattice) (ty : HighTypeMd)
    (visited : Std.HashSet String := {}) : HighTypeMd :=
  match ty.val with
  | .UserDefined name =>
    if visited.contains name.text then ty
    else match ctx.unfoldMap.get? name.text with
      | some target => ctx.unfold target (visited.insert name.text)
      | none => ty
  | _ => ty

/-- All ancestors of a composite type (including itself), reachable via
    repeated `extending` lookups. Implemented as a visited-set BFS over the
    `extending` graph: the accumulator `acc` doubles as the visited set, and
    every node is `insert`ed before its parents are enqueued, so each name is
    processed at most once. The accumulator only grows, hence cycles in the
    (possibly malformed) graph terminate — no `fuel` parameter is needed. -/
partial def TypeLattice.ancestors (ctx : TypeLattice) (name : String) : Std.HashSet String :=
  let rec go (acc : Std.HashSet String) (frontier : List String) : Std.HashSet String :=
    match frontier with
    | [] => acc
    | n :: rest =>
      if acc.contains n then go acc rest
      else
        let acc' := acc.insert n
        let parents := (ctx.extendingMap.get? n).getD []
        go acc' (parents ++ rest)
  go {} [name]

/-- The instantiation-tag arms COMMON to both monomorphization (`tyTag`) and heap-box
    naming (`appliedBoxTag`): identifier-legal, `$`-delimited, `none` on any type the
    caller doesn't explicitly handle. `recurse` is the caller's own tagger, threaded so
    nested `.Applied` args use the CALLER's accepted-type-set (the two callers differ only
    in one extra leaf arm — `tyTag` allows `.TVoid`, `appliedBoxTag` allows `.TCore` — and
    each keeps that arm local, so neither caller's accepted set changes). Returning `none`
    (not a catch-all) is load-bearing: a collision would coalesce distinct instantiations.
    E.g. `Box<Pair<int,bool>>` → `Box$a1$Pair$a2$int$bool`. A type this renderer can't tag
    injectively yields `none` (e.g. an arg of `.TMap`/`.TVar`/`.Pure` has no arm here), so a
    `Box<Map int int>` argument is untaggable → the whole tag is `none` (fail loud, never
    coalesced). -/
partial def instTagCommon (recurse : HighType → Option String) : HighType → Option String
  | .TInt => some "int" | .TBool => some "bool" | .TReal => some "real"
  | .TString => some "string" | .TFloat64 => some "float64"
  | .TBv n => some s!"bv{n}"
  | .UserDefined n => some n.text
  | .Applied b as =>
    match b.val with
    | .UserDefined n => do
      let argTags ← as.mapM (fun a => recurse a.val)
      some s!"{n.text}$a{argTags.length}${String.intercalate "$" argTags}"
    | _ => none
  -- Built-in collection formers `Map`/`Set` tag like a 2-/1-ary applied type, so a
  -- `Map`-/`Set`-typed composite FIELD can be heap-boxed (the box-name fns route through
  -- this tagger). `Map`/`Set` are reserved keywords (no user `.Applied Map`), so `Map$a2$…`
  -- cannot collide with a user generic. The `do`-block short-circuits to `none` on an
  -- untaggable element (e.g. a nested `.TVar`), preserving injectivity / fail-loud exactly
  -- like the `.Applied` arm above.
  | .TMap k v => do
    let kt ← recurse k.val
    let vt ← recurse v.val
    some s!"Map$a2${kt}${vt}"
  | .TSet e => do
    let et ← recurse e.val
    some s!"Set$a1${et}"
  | _ => none

/-- A canonical, source-free string key for a `HighType`, for deduping the
    `substitutedAncestors` worklist (structurally-equal `.Applied` types must share a key,
    and metadata must not split them). -/
partial def highTypeKey : HighType → String
  | .TVoid => "void" | .TBool => "bool" | .TInt => "int" | .TReal => "real"
  | .TString => "string" | .TFloat64 => "f64" | .Unknown => "?"
  | .TBv n => s!"bv{n}" | .TCore s => s!"core·{s}"
  | .UserDefined n => n.text | .TVar n => s!"'{n.text}"
  | .TSet v => s!"set<{highTypeKey v.val}>"
  | .Pure v => s!"pure<{highTypeKey v.val}>"
  | .TMap k v => s!"map<{highTypeKey k.val},{highTypeKey v.val}>"
  | .Applied b args => s!"{highTypeKey b.val}<{String.intercalate "," (args.map (fun a => highTypeKey a.val))}>"
  | .Intersection ts => s!"&<{String.intercalate "," (ts.map (fun t => highTypeKey t.val))}>"
  | .MultiValuedExpr ts => s!"mv<{String.intercalate "," (ts.map (fun t => highTypeKey t.val))}>"

/-- The fully-SUBSTITUTED ancestor TYPES of `C<args>`. Starting from the
    given composite `name` instantiated at `args`, look up `(params, parentExprs)` in
    `parentExprMap`, substitute `{params := args}` into each parent EXPRESSION, and recurse
    on each substituted parent — so `extends Pair<B,A>` at `P2<int,bool>` yields the TRUE
    supertype `Pair<bool,int>` (NOT `Pair<int,bool>`), and `extends Base<int>` yields
    `Base<int>` regardless of the child's own args (concretization). This is the remap the
    reverted upcast arm ignored. Returns the parent types (NOT including `C<args>` itself);
    `isSubtype` checks the target against this set with INVARIANT args.
    Termination: `visited` keyed on `highTypeKey` (dedupes structural repeats; a malformed
    cyclic `extends` terminates) + `fuel` backstop. -/
partial def TypeLattice.substitutedAncestors (ctx : TypeLattice)
    (name : String) (args : List HighTypeMd) : List HighTypeMd := Id.run do
  let mut out : List HighTypeMd := []
  let mut visited : Std.HashSet String := {}
  -- worklist of (composite name, its concrete args) to expand
  let mut work : List (String × List HighTypeMd) := [(name, args)]
  let mut fuel : Nat := 1024
  while !work.isEmpty && fuel > 0 do
    fuel := fuel - 1
    match work with
    | [] => pure ()
    | (curName, curArgs) :: rest =>
      work := rest
      match ctx.parentExprMap.get? curName with
      | none => pure ()  -- no parents (or not a known composite)
      | some (params, parentExprs) =>
        let subst : Std.HashMap String HighTypeMd :=
          (params.zip curArgs).foldl (fun m (p, a) => m.insert p.text a) {}
        for pe in parentExprs do
          let pe' := substTypeVars subst pe
          let key := highTypeKey pe'.val
          unless visited.contains key do
            visited := visited.insert key
            out := out ++ [pe']
            -- enqueue the substituted parent for transitive ancestors
            match pe'.val with
            | .UserDefined pn => work := work ++ [(pn.text, [])]
            | .Applied pb pargs =>
              match highBaseName? pb.val with
              | some pn => work := work ++ [(pn.text, pargs)]
              | none => pure ()
            | _ => pure ()
  return out

/-- Pure subtyping `<:`. Walks the `extending` chain for `CompositeType`
    (via `TypeLattice.ancestors`), unfolds `TypeAlias` to its target, and
    unwraps `ConstrainedType` to its base (both via `TypeLattice.unfold`),
    then falls back to structural equality via `highEq`.

    Used together with `isConsistent` to form `isConsistentSubtype`, which
    is what the bidirectional checker invokes at every check-mode boundary
    (rule `[⇐] Sub`). -/
def isSubtype (ctx : TypeLattice) (sub sup : HighTypeMd) : Bool :=
  let sub' := ctx.unfold sub
  let sup' := ctx.unfold sup
  match sub'.val, sup'.val with
  | .UserDefined subName, .UserDefined supName =>
    -- After unfolding, both sides are composites (or unresolved). A composite
    -- is a subtype of any type in its extending chain.
    (ctx.ancestors subName.text).contains supName.text || highEq sub' sup'
  -- GENERIC UPCAST, REMAP-AWARE and SOUND. `C<args> <: P<pargs>` iff some
  -- fully-SUBSTITUTED ancestor type of `C<args>` equals the target `sup`. Critically, the
  -- comparison is against an ALREADY-SUBSTITUTED ancestor (`substitutedAncestors` applies
  -- the `extends` remap/concretization), so:
  --   • `P2<int,bool> extends Pair<B,A>` ⇒ ancestor `Pair<bool,int>`; `<: Pair<bool,int>`
  --     succeeds, `<: Pair<int,bool>` (the reverted bug) FAILS.
  --   • `Box<bool> extends Base<int>` ⇒ ancestor `Base<int>`; `<: Base<bool>` FAILS.
  -- Args are INVARIANT — `highEq` against the substituted ancestor is exact, so a wrong
  -- instantiation (`Box<int> <: Base<bool>`) and an unrelated type both fail. This is the
  -- arm whose earlier non-substituting version was unsound; the substitution closes it.
  | .Applied subBase subArgs, _ =>
    (match highBaseName? subBase.val with
     | some subName => (ctx.substitutedAncestors subName.text subArgs).any (fun anc => highEq anc sup')
     | none => false)
    || highEq sub' sup'
  | _, _ => highEq sub' sup'

/- ### Variance policy (covers `isSubtype` and `isConsistent`)
   The MUTABLE-collection constructors are INVARIANT by design: `isConsistent`
   bottoms out in `highEq` (structural equality) for `TSet`, `TMap`,
   `Applied`, `Pure`, and `Intersection`. So `TSet Unknown ~
   TSet TInt` is FALSE — `Unknown` is a wildcard only at the TOP of a type,
   never under a constructor. This is intentional: `TSet` / `TMap` are MUTABLE
   collections, where covariance would be unsound; if you don't know the
   element type, write a bare `Unknown`, not `TSet Unknown`.

   `MultiValuedExpr` and `Applied` RECURSE element-wise (consistency, not
   equality) rather than bottoming out in `highEq`:
   - `MultiValuedExpr` is a transient tuple of independent procedure-output
     values matched against multi-assignment targets, so per-element consistency
     (letting an `Unknown` output flow into one slot) is correct, not unsound.
   - `Applied` (generics) recurses element-wise in `isConsistent` so a concrete
     `Box<int>` argument can satisfy a `Box<T>` parameter (the inner `int`/`.TVar T`
     pairing reaches the `.TVar` wildcard). The args stay INVARIANT between two
     CONCRETE instantiations — `Box<int> ~ Box<bool>` still FAILS on `int`/`bool`,
     so this is not covariance, just wildcard-penetration for `.TVar`/`Unknown`.
     For SUBTYPING, `isSubtype` additionally relates `C<args> <: P<pargs>` via
     `substitutedAncestors` (the `extends` chain with the type-arg remap applied);
     args there are likewise invariant (compared against the already-substituted
     ancestor). True per-constructor parametric variance remains deferred.

   `Pure b` is invariant today, but it is the one constructor where covariance
   would be SOUND and desirable — it is the immutable value-view of a composite,
   and immutability is exactly the condition that makes covariance safe.
   TODO: Pure could be covariant once it matters (immutable value-view ⇒ covariance is sound)

   `Intersection` is NOT a variance question: `A & B` has lattice structure
   (`A & B <: A`, `A & B <: B`, etc.) that is not modeled, and the current
   `highEq` arm zips element-wise IN DECLARATION ORDER, so `A & B ≠ B & A` even
   though intersection is conceptually unordered. Known limitation, to fix with
   bespoke subtyping rules when intersections become live. -/
/-- Consistency `~` (Siek–Taha): the symmetric gradual relation. `Unknown`
    is the dynamic type and is consistent with everything; otherwise
    structural equality after unfolding aliases / constrained types.

    `TCore _` is also treated as gradual — consistent with everything —
    pending its removal from the type representation.
    `MultiValuedExpr` is checked element-wise so the same equivalence
    propagates through procedure-output tuples.

    Used directly by `[⇒] Op-Eq`, where the operand types must be mutually
    consistent (no subtype direction is privileged), and as one half of
    `isConsistentSubtype`. -/
def isConsistent (ctx : TypeLattice) (a b : HighTypeMd) : Bool :=
  -- `MultiValuedExpr` is checked element-wise *before* unfolding so elements
  -- remain demonstrable subterms of `a`/`b`. `unfold` is `partial`, and is in
  -- any case the identity on `MultiValuedExpr`, so this loses no precision.
  match _a: a.val, _b: b.val with
  | .MultiValuedExpr ts1, .MultiValuedExpr ts2 =>
    ts1.length == ts2.length &&
      (ts1.attach.zip ts2).all (fun (t1, t2) => isConsistent ctx t1.1 t2)
  -- A generic application `C<τ…>` is checked element-wise *before* unfolding (like
  -- `MultiValuedExpr`), so the args remain demonstrable subterms for termination and
  -- `unfold` (identity on `.Applied`) loses no precision. This is what lets a concrete
  -- `Box<int>` argument satisfy a `Box<T>` parameter: the bases match by consistency and
  -- the inner `int`/`.TVar T` pairing hits the `.TVar` wildcard below. Without this arm
  -- `.Applied` falls to the invariant structural `highEq`, where `int` vs `T` is false —
  -- so the `.TVar` wildcard (which only fires at the TOP of a type) never reaches the
  -- nested type var and every generic-composite-param call is spuriously rejected. (The
  -- recursion keeps full strictness between two CONCRETE instantiations: `Box<int>` vs
  -- `Box<bool>` still fails on the inner `int`/`bool`.)
  | .Applied base1 args1, .Applied base2 args2 =>
    args1.length == args2.length && isConsistent ctx base1 base2 &&
      (args1.attach.zip args2).all (fun (t1, t2) => isConsistent ctx t1.1 t2)
  -- Collection types recurse element-wise *before* unfolding, for the same reason as
  -- `.Applied`: so the `.TVar` wildcard reaches a nested type var (a `Map K V` parameter
  -- satisfied by a concrete `Map int bool` argument). Recursion only — concrete-vs-concrete
  -- stays strict (`Map int bool` vs `Map int int` fails on the value leaf). `.TSet` mirrors
  -- `.TMap` for symmetry with the other type traversals (`highEq`, `substTypeVars`), though
  -- `Set` has no surface-Laurel production today, so only the `.TMap` arm is exercised.
  | .TMap k1 v1, .TMap k2 v2 => isConsistent ctx k1 k2 && isConsistent ctx v1 v2
  | .TSet e1, .TSet e2 => isConsistent ctx e1 e2
  -- A BARE composite name and its INSTANTIATION are consistent when the base names
  -- match: `Box ~ Box<int>`. This is the legacy `new C` correlation form — `var b:
  -- Box<int> := new Box` synthesizes the allocation as `.UserDefined "Box"` (no args;
  -- the monomorphizer recovers `int` from the declared `Box<int>` type), so the
  -- assignment check sees `.UserDefined Box` vs `.Applied Box [int]`. All instantiations
  -- of a generic composite erase to the SAME Core `Composite` type, so distinguishing
  -- them by arity here would reject sound legacy programs ("expected 'Box', got 'Box'").
  | .UserDefined n1, .Applied b2 _ | .Applied b2 _, .UserDefined n1 =>
    (match b2.val with | .UserDefined n2 => n1.text == n2.text | _ => false)
  | _, _ =>
    let a' := ctx.unfold a
    let b' := ctx.unfold b
    match a'.val, b'.val with
    | .Unknown, _ | _, .Unknown => true
    | .TCore _, _ | _, .TCore _ => true
    -- A type VARIABLE is consistent with everything (like `Unknown`): an
    -- un-monomorphized `T` is a not-yet-known concrete type. Polymorphic code
    -- (`idp<T>(x:T)` called at `int`; a generic composite field `val:T` written
    -- with an `int`) is type-checked at the INITIAL resolution where `T` is still
    -- `.TVar` — before monomorphization erases it or CallElim freshens it. Without
    -- this arm the gradual checker would reject every polymorphic use with a
    -- spurious "expected 'T', got 'int'" and (since any non-warning resolution
    -- diagnostic gates translation) block ALL polymorphic programs. This is the
    -- gradual-typing-correct treatment, mirroring the `Unknown` wildcard.
    | .TVar _, _ | _, .TVar _ => true
    | _, _ => highEq a' b'
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    all_goals (first | (cases base1; term_by_mem) | (cases t1; term_by_mem))

/-- Consistent subtyping: `∃ R. sub ~ R ∧ R <: sup`. For our flat lattice
    this collapses to `sub ~ sup ∨ sub <: sup` — the standard collapse.

    Used by rule `[⇐] Sub` (and every bespoke check rule). That single
    choice is what makes the system *gradual*: an expression of type
    `Unknown` (a hole, an unresolved name, a `Hole _ none`) flows freely
    into any typed slot, and any expression flows freely into a slot of
    type `Unknown`. Strict checking is applied between fully-known types
    only.

    A previous iteration was synth-only with two *bivariantly-compatible*
    wildcards: `Unknown` and `UserDefined`. The `UserDefined` carve-out was
    load-bearing: no assignment, call argument, or comparison involving a
    user type was ever rejected. The bidirectional design retires that
    carve-out — user-defined types are now a regular participant in `<:`,
    with `isSubtype` walking inheritance chains and unwrapping aliases
    and constrained types to deliver real checking on user-defined code. -/
def isConsistentSubtype (ctx : TypeLattice) (sub sup : HighTypeMd) : Bool :=
  isConsistent ctx sub sup || isSubtype ctx sub sup

def HighType.isBool : HighType → Bool
  | TBool => true
  | _ => false

/-- Return the constructor name of a `StmtExprMd` as a `String`. -/
def StmtExpr.constructorName (e : StmtExpr) : String :=
  match e with
  | .IfThenElse .. => "IfThenElse"
  | .Block .. => "Block"
  | .While .. => "While"
  | .Exit .. => "Exit"
  | .Return .. => "Return"
  | .LiteralInt .. => "LiteralInt"
  | .LiteralBool .. => "LiteralBool"
  | .LiteralString .. => "LiteralString"
  | .LiteralDecimal .. => "LiteralDecimal"
  | .LiteralBv .. => "LiteralBv"
  | .Var .. => "Var"
  | .Assign .. => "Assign"
  | .PureFieldUpdate .. => "PureFieldUpdate"
  | .StaticCall .. => "StaticCall"
  | .PrimitiveOp .. => "PrimitiveOp"
  | .New .. => "New"
  | .This => "This"
  | .ReferenceEquals .. => "ReferenceEquals"
  | .AsType .. => "AsType"
  | .IsType .. => "IsType"
  | .InstanceCall .. => "InstanceCall"
  | .Quantifier .. => "Quantifier"
  | .Assigned .. => "Assigned"
  | .Old .. => "Old"
  | .Fresh .. => "Fresh"
  | .Assert .. => "Assert"
  | .Assume .. => "Assume"
  | .ProveBy .. => "ProveBy"
  | .ContractOf .. => "ContractOf"
  | .Abstract => "Abstract"
  | .All => "All"
  | .Hole .. => "Hole"
  | .IncrDecr .. => "IncrDecr"

/-- Build an expression that reads back the value of a variable reference.

    The result is always a `Var` expression that evaluates to the variable's
    value. A `Declare` is read back as a `Local` reference to the declared name
    (so a declaration target reads back the variable it introduces). -/
def Variable.toReadbackExpr : Variable → StmtExpr
  | .Local name => .Var (.Local name)
  | .Declare param => .Var (.Local param.name)
  | .Field target fieldName => .Var (.Field target fieldName)

/-- Source-preserving read-back expression for a `VariableMd`
    (see `Variable.toReadbackExpr`). -/
def VariableMd.toReadbackExpr (v : VariableMd) : StmtExprMd :=
  ⟨ v.val.toReadbackExpr, v.source ⟩

/-- Check whether a single modifies entry is the wildcard (`*`). -/
def StmtExprMd.isWildcard (m : StmtExprMd) : Bool := match m.val with | .All => true | _ => false

/-- Check whether a modifies list contains the wildcard (`*`). -/
def hasModifiesWildcard (modifiesExprs : List StmtExprMd) : Bool :=
  modifiesExprs.any StmtExprMd.isWildcard

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
  /-- Type parameters, e.g. `T` in `composite Box<T> { ... }`. Empty for
      monomorphic composites (default keeps existing sites compiling). -/
  typeArgs : List Identifier := []
  /-- Composite types this type extends, as type references. Usually a bare name
      (`.UserDefined Base`), but a generic composite may extend a generic parent at an
      instantiation (`Box<T> extends Base<T>` → `.Applied (UserDefined Base) [TVar T]`).
      Consumers that only need the parent NAME peel the base via `highBaseName?`.
      The type hierarchy affects `IsType`/`AsType` results. -/
  extending : List HighTypeMd
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
  /-- Identifier for the auto-generated tester function (e.g. `IntList..isNil`).
      Populated with a `uniqueId` during resolution. -/
  testerName : Identifier := mkId ""

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

/-- Build a `TypeLattice` from a list of `TypeDefinition`s.
    Aliases populate `unfoldMap` with their target; constrained types populate
    it with their base; composites populate `extendingMap` with their direct
    parents. Datatypes contribute nothing — they're nominal and irreducible. -/
def TypeLattice.ofTypes (types : List TypeDefinition) : TypeLattice :=
  types.foldl (init := {}) fun ctx td =>
    match td with
    | .Alias ta => { ctx with unfoldMap := ctx.unfoldMap.insert ta.name.text ta.target }
    | .Constrained ct => { ctx with unfoldMap := ctx.unfoldMap.insert ct.name.text ct.base }
    | .Composite c =>
      -- `extending` is now `List HighTypeMd`; the subtype lattice keys on parent NAME
      -- (an instantiation `Base<T>` and `Base` share the same ancestor chain), so peel
      -- the base name. A parent with no nameable base (shouldn't occur for `extends`)
      -- is dropped from the chain rather than crashing.
      -- ALSO record the child's params + verbatim parent EXPRESSIONS so the remap survives
      -- for `substitutedAncestors`. `extendingMap` (name-only) is kept for
      -- the name-walk consumers.
      { ctx with
        extendingMap := ctx.extendingMap.insert c.name.text (c.extending.filterMap (fun e => (highBaseName? e.val).map (·.text))),
        parentExprMap := ctx.parentExprMap.insert c.name.text (c.typeArgs, c.extending) }
    | .Datatype _ => ctx

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

end -- public section

end Laurel
end Strata
