/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.DL.Imperative.MetaData
public import Strata.Languages.Core.Expressions
import Strata.Util.Tactics
public import StrataDDM.Util.Decimal
public import Strata.Util.FileRange
open StrataDDM

/-
Documentation for Laurel can be found in docs/verso/LaurelDesignerGuide.lean
(language definition) and docs/verso/LaurelImplementorGuide.lean
(translation to Core).

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
  source : FileRange := .unknown
  deriving Repr

instance : Inhabited Identifier where
 default := { text := "defaultIdentifier" }

instance : ToString Identifier where
  toString id := id.text

instance : Coe String Identifier where
  coe s := { text := s }

def mkId (name: String): Identifier := { text := name }

/-- Extract the unique ID, or fail with a descriptive message when unresolved. -/
def Identifier.getUniqueId (id : Identifier) : Except String Nat :=
  match id.uniqueId with
  | some n => .ok n
  | none => .error s!"identifier '{id.text}' missing uniqueId (not resolved)"

/-- Compare two identifiers by uniqueId. Throws if either is unresolved. -/
def Identifier.sameId (a b : Identifier) : Except String Bool :=
  match a.uniqueId, b.uniqueId with
  | some x, some y => .ok (x == y)
  | none, _ => .error s!"identifier '{a.text}' missing uniqueId (not resolved)"
  | _, none => .error s!"identifier '{b.text}' missing uniqueId (not resolved)"

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
Name of the built-in wrapper procedure implementing an `Operation`.

Operators are not a distinct kind of expression: `x + y` is a `StaticCall` to
the overloaded procedure `$add`, declared in `CoreDefinitionsForLaurel` and
prepended to every program. The `$` prefix puts these in Laurel's reserved
namespace so they cannot collide with a user-defined `add`.

Each wrapper is a thin transparent procedure delegating to a type-specific
external (`intAdd`, `realAdd`, …) that `LaurelToCoreSchemaPass` recognizes and
lowers to the corresponding Core operator. Overload resolution picks the
wrapper matching the argument types, which is why the wrappers must share one
name per operator while the externals they call do not.
-/
def Operation.procName : Operation → String
  | .Eq => "$eq"                | .Neq => "$neq"
  | .And => "$and"              | .Or => "$or"
  | .Not => "$not"              | .Implies => "$implies"
  | .AndThen => "$andThen"      | .OrElse => "$orElse"
  | .Neg => "$neg"              | .Add => "$add"
  | .Sub => "$sub"              | .Mul => "$mul"
  | .Div => "$div"              | .Mod => "$mod"
  | .DivT => "$divT"            | .ModT => "$modT"
  | .Lt => "$lt"                | .Leq => "$le"
  | .Gt => "$gt"                | .Geq => "$ge"
  | .StrConcat => "$strConcat"

/-- Inverse of `Operation.procName`: recognize a built-in operator wrapper by
    name. Used by the pretty-printer to print `$add(x, y)` back as `x + y`, so
    that a parsed program round-trips. -/
def Operation.ofProcName? : String → Option Operation
  | "$eq" => some .Eq                | "$neq" => some .Neq
  | "$and" => some .And              | "$or" => some .Or
  | "$not" => some .Not              | "$implies" => some .Implies
  | "$andThen" => some .AndThen      | "$orElse" => some .OrElse
  | "$neg" => some .Neg              | "$add" => some .Add
  | "$sub" => some .Sub              | "$mul" => some .Mul
  | "$div" => some .Div              | "$mod" => some .Mod
  | "$divT" => some .DivT            | "$modT" => some .ModT
  | "$lt" => some .Lt                | "$le" => some .Leq
  | "$gt" => some .Gt                | "$ge" => some .Geq
  | "$strConcat" => some .StrConcat
  | _ => none

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
  source : FileRange
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
  /-- A generic type application, e.g. `List<Int>`. -/
  | Applied (base : AstNode HighType) (typeArguments : List (AstNode HighType))
  /-- An intersection of types. Used for implicit intersection types, e.g. `Scientist & Scandinavian`. -/
  | Intersection (types : List (AstNode HighType))
  /-- Bitvector type of a given width. -/
  | TBv (size : Nat)
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

/-- How a pre/postcondition should be lowered.

    A condition has a "natural assert" site and a "natural assume" site that
    differ between pre- and postconditions:
    - precondition: asserted at call sites, assumed in the implementation body.
    - postcondition: asserted at the end of the body, assumed after calls.

    The mode selects which of those lowerings are emitted.

    Laurel authors only need to use `ConditionMode.Both`. The other options
    (`Assert` and `Assume`) are used by Laurel compilation steps. -/
inductive ConditionMode where
  | Assert | Assume | Both
  deriving BEq

/-- Whether the condition's "assert" lowering should be emitted. -/
def ConditionMode.doesAssert : ConditionMode → Bool
  | .Assert | .Both => true
  | .Assume => false

/-- Whether the condition's "assume" lowering should be emitted. -/
def ConditionMode.doesAssume : ConditionMode → Bool
  | .Assume | .Both => true
  | .Assert => false

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
  /-- Optional termination measure for recursive procedures. -/
  decreases : Option (AstNode StmtExpr) -- optionally prove termination
  /-- The procedure body: transparent, opaque, or abstract. -/
  body : Body
  /-- Optional trigger for auto-invocation. When present, the translator also emits an axiom
      whose body is the ensures clause universally quantified over the procedure's inputs,
      with this expression as the SMT trigger. -/
  invokeOn : Option (AstNode StmtExpr) := none
  /-- When `true`, the producer marked this procedure as an entry point for
      concrete interpretation (`laurelInterpret`). It has no effect on
      verification.

      Distinct from `Core.EntryPoint` (the verifier's `.main | .roots | .all`
      target selector) — this marker drives the concrete interpreter only. -/
  isInterpretEntry : Bool := false
  /-- Axioms to emit alongside this procedure. Populated by the contract pass from
      `invokeOn` and ensures clauses. -/
  axioms : List (AstNode StmtExpr) := []
  /-- Optional declared exception type: the single type this procedure may
      throw, drawn from the front end's own hierarchy (no built-in upper bound).
      Catch-or-declare *is* enforced against it, by `validateExceptionEscapes`
      during resolution (only a subtype of this type may escape; a procedure with
      no `throwsType` may let nothing escape). Not lowered until
      `EliminateExceptions`, which turns it into the `Err` argument of the
      procedure's `Result<Val, Err>`. -/
  throwsType : Option (AstNode HighType) := none
  /-- The name the `throws (e: T)` clause binds to the thrown value. Scoped over the
      `throwsOn` blocks' postconditions — not over their guards, which are pre-state
      conditions evaluated on entry.

      Paired with `throwsType`: the grammar has a single `throws` op, which carries
      both, so a parsed procedure has either both fields or neither. Code that only
      needs to know whether a procedure throws should therefore test `throwsType`. -/
  throwsBinding : Option Identifier := none
  /-- Exceptional behavior cases (`throwsOn C { ensures … modifies … }`), one per
      case. See `ThrowsOnBlock`. Empty means the procedure states nothing about
      its throwing paths beyond the declared `throwsType`. -/
  throwsOn : List ThrowsOnBlock := []

/--
A typed parameter for a procedure.
-/
structure Parameter where
  /-- The parameter name. -/
  name : Identifier
  /-- The parameter type. -/
  type : AstNode HighType

/--
A parameter with an *optional* type annotation, used for local variable
declarations (`Variable.Declare`).

This mirrors `Parameter` but lets the annotation be omitted: `type` is `some T`
for an annotated declaration (`var x : T`, `var x : T := e`) and `none` for an
unannotated one (`var x`, `var x := e`). An unannotated declaration is a
transient form produced by the parser; the resolution pass recovers a concrete
type — synthesized from the initializer for `var x := e`, or `Unknown` (with a
diagnostic) for the annotation-less, initializer-less `var x` — and fills in
`some T`. Every declaration reaching the post-resolution passes therefore
carries `some`.
-/
structure Parameter? where
  /-- The parameter name. -/
  name : Identifier
  /-- The parameter's optional type annotation. -/
  type : Option (AstNode HighType)

/--
A condition with an optional human-readable summary.
Used for assertions, preconditions, and postconditions.
-/
structure Condition where
  /-- The boolean condition expression. -/
  condition : AstNode StmtExpr
  /-- Optional human-readable summary describing the property being checked. -/
  summary : Option String := none
  /-- How this condition is lowered (checked, assumed, or both). The default
      `Both` is the ordinary contract behavior. `Assume` corresponds to a *free*
      condition: a free precondition is assumed by the implementation but not
      asserted at call sites, and a free postcondition is assumed upon return
      from calls but not checked on exit from implementations. -/
  mode : ConditionMode := ConditionMode.Both

/--
A `catch` clause: a mandatory binding bound to the caught value (typed at
the least common ancestor of the exception types thrown in the `try` body), an
optional predicate guard, and a handler body. A `Try` holds an ordered list of
these; clauses are tried in order, first-match-wins, and an absent predicate is
a catch-all. Type dispatch is written as a guard, e.g. `catch e when e is T`.
See the Exceptions section of the Laurel User Guide.
-/
structure CatchClause where
  /-- The identifier bound to the caught value (typed at the least common
      ancestor of the exception types thrown in the `try` body). -/
  binding : Identifier
  /-- Optional guard predicate (checked at `TBool`); `none` is a catch-all. -/
  predicate : Option (AstNode StmtExpr) := none
  /-- The handler body, run when this clause matches. -/
  body : AstNode StmtExpr
  /-- The binding's resolved type: the least common ancestor of the exception
      types thrown in the `try` body (computed by `Check.tryCatch`). `Unknown`
      before resolution. Carried on the node so it survives Phase 1 into Phase 2
      (the `refToDef` builder) and the `EliminateExceptions` pass, which types
      the per-`try` `$exc_<i>` local at it. -/
  bindingType : AstNode HighType := { val := .Unknown, source := .unknown }

/--
An exceptional *behavior case*: `throwsOn C { ensures … modifies … }`.

`guard` is a pre-state condition that **forces** this throw. The case means

```
C ==> (Result..isBad($result) ∧ <the block's postconditions>)
```

with the block's frame applying on that path only. So a caller who establishes
`C` can conclude the call throws (and what then holds of the thrown value), and
one who refutes every guard can conclude it does not.

A procedure carries a list of these. Because the blocks are independent, a
per-thrown-type frame is expressible — one block per case — rather than every
exceptional frame being unioned into a single clause.

`ModifiesClauses` additionally emits a checked
`Result..isBad($result) ==> (C₁ ∨ … ∨ Cₙ)` for a procedure that has an
implementation, so a throwing path matching no guard is rejected rather than
silently left unframed. It is not emitted for a bodiless procedure, where there
is nothing to check it against and callers would be handed an unverified
promise. See the Exceptions section of the Laurel User Guide.
-/
structure ThrowsOnBlock where
  /-- The pre-state guard `C` (checked at `TBool`). The thrown value is *not* in
      scope here: the guard is evaluated on entry, before any throw. -/
  guard : AstNode StmtExpr
  /-- Exceptional postconditions scoped to this case. The thrown value is in
      scope under the name bound by the procedure's `throws (e: T)` clause. -/
  postconditions : List Condition
  /-- This case's exceptional frame: when it fires, only these locations may
      change. Empty means the case constrains no heap locations. -/
  modifies : List (AstNode StmtExpr)

/--
One frame of a procedure's `modifies` specification: when `guard` holds (or
unconditionally, when it is `none`), only `targets` may change.

Each group lowers to its own frame condition, so the grouping is semantic, not
cosmetic: targets in one group *union* (any of them may change), while separate
groups *conjoin* (each group's frame must hold whenever its guard does).

User syntax produces exactly one unguarded group — the plain `modifies` list.
Guards exist for the compilation passes: `EliminateExceptions` consumes a
`throwsOn` block by appending a group guarded on that case
(`Result..isBad(<carrier>) && C`), and re-guards the user's group on the normal
path (`Result..isGood(<carrier>)`). This is what lets the downstream frame
lowering (`ModifiesClauses`) stay agnostic to exceptions: it sees only
"guard implies frame", never a `throwsOn`. There is no *authored* syntax for a
guard — users never write one — but the pass-generated form round-trips: the
printer renders a guarded group as `modifies <targets> when <guard>`
(`modifiesWhenClause`), and the parser reads it back, so between-pass output
stays loadable as well as readable.
-/
structure ModifiesGroup where
  /-- The frame's targets: references (or `*`) that may change. -/
  targets : List (AstNode StmtExpr)
  /-- When the frame applies; `none` means always. -/
  guard : Option (AstNode StmtExpr) := none
  /-- Diagnostic summary for the frame this group lowers to. Set by the pass that
      created a guarded group, so a failed frame is reported in the vocabulary the
      author wrote (`throwsOn modifies clause`), not the pass's. -/
  summary : Option String := none

/--
The body of a procedure. A body can be transparent (with a visible
implementation), opaque (with a postcondition and optional implementation),
or abstract (requiring overriding in extending types).
-/
inductive Body where
  /-- A transparent body whose implementation is visible to callers. -/
  | Transparent (body : AstNode StmtExpr)
  /-- An opaque body with a postcondition, optional implementation, and modifies clause. Without an implementation the postcondition is assumed.

      Each `modifies` entry lists state the procedure may change; everything else
      on the heap is preserved. The legal forms, recognized by the downstream
      `ModifiesClauses` pass, are:
      - `modifies o` — a single object reference; any field of `o` may change.
      - `modifies s` — an object set; any field of any member of `s` may change.
      - `modifies o#f` — a single field of a single object; only field `f` of `o`
        may change (field-granular).
      - `modifies *` — the wildcard (`StmtExpr.All`); the procedure may change anything.

      A 'field of an object set' (e.g. `s#f`) is intentionally not yet supported:
      Laurel cannot yet construct set values, so there is no way to test it. -/
  | Opaque
      (postconditions : List Condition)
      (implementation : Option (AstNode StmtExpr))
      -- See the constructor doc above for the allowed `modifies` forms.
      (modifies : List ModifiesGroup)
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
  /-- A local variable declaration with a name and an optional type annotation (see `Parameter?`). -/
  | Declare (parameter : Parameter?)

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
    (postTest : Bool)
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
      Eliminated by the `EliminateIncrDecrAndCompoundAssign` pass before lifting imperative expressions. -/
  | IncrDecr (mode : IncrDecrMode) (op : IncrDecrOp) (target : AstNode Variable)
  /-- C-style compound assignment (`x += e`, `x -= e`, `x *= e`, `x /= e`, `x %= e`),
      plus `x ^= e` for string concatenation (Laurel uses `^` for concat, OCaml-style,
      not bitwise XOR). Lowers to `target := target op rhs` and yields the new value.
      The target must be a `Local` or `Field` `Variable`.
      Invariant: `op` is one of `Add`/`Sub`/`Mul`/`Div`/`Mod`/`StrConcat` — the only
      operators the concrete-to-abstract translator ever constructs here. Downstream
      sites may treat any other `Operation` as a `StrataBug`.
      Eliminated by the `EliminateIncrDecrAndCompoundAssign` pass before lifting imperative expressions. -/
  | CompoundAssign (op : Operation) (target : AstNode Variable) (rhs : AstNode StmtExpr)
  /-- Update a field on a pure (value) type, producing a new value. -/
  | PureFieldUpdate (target : AstNode StmtExpr) (fieldName : Identifier) (newValue : AstNode StmtExpr)
  /-- Call a static procedure by name with the given arguments.
      Primitive operators are calls too: `x + y` is a `StaticCall` to the
      built-in wrapper `$add`. See `Operation.procName`. -/
  | StaticCall (callee : Identifier) (arguments : List (AstNode StmtExpr))
  /-- Create new object (`new`). -/
  | New (ref : Identifier)
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
  /-- Assert a condition, generating a proof obligation. The optional summary is
      a human-readable description of the property being checked. -/
  | Assert (condition : AstNode StmtExpr) (summary : Option String)
  /-- Assume a condition, restricting the state space. -/
  | Assume (condition : AstNode StmtExpr)
  /-- Throw a value on the exceptional channel. The operand is unconstrained
      at the `throw` site; the thrown types are reconciled at each enclosing
      `catch` (typed at their least common ancestor) and against the procedure's
      declared `throwsType`. See the Exceptions section of the Laurel User Guide. -/
  | Throw (value : AstNode StmtExpr)
  /-- Structured exception handler: a `body`, an ordered list of `catch`
      clauses (tried first-match-wins), and an optional `finally` arm that runs on
      every exit path. See the Exceptions section of the Laurel User Guide. -/
  | Try (body : AstNode StmtExpr) (catches : List CatchClause) (finally? : Option (AstNode StmtExpr))
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
  | .CompoundAssign ..   => "compound assignment"
  | .PureFieldUpdate ..  => "field update"
  | .StaticCall ..       => "call"
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
  | .Throw ..            => "throw"
  | .Try ..              => "try"
  | .ProveBy ..          => "by"
  | .ContractOf ..       => "contractOf"
  | .Abstract            => "abstract"
  | .All                 => "all"
  | .Hole ..             => "hole"

@[expose] abbrev HighTypeMd := AstNode HighType
@[expose] abbrev StmtExprMd := AstNode StmtExpr
@[expose] abbrev VariableMd := AstNode Variable

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

/-! ### Names of the injected exception-result datatype

`EliminateExceptions` encodes a throwing procedure's two outcomes as a
`Result<Val, Err>` datatype (defined in `CoreDefinitionsForLaurel`, injected only
into programs that use exceptions). The pass *builds* that encoding, and every
downstream consumer meets it only through expressions the pass itself constructed
(`Result..isGood(<carrier>) ==> …` postconditions and `ModifiesGroup` guards), so
the member names live here for the passes that *print* or *inspect* datatype
members generally, not as a cross-pass contract about the carrier.

The carrier *output* is not named here at all. Its name is private to
`EliminateExceptions`, which references the carrier directly in everything it
emits — no downstream pass reconstructs it, so none can misread an unrelated
output that happens to be spelled the same way. It does have to stay distinct
from `resultOutputName`, the output the short `: T` return form mints for every
procedure: were they equal, both would claim one identifier in a throwing
procedure written `: T`, and the signature's `Result<…>` would contradict the
value type the body assigns; the pass freshens past taken names for exactly that
reason.

The member names are derived from the datatype, constructor, and field names
below, following the same convention as `DatatypeDefinition.testerName` and
`DatatypeDefinition.destructorName`, so renaming a constructor here updates its
tester too. A `#guard` next to the datatype definition checks these against the
definition itself. -/

/-- Name of the datatype encoding a throwing procedure's outcome. -/
def exnResultDatatypeName : String := "Result"

/-- Constructor for the normal-return outcome. -/
def exnResultGoodCtor : String := "Good"

/-- Constructor for the exceptional outcome. -/
def exnResultBadCtor : String := "Bad"

/-- Field of `exnResultGoodCtor`, carrying the returned value. -/
def exnResultValueField : String := "value"

/-- Field of `exnResultBadCtor`, carrying the thrown exception. -/
def exnResultErrField : String := "err"

/-- `Result..member` — a member (tester or destructor) of the result datatype. -/
private def exnResultMember (member : String) : String :=
  s!"{exnResultDatatypeName}..{member}"

/-- Tester for the normal-return outcome: `Result..isGood`. -/
def exnResultIsGood : String := exnResultMember s!"is{exnResultGoodCtor}"

/-- Tester for the exceptional outcome: `Result..isBad`. -/
def exnResultIsBad : String := exnResultMember s!"is{exnResultBadCtor}"

/-- Destructor reading the returned value: `Result..value`. -/
def exnResultValue : String := exnResultMember exnResultValueField

/-- Destructor reading the thrown exception: `Result..err`. -/
def exnResultErr : String := exnResultMember exnResultErrField

theorem AstNode.sizeOf_val_lt {t : Type} [SizeOf t] (e : AstNode t) : sizeOf e.val < sizeOf e := by
  cases e; grind

theorem Condition.sizeOf_condition_lt (c : Condition) : sizeOf c.condition < 1 + sizeOf c := by
  cases c; grind

theorem CatchClause.sizeOf_body_lt (c : CatchClause) : sizeOf c.body < 1 + sizeOf c := by
  cases c; grind

theorem CatchClause.sizeOf_predicate_lt (c : CatchClause) : sizeOf c.predicate < 1 + sizeOf c := by
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

/-- Build a provenance from a source location. -/
def fileRangeToProvenance (source : FileRange) : Provenance :=
  Provenance.ofSourceRange source.file source.range

/-- Build Core metadata from a source location. -/
def fileRangeToCoreMd (source : FileRange) : Imperative.MetaData Core.Expression :=
  Imperative.MetaData.ofProvenance (fileRangeToProvenance source)

/-- Build Core metadata from an AstNode's source location. -/
def astNodeToCoreMd (node : AstNode α) : Imperative.MetaData Core.Expression :=
  fileRangeToCoreMd node.source

/-- Build Core metadata from an Identifier's source location. -/
def identifierToCoreMd (id : Identifier) : Imperative.MetaData Core.Expression :=
  fileRangeToCoreMd id.source

/-- Create a Message from a source location and a message. -/
def diagnosticFromSource (source : FileRange) (msg : String) (type : MessageKind := .userError) : Message :=
  Message.withRange source msg type

instance : Inhabited StmtExpr where
  default := .Hole

instance : Inhabited (AstNode Variable) where
  default := { val := .Local default, source := default }

instance : Inhabited HighTypeMd where
  default := { val := HighType.Unknown, source := default }

instance : Inhabited StmtExprMd where
  default := { val := default, source := default }

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
  | HighType.Applied b1 args1, HighType.Applied b2 args2 =>
      highEq b1 b2 && args1.length == args2.length && (args1.attach.zip args2 |>.all (fun (a1, a2) => highEq a1.1 a2))
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

instance : BEq HighType where
  beq a b := highEq ⟨a, default⟩ ⟨b, default⟩


/-- The proof-relevant verdict of `coerce sub sup`: not just "is `sub <: sup`?" but
    *how* to realize the coercion. `coerce` returns `some verdict` exactly when the
    subtype holds (so `isConsistentSubtype := (coerce ..).isSome`), and the verdict
    tells the frontend's `realizeCoercion` which runtime term to insert. The five
    constructors are exactly the distinct realizer outputs — none collapses into another,
    because each maps to a DIFFERENT operation:

    | verdict     | when                                   | realizer must emit        |
    |-------------|----------------------------------------|---------------------------|
    | `refl`      | same type after unfold, or wildcard    | nothing (identity)        |
    | `upcast`    | nominal composite ≤ ancestor composite | nothing — SAME represn.   |
    | `widen T`   | numeric `int ≤ real/float64`           | `int_to_real` — subtype   |
    |             |                                        |   but DIFFERENT represn.  |
    | `inject A`  | concrete `A` ≤ dynamic-top `Any`       | box (`from_A`)            |
    | `project A` | dynamic-top `Any` ≤ concrete `A`       | unbox (`Any..as_A!`)      |

    Why NOT fewer cases:
    - `upcast` vs `widen`: both are subtyping (`int <: real` just like `Dog <: Animal`),
      but `upcast` is representation-preserving (a subclass reference already IS a
      superclass reference → identity), whereas `int` and `real` have different Core
      sorts, so `widen` needs the `int_to_real` conversion. Merging them and realizing
      as identity would hand Core an `int` in a `real` slot — malformed downstream.
    - `inject` vs `project`: opposite directions across the dynamic top — box vs unbox.
      They are NOT inverses the realizer can share: each carries the concrete type so the
      realizer picks the right (un)boxer (`from_int`/`from_Composite` vs `Any..as_int!`).
    - `widen`/`inject`/`project` all carry a `HighType` because the realizer needs the
      concrete source/target type to name the exact runtime function.

    Terminology note: `inject`/`project` follow Henglein's coercion calculus (injection
    `T!` into / projection `T?` out of the dynamic type), the standard names for gradual
    casts against a dynamic top. Truthiness is NOT a verdict here (it is not subtyping —
    `list` is not `<: bool`); it is a separate `toBool` hook fired only at boolean-context
    slots, so `coerce` stays an honest subtype judgment. -/
inductive Coercion where
  | refl
  | inject (source : HighType)
  | project (target : HighType)
  | upcast
  | widen (target : HighType)
  deriving Inhabited

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
  /-- Type names that are treated as the gradual/dynamic top type (consistent with everything).
      Set by language frontends (e.g. Python pipeline registers `"Any"` here). -/
  gradualTypes : Std.HashSet String := {}
  /-- Caller-supplied REALIZER for an abstract `Coercion` verdict: maps the verdict
      plus the term being coerced to a rewritten term carrying the concrete runtime
      coercion call. `none` (the default, for native Laurel) means "identity" — no
      coercion term is inserted. The Python frontend sets this to its box/unbox
      vocabulary. This REALIZES an already-decided verdict; it makes no subtyping
      decision, so it can never disagree with `coerce`. -/
  realizeCoercion : Option (Coercion → StmtExprMd → StmtExprMd) := none
  /-- Caller-supplied TRUTHINESS realizer: maps an operand's `HighType` plus the term to a
      bool-typed term (e.g. Python `str_to_bool`/`int_to_bool`/`Any_to_bool`). Truthiness is a
      boolean-CONTEXT coercion, NOT subtyping (`coerce Any bool` would be non-functional: unbox
      vs truthify), so it lives here as a separate hook applied at bool-context sites
      (if/assert/assume/bool-ops), not in `coerce`. `none` (native Laurel) = identity. -/
  toBool : Option (HighType → StmtExprMd → StmtExprMd) := none
  deriving Inhabited

/-- Unfold aliases and constrained types to their underlying type.
    Composites and primitives are returned unchanged. A `visited` set guards
    against cycles in the alias/constrained graph (already cycle-checked
    elsewhere, but keeps `unfold` safe to call independently).

    INVARIANT (AST producers): the primitive keywords `int`/`real`/`bool`/`string`
    must not be used as user type names. `unfold` canonicalizes a `UserDefined` with
    one of those names to the corresponding primitive, so a user/generated type so
    named would be silently reinterpreted. The Laurel parser already reserves these
    (`composite real { … }` fails to parse), so this only constrains non-parser AST
    producers (frontends / generated ASTs). -/
partial def TypeLattice.unfold (ctx : TypeLattice) (ty : HighTypeMd)
    (visited : Std.HashSet String := {}) : HighTypeMd :=
  match ty.val with
  | .UserDefined name =>
    -- A `UserDefined` whose name is a primitive keyword is that primitive. Some paths
    -- (e.g. a `TFloat64`/`real` name round-trip, or a stub type written by name) yield a
    -- phantom `UserDefined "real"` that must denote `TReal` — otherwise it collides with a
    -- genuine `TReal` (both print "real") and `coerce`/`highEq` wrongly reject them.
    match name.text with
    | "real" => { ty with val := .TReal }
    | "int" => { ty with val := .TInt }
    | "bool" => { ty with val := .TBool }
    | "string" => { ty with val := .TString }
    | _ =>
      if visited.contains name.text then ty
      else match ctx.unfoldMap.get? name.text with
        | some target => ctx.unfold target (visited.insert name.text)
        | none => ty
  -- Generic type application is *erased* to its base in Laurel's consistency /
  -- subtype relation: `Option<int>` relates as `Option`. (Resolution still
  -- checks the application's arity and well-formedness; only the deep
  -- type-argument check against instantiated parameters is left to Core, which
  -- has real polymorphic datatypes.) The args are preserved in the AST and
  -- dropped only here, in the type-relation layer — never in the Laurel→Core
  -- translation of a named-base application (`translateType` forwards them to
  -- the Core `.tcons`).
  | .Applied base _ => ctx.unfold base visited
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

/-- The least common ancestor (join) of a list of composite type names in the
    `extending` hierarchy: the unique most-specific type that is an ancestor of
    every name. Used to type a `catch` binding at the join of the exception types
    that reach it, so `e#field` is well-typed against the shared supertype
    without a downcast.

    Returns `none` when there is no common ancestor, or when the join is
    *ambiguous* — two or more equally-specific common ancestors, possible under
    multiple inheritance (`extends A, B`). Callers treat `none` as "type at
    `Unknown`"; the `try`/`catch` check in `Resolution` reports the
    missing/ambiguous join as an error there.

    A singleton list joins to itself (a type is its own most-specific ancestor). -/
def TypeLattice.commonAncestor (ctx : TypeLattice) (names : List String) : Option String :=
  match names with
  | [] => none
  | first :: rest =>
    -- Common ancestors: ancestors of `first` that are also ancestors of every
    -- other name.
    let common : List String :=
      (ctx.ancestors first).toList.filter fun a =>
        rest.all fun n => (ctx.ancestors n).contains a
    -- The join is the common ancestor that is itself a subtype of every common
    -- ancestor (i.e. the deepest). Unique ⇒ the join; otherwise ambiguous.
    let candidates := common.filter fun m =>
      common.all fun c => (ctx.ancestors m).contains c
    match candidates with
    | [m] => some m
    | _ => none

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
  | _, _ => highEq sub' sup'

/- ### Variance policy (covers `isSubtype` and `isConsistent`)
   All child-carrying constructors are INVARIANT by design: `isConsistent`
   bottoms out in `highEq` (structural equality) for `TSet`, `TMap`,
   `Applied`, and `Intersection`. So `TSet Unknown ~
   TSet TInt` is FALSE — `Unknown` is a wildcard only at the TOP of a type,
   never under a constructor. This is intentional: `TSet` / `TMap` are MUTABLE
   collections, where covariance would be unsound; if you don't know the
   element type, write a bare `Unknown`, not `TSet Unknown`.

   `MultiValuedExpr` is the SOLE exception that recurses (element-wise
   consistency, not equality). It is not a mutable container: it is a transient
   tuple of independent procedure-output values matched against multi-assignment
   targets, so per-element consistency (letting an `Unknown` output flow into
   one slot) is correct rather than unsound.

   `Applied` (generics) is invariant as the safe default for not-yet-designed
   parametric types; real variance is per-constructor and deliberately deferred.

   `Intersection` is NOT a variance question: `A & B` has lattice structure
   (`A & B <: A`, `A & B <: B`, etc.) that is not modeled, and the current
   `highEq` arm zips element-wise IN DECLARATION ORDER, so `A & B ≠ B & A` even
   though intersection is conceptually unordered. Known limitation, to fix with
   bespoke subtyping rules when intersections become live. -/
/-- Consistency `~` (Siek–Taha): the symmetric gradual relation. `Unknown`
    is the dynamic type and is consistent with everything; otherwise
    structural equality after unfolding aliases / constrained types.

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
  | _, _ =>
    let a' := ctx.unfold a
    let b' := ctx.unfold b
    let isGradual (t : HighType) := match t with
      | .Unknown => true
      | .UserDefined id => ctx.gradualTypes.contains id.text
      | _ => false
    if isGradual a'.val || isGradual b'.val then true
    else highEq a' b'
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    cases t1; term_by_mem

/-- Test whether a type is gradual (consistent with everything): `Unknown`, or a
    frontend-registered gradual `UserDefined` (e.g. Python `Any`). Mirrors the
    `isGradual` local inside `isConsistent` so `coerce`'s DECISION classifies
    identically. -/
private def TypeLattice.isGradualTop (ctx : TypeLattice) (t : HighType) : Bool :=
  match t with
  | .Unknown => true
  | .UserDefined id => ctx.gradualTypes.contains id.text
  | _ => false

/-- Test whether a type is the BOXABLE dynamic type — Python `Any`, a
    frontend-registered gradual `.UserDefined "Any"`. This is the SUBSET of
    `isGradualTop` that has a runtime representation you can inject into / project
    out of. `Unknown` is a gradual *wildcard* (a synth gap, a hole, an unresolved
    accessor, internal plumbing): it flows freely but carries NO box/unbox
    coercion, so a coercion against it is `refl` (identity) — coercing it would
    wrap concrete-typed prelude code (`ListAny..tail!` synth'd as `Unknown`) or
    heap plumbing in a bogus box/unbox. -/
private def TypeLattice.isDynamicBoxable (ctx : TypeLattice) (t : HighType) : Bool :=
  match t with
  | .UserDefined id => ctx.gradualTypes.contains id.text
  | _ => false

/-- PROOF-RELEVANT consistent subtyping: the ONE subtyping judgment. Returns the
    abstract `Coercion` verdict witnessing `sub ≤ sup`, or `none` when unrelated.
    Its `.isSome` matches the old boolean `isConsistentSubtype` (`isConsistent ∨
    isSubtype`) EXCEPT for numeric widening (int → real/float64), which is now gated
    on `realizeCoercion.isSome`: native Laurel (no realizer) rejects int in a real
    slot exactly as before, while a frontend that supplies a realizer accepts and
    realizes it. A check-mode site that rebuilds the term can obtain the witness and
    realize it. GENERIC: the verdict names the KIND of coercion
    (inject/project/upcast/widen/refl), never a runtime function; the frontend's
    `realizeCoercion` turns it into a concrete term.

    The gradual cases split by WHICH gradual: only the boxable dynamic type (`Any`)
    yields a runtime `inject`/`project`; a bare wildcard (`Unknown`) yields
    `refl` (it flows with no coercion). The DECISION (`.isSome`) is unchanged either
    way — both are `some` — so `isConsistentSubtype` matches the old boolean exactly.

    Case-for-case (mirrors `isConsistent ∨ isSubtype` for the decision):
    - `MultiValuedExpr` (proc-output tuples): delegate to `isConsistent`; `refl`.
    - equal after unfold → `refl`.
    - `sup` is `Any`, `sub` concrete → `inject sub'` (box into the dynamic type).
    - `sub` is `Any`, `sup` concrete → `project sup'` (unbox/downcast out of it).
    - either side a bare wildcard (`Unknown`) → `refl` (gradual, no runtime op).
    - both `UserDefined` with `sub`'s ancestors ∋ `sup` → `upcast` (nominal). -/
def coerce (ctx : TypeLattice) (sub sup : HighTypeMd) : Option Coercion :=
  match sub.val, sup.val with
  | .MultiValuedExpr _, .MultiValuedExpr _ =>
    if isConsistent ctx sub sup then some .refl else none
  | _, _ =>
    let sub' := ctx.unfold sub
    let sup' := ctx.unfold sup
    let subBoxable := ctx.isDynamicBoxable sub'.val
    let supBoxable := ctx.isDynamicBoxable sup'.val
    -- `Unknown` is the only PURE wildcard: a synth gap / hole / unresolved accessor
    -- with no runtime form, so a coercion against it is `refl` (it flows freely, no
    -- box/unbox). A concrete container type like `ListAny`/`DictStrAny` (a
    -- `UserDefined` NOT in `gradualTypes`) is NOT a wildcard — it is a real type that
    -- boxes/unboxes against `Any` (`from_ListAny`/`Any..as_ListAny!`). Distinguishing
    -- them here is what lets `Any ↔ ListAny` insert a witness while `Any ↔ <hole>`
    -- stays `refl`.
    let isWildcard (t : HighType) : Bool := match t with | .Unknown => true | _ => false
    if subBoxable && supBoxable then some .refl                  -- Any ↔ Any
    else if isWildcard sub'.val || isWildcard sup'.val then some .refl  -- wildcard: no op
    else if supBoxable then some (.inject sub'.val)              -- concrete → Any (box)
    else if subBoxable then some (.project sup'.val)             -- Any → concrete (unbox)
    else if highEq sub' sup' then some .refl
    else match sub'.val, sup'.val with
      -- Numeric widening: an `int` flows into a `real`/`float64` slot (e.g. `total: float = 0`).
      -- Legitimate in Python (int <: float); realized by `int_to_real`.
      -- Option A (Heimdall blocking finding): only produce a widen verdict when a realizer is
      -- available to actually insert the int_to_real conversion. Native Laurel supplies
      -- realizeCoercion = none, so it still rejects int in a real slot (behavior-neutral); a
      -- widen verdict nobody can realize is exactly `none`.
      | .TInt, .TReal => if ctx.realizeCoercion.isSome then some (.widen .TReal) else none
      | .TInt, .TFloat64 => if ctx.realizeCoercion.isSome then some (.widen .TFloat64) else none
      | .UserDefined subName, .UserDefined supName =>
        if (ctx.ancestors subName.text).contains supName.text then some .upcast else none
      -- Gradual types cannot reach here: wildcards and boxable gradual UserDefineds are consumed
      -- by the guards above (isWildcard / subBoxable / supBoxable) on the SAME unfolded values
      -- this branch tests, so isGradualTop is always false at this point. (AutoSDE f-362a2f95.)
      | _, _ => none

/-- Consistent subtyping: `∃ R. sub ~ R ∧ R <: sup`. DERIVED from the
    proof-relevant `coerce` so the yes/no answer and the inserted coercion can
    never disagree (ONE judgment). Used by rule `[⇐] Sub` and every bespoke check
    rule. That single choice is what makes the system *gradual*: an expression of
    type `Unknown` (a hole, an unresolved name, a `Hole _ none`) flows freely into
    any typed slot, and any expression flows freely into a slot of type `Unknown`. -/
def isConsistentSubtype (ctx : TypeLattice) (sub sup : HighTypeMd) : Bool :=
  (coerce ctx sub sup).isSome

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
  | .Throw .. => "Throw"
  | .Try .. => "Try"
  | .ProveBy .. => "ProveBy"
  | .ContractOf .. => "ContractOf"
  | .Abstract => "Abstract"
  | .All => "All"
  | .Hole .. => "Hole"
  | .IncrDecr .. => "IncrDecr"
  | .CompoundAssign .. => "CompoundAssign"

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
A field in a composite type, also used for file-scope globals (which resolution
registers as fields of the reserved `$static` owner). Fields declare their
name, mutability, and type.
Mutability affects what permissions are needed to access the field.
-/
structure Field where
  /-- The field name. -/
  name : Identifier
  /-- Whether the field is mutable. Mutable fields require write permission. -/
  isMutable : Bool
  /-- The field's type. -/
  type : HighTypeMd
  initializer : Option StmtExprMd := none

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
      { ctx with extendingMap := ctx.extendingMap.insert c.name.text (c.extending.map (·.text)) }
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

/-- Reserved internal name of a function's anonymous (short `: T`) return
    output. The leading `$` follows Strata's reserved-name convention and
    cannot be written as a surface identifier, so user parameters/locals named
    `result` never collide with the return value. To refer to the return value
    explicitly, use the named-return form `returns (r: T)`. -/
def resultOutputName : String := "$result"

/-- Reserved prefix stamped onto a call site whose overload resolution failed
    (no overload matched, or the call was ambiguous). The `UniqueOverloadNames`
    pass renames every overloaded definition away, so an unrewritten call site
    would otherwise re-resolve to a spurious *'<name>' is not defined* error.
    The marker lets re-resolution recognize the site and stay silent. -/
def overloadFailurePrefix : String := "$ovFail$"

/-- Rename a call site to the reserved overload-failure marker. -/
def overloadFailureName (name : Identifier) : Identifier :=
  { name with text := overloadFailurePrefix ++ name.text }

end -- public section

end Laurel
end Strata
