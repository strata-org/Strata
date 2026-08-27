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
    Carries an optional unique ID, filled in by the resolution pass (`none` before it runs). -/
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
Primitive operations available in Laurel expressions (each constructor is
documented individually below).

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
The type system for Laurel programs (each constructor is documented
individually below). Two constructors are internal, not surface types:
`Unknown` (resolution-error recovery / gradual wildcard) and `MultiValuedExpr`
(multi-output-call results).
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

/-- Whether a procedure is an ordinary procedure or a coroutine. -/
inductive ProcedureKind where
  | Regular
  | Coroutine
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

The `guard` field is a stand-in for set-valued modifies expressions. A modifies
clause is meant to accept an arbitrary expression; with set values, a
conditional frame would be written as the ordinary expression
`if guard then {x} else {}` and would need no dedicated field. Laurel has no
set type yet, so the guard rides in a field of its own. Once sets exist, this
structure is expected to simplify to a single set-valued target expression
plus `summary`:
`structure ModifiesClause where target : AstNode StmtExpr; summary : Option String`.
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
  /-- Refer to the value of `value` at an earlier program point.

      `label?` names *which* earlier state:
      * `none` — the procedure's native pre-state (Core's two-state `old`). This
        is the only form on the regular path; surface `old(e)` produces it.
      * `some h` — a named earlier state `h`, so `old` reads that state rather
        than the procedure entry state. `h` is bound either by a `Snapshot h`
        earlier in the body or by a threaded `Heap` parameter. -/
  | Old (value : AstNode StmtExpr) (label? : Option Identifier := none)
  /-- Coroutine-only: refer to the value of `value` at the start of the
      *current* coroutine step. Surface form: `oldGuarantee(value)`.

      Outside a coroutine body it is a resolution error. The lowering depends on
      the path:
      * **Body path** — the start-of-step heap is the previous yield's
        post-havoc snapshot (or procedure entry for the first yield), so it
        lowers to a labeled `Old value (some $old_heap)` reading the
        start-of-step `Snapshot` — the same lowering as an implicit `old(...)`
        inside a `guarantees` clause.
      * **Caller path** — the start-of-step heap is `resume`'s native entry
        state (`H2`), so it lowers to a plain `Old value` (no label) that
        push-old distributes onto the inout `$heap`.

      The user uses this in body asserts and loop invariants where the
      framework needs to relate the current heap to the previous yield's
      resume point. -/
  | OldGuarantee (value : AstNode StmtExpr)
  /-- Coroutine-only: the `old` state of a two-state `relies R(old, now)`
      — the heap at the coroutine's most recent suspension (`H1`). Surface
      form: `oldRelies(value)`. Unlike `OldGuarantee` (whose `old` heap is
      `resume`'s native entry state), `H1` is tracked by the caller per
      instance and threaded in as an explicit `$h_rely_old : Heap`
      parameter, so on the caller path `oldRelies(e)` lowers to
      `Old e (some $h_rely_old)` (no Core `old`, since relies become `resume`
      preconditions). Seeded to the current heap on the first resume, so
      `R(H1, now)` becomes `R(H0, H0)` there. -/
  | OldRelies (value : AstNode StmtExpr)
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
  /-- Yield expression used inside coroutines.

      Statement position: suspends the coroutine; the resumed value is dropped.
      Expression position (`z := yield`): suspends; evaluates to the value the
      next `resume(co, v)` sends in (type matches the coroutine's `resumes`
      binding).

      To yield a value outward, the user assigns it to the coroutine's
      `yields` binding before the suspension: `x := e; yield`. -/
  | Yield
  /-- Resume a coroutine instance, optionally sending it a value.
      `target` evaluates to the coroutine instance to resume.
      `value` is the value sent into the coroutine (the binding for the
      yield expression that suspended it); `none` for a unit-valued resume.
      As a statement, the resumed value (the next yield's payload) is dropped;
      in expression position (`x := resume(g, v)`) it is bound to `x`. -/
  | Resume (target : AstNode StmtExpr) (value : Option (AstNode StmtExpr))
  /-- Has-next test on a coroutine instance: `has_next(co)` evaluates to
      `true` iff `co` has not yet run to completion (its internal `$pc`
      has not reached the END state). -/
  | HasNext (target : AstNode StmtExpr)
  /-- Lowering artifact (no surface syntax): capture the current state at this
      program point under the opaque label `label`, so a later
      `Old e (some label)` reads `e` against it. -/
  | Snapshot (label : Identifier)

inductive ContractType where
  | Reads | Modifies | Precondition | PostCondition | Relies | Guarantees
end

/--
The coroutine-specific contract clauses of a procedure.

A regular procedure carries none of these (`Regular`); a coroutine carries all
four (`Coroutine`), any of which may be empty. Bundling them in one sum type —
rather than four independent fields guarded by a separate `ProcedureKind` flag —
makes the illegal state "a regular procedure with a non-empty `relies`"
unrepresentable: the clauses exist *only* in the `Coroutine` case. `Procedure.kind`
is recovered from which constructor is present, so `ProcedureKind` remains the
public spelling for the regular/coroutine distinction.
-/
inductive CoroutineContracts where
  /-- An ordinary (non-coroutine) procedure: no coroutine clauses. -/
  | Regular
  /-- A coroutine's four contract clauses.

      - `relies`: a property the caller is required to (re-)establish between
        yields, and which the body may assume on entry and immediately after
        every `yield`. The `resumes (y: U)` binding is in scope here.
      - `guarantees`: a property the body must establish at every `yield` site
        (and at the implicit yield on construction-spec exit, if any). The
        `yields (x: T)` binding is in scope here.
      - `yields`: the outgoing-channel bindings declared by
        `yields (x1: T1, ...)`. Names are in scope inside the body, inside the
        `guarantees` clauses (per-yield guarantee), and inside the halt
        `ensures` clauses if the body assigns to them before falling off. The
        grammar rejects empty parens.
      - `resumes`: the incoming-channel bindings declared by
        `resumes (y1: U1, ...)`. Names are in scope inside the `relies` clauses
        (per-yield rely); the body retrieves resumed values via the
        expression-form of `yield`. -/
  | Coroutine
      (relies : List Condition)
      (guarantees : List Condition)
      (yields : List Parameter)
      (resumes : List Parameter)

/--
A procedure in Laurel. Procedures are the main unit of specification and
verification. Unlike separate functions and methods, Laurel uses a single
general concept that covers both.
-/
structure Procedure : Type where
  /-- The procedure's name. -/
  name : Identifier
  /-- Type parameters, e.g. `T` in `procedure f<T>(...)`. Empty for monomorphic
      procedures. Brought into scope by resolution so `T` in a signature
      resolves to `.TVar`. -/
  typeArgs : List Identifier := []
  /-- Input parameters with their types. -/
  inputs : List Parameter
  /-- Output parameters with their types. Multiple outputs are supported. -/
  outputs : List Parameter
  /-- The preconditions that callers must satisfy. For regular
      procedures, the standard call-time precondition. For coroutines,
      the construction precondition: fires once at spawn time (when
      the coroutine value is first created) and is *not* re-checked at
      each resume. -/
  preconditions : List Condition
  /-- The coroutine-specific contract clauses (`relies` / `guarantees` /
      `yields` / `resumes`). `Regular` for an ordinary procedure; a
      `Coroutine` bundle for a coroutine. This field also determines
      `Procedure.kind`. -/
  contracts : CoroutineContracts := .Regular
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
  | .OldGuarantee ..     => "oldGuarantee"
  | .OldRelies ..        => "oldRelies"
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
  | .Yield               => "yield"
  | .Resume ..           => "resume"
  | .HasNext ..          => "has_next"
  | .Snapshot ..         => "snapshot"

@[expose] abbrev HighTypeMd := AstNode HighType
@[expose] abbrev StmtExprMd := AstNode StmtExpr
@[expose] abbrev VariableMd := AstNode Variable

/-! The two degenerate `ModifiesGroup` forms every frontend emits, named so the
    load-bearing distinction is spelled once: an empty-target group means
    "nothing changes", a wildcard group means "may modify anything", and zero
    *groups* would mean unframed. Mixing these up silently flips a procedure's
    frame semantics, so construction sites should route through these rather
    than restate the literals. -/

/-- The opaque default frame: one unguarded group with no targets — the
    procedure changes nothing. Distinct from `[]` (no groups), which means
    *unframed*. -/
def ModifiesGroup.nothingChanges : List ModifiesGroup := [{ targets := [] }]

/-- One unguarded group whose only target is the wildcard — the procedure may
    modify anything. -/
def ModifiesGroup.wildcard (source : FileRange) : List ModifiesGroup :=
  [{ targets := [{ val := .All, source }] }]

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

/-- The base composite NAME of a type reference, for consumers that need the parent
    name rather than its instantiation: `.UserDefined Base` and `.Applied (UserDefined
    Base) args` both peel to `Base`, and a bare `.TVar T` yields its own name `T` (an
    inherited type-var parent, pre-monomorphization). `none` for a type with no nameable
    base (a primitive, collection, etc.) — callers treat that as "no inheritable parent". Used by
    the `extending`-list consumers after `extending` became `List HighTypeMd`:
    field-scope inheritance, the subtype `parentExprMap`/`ancestors`, and diamond checks
    all key on the parent NAME (field names are instantiation-independent), so peeling to
    the base is correct for them; only prelude dependency-collection needs the full type
    (it recurses the args separately). -/
def highBaseName? : HighType → Option Identifier
  | .UserDefined n => some n
  | .Applied base _ => highBaseName? base.val
  | .TVar n => some n   -- name-keyed lookups still want the tvar's own name
  | _ => none

/-- Recurse a `HighType`'s structural constructors (`TSet`/`TMap`/`Applied`/
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
      | .Intersection ts => .Intersection (ts.map go)
      | .MultiValuedExpr ts => .MultiValuedExpr (ts.map go)
      | other => other
    { val := v, source := ty.source }
  go ty

/-- Does a `HighType` mention a type variable (`.TVar`) anywhere — bare, or nested
    inside a generic application / collection / intersection (`Box<T>`, `Map T int`,
    `A & T`)? The recursive counterpart of the top-level `.TVar` test, used where a
    type must be treated as "not yet concrete" if a parameter appears at any depth:
    the poly-`throws` escape deferral in `Resolution.exceptionEscapes`, and
    `ContractPass`'s polymorphic-callee detection. Single definition so those callers
    can't drift apart. -/
partial def mentionsTVar : HighType → Bool
  | .TVar _ => true
  | .Applied b args => mentionsTVar b.val || args.any (mentionsTVar ·.val)
  | .TMap k v => mentionsTVar k.val || mentionsTVar v.val
  | .TSet e => mentionsTVar e.val
  | .Intersection ts => ts.any (mentionsTVar ·.val)
  | .MultiValuedExpr ts => ts.any (mentionsTVar ·.val)
  | _ => false

/-- Substitute type variables (by name) throughout a `HighType`. A parameter may appear as
    `.TVar name` (when resolution scoped it) or `.UserDefined name` (if it didn't); either
    is replaced by its `subst` entry (by name), or left as-is. -/
partial def substTypeVars (subst : Std.HashMap String HighTypeMd) (ty : HighTypeMd) : HighTypeMd :=
  mapHighTypeNames (fun ctor name =>
    match subst.get? name.text with
    | some replacement => replacement.val
    | none => ctor name) ty

/-- Apply a generic alias's type arguments to its target: bind `params ↦ args` and substitute
    into `target` (via `substTypeVars`). Returns `none` when `params` is empty (a monomorphic
    alias erroneously reaching an `.Applied` position) or the arity doesn't match — the caller
    then leaves the application unfolded for an upstream arity error. Does NOT recurse: each
    caller (`TypeAliasElim.resolveAliasType`, `TypeLattice.unfold`) recurses with its own
    recursor. Single source of truth for the alias-arg substitution so the consistency relation
    (`unfold`) and the elimination pass cannot drift — the lockstep the false-twin tests pin. -/
def applyAliasArgs (params : List Identifier) (args : List HighTypeMd) (target : HighTypeMd) :
    Option HighTypeMd :=
  if !params.isEmpty && params.length == args.length then
    let subst : Std.HashMap String HighTypeMd :=
      (params.zip args).foldl (fun m (p, a) => m.insert p.text a) {}
    some (substTypeVars subst target)
  else none

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
  | HighType.TVar r1, HighType.TVar r2 => r1.text == r2.text
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


/-- Structurally match a DECLARED type (which may mention type variables `.TVar`)
    against an ACTUAL type, accumulating bindings `tv ↦ actual`. This is the
    type-argument inference for procedure monomorphization: matching the declared
    param `Box<T>` against an arg of type `Box<int>` yields `T ↦ int`.

    Matching, not unification (binds a `.TVar` only on the DECLARED side): we infer one
    procedure's type args from a single call's arg types, so no two-sided `F<X>` vs `F<Y>`
    constraint ever arises. The actual side is NOT always ground — a pristine poly body's
    internal call can pass `b : Box<T>` — so matching may bind `T ↦ .TVar T`; that bogus
    binding isn't special-cased here but rejected by `inferProcInst`'s concreteness gate
    (every inferred arg must be `tyTag`-taggable), deferring the call until cloning makes
    the arg concrete. (The occurs-check analogue — a divergent recursive generic — is the
    worklist depth cap's job.)

    Returns the extended binding map, or `none` on a structural mismatch (different
    head constructors / arities) or an INCONSISTENT binding (a `tv` matched to two
    different types — a genuine type error the caller surfaces loudly).
    `acc` threads bindings across multiple parameters. -/
def matchTypeArg (declared actual : HighType)
    (acc : Std.HashMap String HighType) : Option (Std.HashMap String HighType) :=
  match _h : declared with
  | .TVar tv =>
    match acc.get? tv.text with
    | some prev => if highEq ⟨prev, .unknown⟩ ⟨actual, .unknown⟩ then some acc else none  -- inconsistent
    | none => some (acc.insert tv.text actual)
  | .Applied db dargs =>
    match actual with
    | .Applied ab aargs =>
      if dargs.length != aargs.length then none
      -- SELF-GUARD: two `.UserDefined` heads with different base names must NOT match.
      -- The head recursion below binds nothing for `.UserDefined`/`.UserDefined` (it hits
      -- the catch-all), so without this `Box<T>` would structurally match `Pair<int>` on
      -- arity alone (MatchTypeArgTest case 7). No live wrong-accept today — the earlier
      -- gradual-assignability gate rejects such args — but this makes monomorphization
      -- self-guarding rather than trusting an upstream pass. Only the both-named-mismatch
      -- case is constrained; every other head shape keeps the prior behavior.
      else if (match db.val, ab.val with
               | .UserDefined dn, .UserDefined an => dn.text != an.text
               | _, _ => false) then none
      else
        -- match the head, then each arg positionally, threading `acc`
        match matchTypeArg db.val ab.val acc with
        | none => none
        | some acc1 =>
          -- `.attach` on the zipped pairs exposes `⟨d,a⟩ ∈ dargs.zip aargs`, from which
          -- `List.of_mem_zip` recovers `d ∈ dargs` for the termination measure.
          (dargs.zip aargs).attach.foldl (fun acc? ⟨(d, a), _⟩ =>
            acc?.bind (fun m => matchTypeArg d.val a.val m)) (some acc1)
    | _ => none
  | .TSet dv => match actual with | .TSet av => matchTypeArg dv.val av.val acc | _ => none
  | .TMap dk dv => match actual with
    | .TMap ak av => (matchTypeArg dk.val ak.val acc).bind (fun m => matchTypeArg dv.val av.val m)
    | _ => none
  -- A concrete declared type (no tyvar) need only be consistent with the actual;
  -- we don't constrain it (any mismatch is a separate type error, not our concern).
  | _ => some acc
  termination_by declared
  decreasing_by
    -- Most goals recurse into a `.val` child (`db`/`dv`/`dk`), closed by the shared tactic.
    -- The `.Applied` args case recurses on `d.val` for `⟨d,a⟩ ∈ dargs.zip aargs`; recover
    -- `d ∈ dargs` via `List.of_mem_zip` first, then it too closes by the shared tactic.
    all_goals (try (rename_i h; have := (List.of_mem_zip h).1))
    all_goals ast_recursion_decreasing

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
    - `parentExprMap` maps a composite type's name to its type-param names + its
      *direct* parent type EXPRESSIONS (`extending` list, verbatim). The name-walk
      subtype check (`ancestors`) projects these to parent names via
      `directParentNames`; `substitutedAncestors` uses the full expressions to
      compute the true supertypes of an instantiation (applying the `extends` remap).

    Keyed by type-name *text* (`String`), not `Identifier`: this is consistent
    with how `highEq` decides `UserDefined` equality (by `.text`), and is forced
    because the lattice is built from the *unresolved* program in
    `TypeLattice.ofTypes`, before the resolution pass assigns `uniqueId`s.
    Consequence: nominal type identity is by name text, so subtyping
    (`ancestors` walking parent names) assumes type names are globally unique.
    Safe today (no module system); revisit when modules / namespacing / imports
    land, since two distinct same-named types would otherwise share an
    inheritance chain. -/
structure TypeLattice where
  -- The type-param names let `unfold` substitute a generic alias's args
  -- (`Foo<int>` ⇒ target[T↦int]) so the consistency relation agrees with what
  -- `TypeAliasElim` produces (empty param list for a monomorphic alias).
  unfoldMap : Std.HashMap String (List Identifier × HighTypeMd) := {}
  -- Per composite name: type-param names + verbatim parent expressions (see docstring above).
  parentExprMap : Std.HashMap String (List Identifier × List HighTypeMd) := {}
  /-- Type names that are treated as the gradual/dynamic top type (consistent with everything).
      Set by language frontends (e.g. Python pipeline registers `"Any"` here). -/
  gradualTypes : Std.HashSet String := {}
  /-- Names RESERVED by the frontend's coercion machinery: the box/unbox bridge procedures
      and datatype constructors/accessors the `realizeCoercion` realizer synthesizes calls to
      (e.g. the Python pipeline's `from_int`, `Any_sets!`, `Any..as_Dict!`, `int_to_real`,
      `exception`). The realizer inserts calls to these by bare name and assumes they always
      resolve to their prelude declarations; a user binding that shadowed one would break that
      assumption (the synthesized call would re-resolve to the local). So a local/parameter/
      quantifier binding whose name is reserved is rejected at its binding site with a user
      diagnostic, exactly as a keyword would be. Empty for native Laurel (no reservations). -/
  reservedNames : Std.HashSet String := {}
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
        -- Monomorphic alias / constrained-type base: splice the target.
        | some ([], target) => ctx.unfold target (visited.insert name.text)
        | _ => ty
  -- A generic-alias application `Foo<τ…>` where `Foo` is an alias with params: bind
  -- `params ↦ τ…`, substitute into the target, and recurse. (Mirrors `TypeAliasElim`'s
  -- `resolveAliasType`, so the consistency relation agrees with what elimination produces.)
  -- A non-alias `.Applied` (a real generic composite/datatype) is not in `unfoldMap` ⇒
  -- returned UNCHANGED — `unfold` only rewrites aliases. Generic datatypes/composites keep
  -- their args here; `isConsistent`/`isSubtype` then check them element-wise (invariantly),
  -- so `Opt<int>` and `Opt<bool>` are distinct rather than both erased to `Opt`.
  | .Applied base args =>
    match base.val with
    | .UserDefined name =>
      if visited.contains name.text then ty
      else match ctx.unfoldMap.get? name.text with
        | some (params, target) =>
          match applyAliasArgs params args target with
          | some t => ctx.unfold t (visited.insert name.text)
          | none => ty
        | none => ty
    | _ => ty
  | _ => ty

/-- The direct parent NAMES of a composite, projected from `parentExprMap`'s parent
    EXPRESSIONS (peeling each to its base name). This is the name-only view the subtype
    walk needs; the full expressions stay in `parentExprMap` for `substitutedAncestors`. -/
private def TypeLattice.directParentNames (ctx : TypeLattice) (name : String) : List String :=
  match ctx.parentExprMap.get? name with
  | some (_, exprs) => exprs.filterMap (fun e => (highBaseName? e.val).map (·.text))
  | none => []

/-- All ancestors of a composite type (including itself), reachable via repeated
    `extending` lookups. Visited-set graph traversal (`parents ++ rest`, so DFS —
    but order is irrelevant since the result is a set): `acc` doubles as the visited
    set, each name inserted before its parents are enqueued, so each is processed at
    most once. `acc` only grows, so cycles in a malformed graph terminate — no `fuel`. -/
partial def TypeLattice.ancestors (ctx : TypeLattice) (name : String) : Std.HashSet String :=
  let rec go (acc : Std.HashSet String) (frontier : List String) : Std.HashSet String :=
    match frontier with
    | [] => acc
    | n :: rest =>
      if acc.contains n then go acc rest
      else
        let acc' := acc.insert n
        let parents := ctx.directParentNames n
        go acc' (parents ++ rest)
  go {} [name]

/-- The unique element of `names` that is a subtype of every element (the most
    specific), or `none` when none dominates.

    `ancestors` is reflexive (`go {} [name]` seeds with `name`), so an element
    dominates itself with no special case. On an acyclic `extending` graph at most one
    element can dominate -- two dominators would be mutually reachable, which needs a
    cycle -- so `find?` is equivalent to demanding a singleton. Nothing rejects a cycle
    (`A extends B`, `B extends A` type-checks today), and in one `find?` returns whichever
    mutually-reachable name it reaches first; that pick is order-dependent, unlike every
    acyclic case. Out of scope here: a cycle needs rejecting where types are defined, not
    working around at each use.

    Each ancestor set is computed ONCE, outside the inner `all`: that lambda runs per
    pair, so computing it inside would cost a graph walk per pair.

    Serves both directions of specificity, differing only in the set passed and in
    what an absent winner means: the most-specific *declarer* of an inherited member
    (`resolveInheritedMember`) and the join of a set of types (`commonAncestor`). -/
private def TypeLattice.mostSpecific (ctx : TypeLattice) (names : List String) : Option String :=
  let withAncestors := names.map fun n => (n, ctx.ancestors n)
  (withAncestors.find? fun (_, anc) => names.all anc.contains).map Prod.fst

/-- The elements of `names` that no OTHER element is a strict subtype of -- the
    most-specific ones, i.e. the maximal antichain under `extending`.

    This is what an ambiguity is *between*. A declarer that some other declarer sits
    strictly below is shadowed along that branch and can never be selected, so naming it
    as a candidate would describe a choice the resolver does not have: for `A` declaring
    `m`, `B extends A` overriding it, and unrelated `C` also declaring it, a type
    extending `B, C` is ambiguous between `B` and `C` alone -- `A` is out, and calling
    `A` and `B` "unrelated" would be false besides, since `B <: A`.

    Reflexivity is why the comparison excludes `n` itself: every element is its own
    ancestor, so an unguarded test would find each element dominated by itself and
    return nothing.

    Dominance is STRICT (`!nAnc.contains other`), which matters only because nothing
    rejects an `extending` cycle: two mutually-extending names each contain the other,
    so a non-strict test calls each dominated by the other and drops BOTH. For
    `Ac <-> Bc` both declaring `m` with unrelated `Cc`, and `Tc extends Bc, Cc`, a
    non-strict test yields "the unrelated types Cc" -- one name, for an ambiguity, and a
    set that no longer contains the branch the user has to choose between. Strictness
    keeps a cyclic pair in the list, where the message is at least honest about what
    competes. `InheritedCallDominance` D7 pins this.

    Filtering never changes WHETHER a call is ambiguous, only which names are reported:
    `mostSpecific` returns `some` exactly when this antichain is a singleton. (Acyclic
    case; in a cycle `mostSpecific` already returns `some`, so this is unreachable.) -/
private def TypeLattice.nonDominated (ctx : TypeLattice) (names : List String) : List String :=
  let withAncestors := names.map fun n => (n, ctx.ancestors n)
  (withAncestors.filter fun (n, nAnc) =>
    !(withAncestors.any fun (other, otherAnc) =>
        other != n && otherAnc.contains n && !nAnc.contains other)).map Prod.fst

/-- Outcome of resolving an instance procedure inherited through `extends`: the
    unique most-specific declarer, none, or a same-specificity ambiguity the caller
    must reject.

    Procedures only. Inherited FIELDS bypass this: `typeScope` copies each parent's
    scope in `extending` order (see `Resolution.lean`), so a field declared by two
    incomparable parents gets a silent last-parent-wins pick, not the ambiguity this
    type surfaces. Routing fields here would change field-resolution behaviour and
    wants its own change; flagged so the asymmetry is not read as an oversight.

    `ambiguous` carries the non-dominated declarers only -- the antichain the ambiguity
    is between -- sorted, since they come from a `HashSet` walk and the diagnostic text is
    derived from them. A shadowed declarer is omitted: it is not a choice the resolver
    has. `resolved` needs no such guarantee -- dominance makes its winner unique. -/
inductive MemberResolution where
  | resolved (declarer : String)
  | undeclared
  | ambiguous (candidates : List String)
  deriving Repr, BEq

/-- Resolve `p` (in practice "declares instance procedure m") across `name`'s
    ancestor chain by MOST-SPECIFIC declarer, the standard rule for static
    multiple-inheritance name lookup (cf. Java interface defaults, C++ member lookup):
    among the ancestors declaring the member, the one that is a subtype of every other
    declarer wins, so an override on a nearer type shadows a farther one along any
    single chain. Declarers on incomparable branches (a diamond: `D extends L, R`,
    both declaring, `D` not) have no most-specific declarer and yield `ambiguous` —
    never a silent pick. `name` is itself a candidate, so a type declaring its own
    member resolves to itself. -/
def TypeLattice.resolveInheritedMember
    (ctx : TypeLattice) (name : String) (p : String → Bool) : MemberResolution :=
  -- `ancestors` is a `HashSet`, so this list's order is incidental: specificity
  -- comes from the subtype relation below, never from position.
  match (ctx.ancestors name).toList.filter p with
  | [] => .undeclared
  | declarers =>
    -- Deduplicated by DECLARER IDENTITY (each ancestor visited once), which stops a
    -- shared base forging a false winner: every composite extends a common root
    -- (Object), yet a diamond `Z extends P, Q` with both declaring `m` yields two
    -- DISTINCT declarers, neither dominating => `ambiguous`. One declaration
    -- reached by two paths is a single entry => `resolved`.
    match ctx.mostSpecific declarers with
    | some winner => .resolved winner
    -- Report the antichain, not every declarer: a dominated declarer is shadowed and
    -- could never be selected (see `nonDominated`). Sorted, since the declarers come
    -- from a `HashSet` walk and the diagnostic text is derived from this list.
    | none => .ambiguous ((ctx.nonDominated declarers).mergeSort (· < ·))

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
    -- other name. The join is the most specific of those -- the same dominance
    -- rule `resolveInheritedMember` applies to declarers, hence `mostSpecific`
    -- for both.
    ctx.mostSpecific <| (ctx.ancestors first).toList.filter fun a =>
      rest.all fun n => (ctx.ancestors n).contains a

/-- The instantiation-tag arms COMMON to both monomorphization (`tyTag`) and heap-box
    naming (`appliedBoxTag`): identifier-legal, `$`-delimited, `none` on any type the caller
    doesn't handle. The two callers differ only in the extra leaf arm (`tyTag` allows `.TVoid`,
    `appliedBoxTag` adds none), supplied via `leaf` (see below). Returning `none` (not a
    catch-all) on an untaggable arg is important: such an arg has no stable name, so a
    `Box<T>` (unbound `T`) argument makes the whole tag `none` (fail loud). E.g.
    `Box<Pair<int,bool>>` → `Box$a1$Pair$a2$int$bool`, `Box<Map int int>` → `Box$a1$Map$a2$int$int`.

    INJECTIVITY CAVEAT: this encoding is NOT injective in general. The `$`-delimited join is
    only injective under the assumption that no rendered leaf name itself contains `$` — but
    `$` is a legal identifier character, so a user composite literally named `Pair$a2$int$bool`
    renders the same string as `Box<Pair<int,bool>>`'s inner tag, and `Pair<X$Y,Z>` collides
    with `Pair<X,Y$Z>` (a `$` migrating across the comma). Such collisions are NOT prevented
    here; they are caught DOWNSTREAM — a coalesced composite with a divergent field layout
    fails the duplicate-definition / type re-resolution net after `MonomorphizeComposites`
    (see `LaurelCompilationPipeline.runLaurelPasses`), and divergent value sorts fail the Core
    type checker. Making this encoding injective (escaping/length-prefixing `$`) would be a
    defense-in-depth hardening; today the downstream nets are what guarantee soundness. -/
-- `leaf` (the caller's extra arm) is consulted first, then the shared arms recurse on
-- `instTagCommon leaf` STRUCTURALLY — that direct recursion is what lets this be a total `def`
-- (an opaque `recurse` callback would hide the subterm decrease from the termination checker).
def instTagCommon (leaf : HighType → Option String) (ty : HighType) : Option String :=
  match leaf ty with
  | some t => some t
  | none =>
  match ty with
  | .TInt => some "int" | .TBool => some "bool" | .TReal => some "real"
  | .TString => some "string" | .TFloat64 => some "float64"
  | .TBv n => some s!"bv{n}"
  | .UserDefined n => some n.text
  | .Applied b as =>
    match b.val with
    | .UserDefined n => do
      let argTags ← as.attach.mapM (fun ⟨a, _⟩ => instTagCommon leaf a.val)
      some s!"{n.text}$a{argTags.length}${String.intercalate "$" argTags}"
    | _ => none
  -- Built-in collection formers `Map`/`Set` tag like a 2-/1-ary applied type, so a
  -- `Map`-/`Set`-typed composite FIELD can be heap-boxed (the box-name fns route through
  -- this tagger). These are their own HighType nodes (`.TMap`/`.TSet`), NOT `.Applied`
  -- heads: `Map<K,V>` has a dedicated surface production (`mapType`) that parses to `.TMap`,
  -- and `.TSet` has no surface production today (so only the `.TMap` arm is exercised — see
  -- lines 1162/1316). (A user composite literally named `Map$a2$int$int` still collides —
  -- see the injectivity caveat above.) The `do`-block
  -- short-circuits to `none` on an untaggable element (e.g. a nested `.TVar`), fail-loud
  -- exactly like the `.Applied` arm above.
  | .TMap k v => do
    let kt ← instTagCommon leaf k.val
    let vt ← instTagCommon leaf v.val
    some s!"Map$a2${kt}${vt}"
  -- `.TSet` is unreachable today (no Set surface production — LaurelGrammar.st has only `mapType`);
  -- kept for symmetry with `.TMap` / the `.TSet` arm in `isConsistent`.
  | .TSet e => do
    let et ← instTagCommon leaf e.val
    some s!"Set$a1${et}"
  | _ => none
  termination_by ty
  decreasing_by ast_recursion_decreasing


/-- The fully-SUBSTITUTED ancestor TYPES of `C<args>`. Starting from the
    given composite `name` instantiated at `args`, look up `(params, parentExprs)` in
    `parentExprMap`, substitute `{params := args}` into each parent EXPRESSION, and recurse
    on each substituted parent — so `P2<A,B> extends Pair<B,A>` gives `P2<int,bool>` the TRUE
    supertype `Pair<bool,int>` (NOT `Pair<int,bool>`), and `extends Base<int>` yields
    `Base<int>` regardless of the child's own args (concretization). This remap is what makes
    upcasting sound under type-argument substitution. Returns the parent types (NOT including `C<args>` itself);
    `isSubtype` checks the target against this set with INVARIANT args.
    Termination: `highEq` dedup drops structural repeats (a malformed cyclic `extends`
    stops re-enqueuing) + `fuel` backstop. -/
partial def TypeLattice.substitutedAncestors (ctx : TypeLattice)
    (name : String) (args : List HighTypeMd) : List HighTypeMd := Id.run do
  let mut out : List HighTypeMd := []
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
      | none => pure ()
      | some (params, parentExprs) =>
        let subst : Std.HashMap String HighTypeMd :=
          (params.zip curArgs).foldl (fun m (p, a) => m.insert p.text a) {}
        for pe in parentExprs do
          let pe' := substTypeVars subst pe
          -- Dedup by `highEq` — the same equality `isSubtype` uses on these ancestors, so no
          -- separate key with its own "agrees with highEq" invariant to keep. Set is tiny.
          unless out.any (fun a => highEq a pe') do
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
  -- GENERIC UPCAST (remap-aware, sound): `C<args> <: sup` iff some SUBSTITUTED ancestor of
  -- `C<args>` `highEq`s `sup`. `substitutedAncestors` applies the `extends` remap, so
  -- `P2<A,B> extends Pair<B,A>` gives `P2<int,bool>` the ancestor `Pair<bool,int>` (not
  -- `Pair<int,bool>`), and `Box<bool> extends Base<int>` has ancestor `Base<int>`. Args INVARIANT
  -- (exact `highEq`), so wrong instantiations (`Box<int> <: Base<bool>`) fail; a non-substituting
  -- check would be unsound.
  | .Applied subBase subArgs, _ =>
    (match highBaseName? subBase.val with
     | some subName => (ctx.substitutedAncestors subName.text subArgs).any (fun anc => highEq anc sup')
     | none => false)
    || highEq sub' sup'
  -- CONCRETE child of a GENERIC-INSTANTIATION parent (`IntBox extends Box<int>` ⊢
  -- `IntBox <: Box<int>`): same remap-aware check as the `.Applied` arm, with no args to
  -- substitute — `substitutedAncestors subName []` yields the `extends` expression verbatim
  -- (`Box<int>`), matched by exact `highEq`. So `IntBox <: Box<bool>` (wrong inst) fails. No
  -- reflexive `highEq` fallback: a `.UserDefined` never `highEq`s an `.Applied`, so it'd be dead.
  | .UserDefined subName, .Applied _ _ =>
    (ctx.substitutedAncestors subName.text []).any (fun anc => highEq anc sup')
  | _, _ => highEq sub' sup'

/- ### Variance policy (covers `isSubtype` and `isConsistent`)
   `isConsistent` RECURSES element-wise (with `isConsistent`, not `highEq`) through
   `TSet`, `TMap`, `Applied`, and `MultiValuedExpr`, so an `Unknown`/`.TVar` wildcard
   DOES penetrate under these constructors: `TSet Unknown ~ TSet TInt` is TRUE (the inner
   `Unknown ~ TInt` hits the wildcard). The recursion keeps two CONCRETE instantiations
   INVARIANT, though — `TSet TInt ~ TSet TBool` is FALSE (`int`/`bool` on the element leaf) —
   so this is gradual-wildcard penetration, not covariance; `TSet`/`TMap` stay sound as
   mutable collections. (`Intersection` still bottoms out in `highEq`.)

   `MultiValuedExpr` and `Applied` recurse element-wise as above:
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
  -- A generic application `C<τ…>` is checked element-wise *before* unfolding (like
  -- `MultiValuedExpr`), so the args remain demonstrable subterms for termination and
  -- `unfold` (identity on a generic-COMPOSITE `.Applied` — composites aren't in `unfoldMap`;
  -- only alias applications unfold) loses no precision here. This is what lets a concrete
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
  -- Base names are compared AFTER unfolding aliases (`ctx.unfold` turns a generic-alias
  -- application `Foo<int>` into its target `Opt<int>`, and a bare alias into its base), so
  -- a var typed via a generic alias of a datatype (`type Foo<T> = Opt<T>`; `var o: Foo<int>
  -- := Som(5)`, where the constructor `Som` synthesizes the bare `Opt`) matches. Unfolding
  -- cannot widen this beyond same-base-name: distinct targets still differ.
  | .UserDefined _, .Applied _ _ | .Applied _ _, .UserDefined _ =>
    match highBaseName? (ctx.unfold a).val, highBaseName? (ctx.unfold b).val with
    | some na, some nb => na.text == nb.text
    | _, _ => false
  | _, _ =>
    let a' := ctx.unfold a
    let b' := ctx.unfold b
    -- A type VARIABLE is consistent with everything (like `Unknown`): an
    -- un-monomorphized `T` is a not-yet-known concrete type. Polymorphic code
    -- (`idp<T>(x:T)` called at `int`; a generic composite field `val:T` written
    -- with an `int`) is type-checked at the INITIAL resolution where `T` is still
    -- `.TVar` — before monomorphization erases it or CallElim freshens it. Without
    -- this arm the gradual checker would reject every polymorphic use with a
    -- spurious "expected 'T', got 'int'" and (since any non-warning resolution
    -- diagnostic gates translation) block ALL polymorphic programs. This is the
    -- gradual-typing-correct treatment, mirroring the `Unknown` wildcard. `.TVar`
    -- joins `Unknown` and the frontend-registered gradual `UserDefined`s (Python
    -- `Any`) as a top-of-type wildcard.
    let isGradual (t : HighType) := match t with
      | .Unknown => true
      | .TVar _ => true
      | .UserDefined id => ctx.gradualTypes.contains id.text
      | _ => false
    if isGradual a'.val || isGradual b'.val then true
    else highEq a' b'
  termination_by (SizeOf.sizeOf a)
  decreasing_by
    all_goals (cases a; cases b; try term_by_mem)
    all_goals (first | (cases base1; term_by_mem) | (cases t1; term_by_mem))

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
      -- Generic polymorphism (poly feature): the element-wise / substituted-ancestor
      -- relations live in `isConsistent`/`isSubtype` (a concrete `Box<int>` satisfying a
      -- `Box<T>` param via the nested `.TVar` wildcard; a `.TVar`/bare-composite wildcard;
      -- `C<args> <: P<pargs>` via `substitutedAncestors`). None of these carry a runtime
      -- coercion — generic composites monomorphize and type variables erase before Core —
      -- so the witness is `refl`. This keeps `isConsistentSubtype := coerce.isSome` equal to
      -- `isConsistent ∨ isSubtype` (the stated invariant) across the poly extensions.
      -- Gradual types cannot reach the arms above: wildcards and boxable gradual UserDefineds
      -- are consumed by the guards (isWildcard / subBoxable / supBoxable) on the SAME unfolded
      -- values this branch tests, so isGradualTop is always false by here.
      | _, _ =>
        if isConsistent ctx sub' sup' || isSubtype ctx sub' sup' then some .refl else none

/-- Consistent subtyping: `∃ R. sub ~ R ∧ R <: sup`. DERIVED from the
    proof-relevant `coerce` so the yes/no answer and the inserted coercion can
    never disagree (ONE judgment). Used by rule `[⇐] Sub` and every bespoke check
    rule. That single choice is what makes the system *gradual*: an expression of
    type `Unknown` (a hole, an unresolved name, a `Hole _ none`) flows freely into
    any typed slot, and any expression flows freely into a slot of type `Unknown`.

    Generic polymorphism flows through `coerce`'s final fallback, which delegates
    to `isConsistent`/`isSubtype` (element-wise generic args, `.TVar` wildcard,
    `substitutedAncestors`) — so a concrete `Box<int>` satisfies a `Box<T>` slot and
    `C<args> <: P<pargs>` holds, all as a `refl` witness. -/
def isConsistentSubtype (ctx : TypeLattice) (sub sup : HighTypeMd) : Bool :=
  (coerce ctx sub sup).isSome

/-- Call-site type-argument inference: the substitution a call makes for its callee's type
    parameters, derived by matching each DECLARED parameter type against the ACTUAL argument
    type. `select<K,V>(map: Map K V, key: K)` applied to a `Map int bool` and an `int` yields
    `{K ↦ int, V ↦ bool}`, so the declared return `V` can be reported as `bool` rather than as
    a bare `.TVar` — which `isConsistent` treats as a gradual wildcard, i.e. unchecked.

    Deliberately BEST-EFFORT, unlike `MonomorphizeComposites.inferProcInst`, whose
    all-or-nothing concreteness gate is right for cloning and wrong here: a parameter that
    fails to match contributes nothing instead of abandoning the whole call, and a type
    parameter that no argument determines (`mapConst<K,V>(value: V)` never fixes `K`) is left
    unbound — substitution then leaves it the `.TVar` it already was, which `isConsistent`
    treats as a gradual wildcard. Inference therefore only sharpens a call site; an
    undetermined parameter is no stricter than an unsubstituted one.

    Each parameter matches under its OWN accumulator and the results are merged here, so a
    type variable occurring in two parameters (`$eq<T>(x: T, y: T)`) is reconciled by
    CONSISTENCY rather than by `matchTypeArg`'s strict `highEq`. That distinction matters: a
    hole or unresolved operand synthesizes `Unknown`, which must still be comparable against a
    concrete operand, whereas `highEq` would call that a conflict.
    Genuine disagreements are returned in the second component for the caller to report, and
    the first binding is kept so one bad slot cannot poison the others.

    A binding whose type still MENTIONS a type variable is dropped rather than recorded: that
    is the abstract-internal-call case (`outer<T>`'s body calling `inner(b)` at `b : Box<T>`),
    where binding `T ↦ T` teaches nothing and would read as if inference had succeeded.

    Actuals are `unfold`ed first so an alias-typed argument (`type IM = Map int bool`) matches
    a `Map K V` parameter — `matchTypeArg` is purely structural and would otherwise compare
    `.UserDefined IM` against `.TMap` and fail. -/
def callSiteTypeSubst (ctx : TypeLattice) (params actuals : List HighTypeMd)
    : Std.HashMap String HighTypeMd × List (String × HighTypeMd × HighTypeMd) :=
  let candidates : List (String × HighTypeMd) :=
    (params.zip actuals).flatMap fun (p, a) =>
      match matchTypeArg p.val (ctx.unfold a).val {} with
      | none => []
      | some bindings =>
        bindings.toList.filterMap fun (name, ty) =>
          if mentionsTVar ty then none
          else some (name, ({ val := ty, source := a.source } : HighTypeMd))
  let names := (candidates.map (·.1)).eraseDups
  names.foldl (init := ({}, [])) fun (subst, conflicts) name =>
    let forName := (candidates.filter (·.1 == name)).map (·.2)
    -- A gradual `Unknown` candidate teaches nothing, so it is set aside unless it is all there
    -- is: `<?> == 1` binds `T ↦ int` rather than stalling at `Unknown`.
    let concrete := forName.filter (fun t => !(t.val matches .Unknown))
    let pool := if concrete.isEmpty then forName else concrete
    -- The binding is the candidate every other candidate satisfies, by consistency or by
    -- subtyping. `isConsistent` alone relates two distinct composites only when they are the
    -- same type, so a subtype argument would otherwise conflict with its own supertype: this is
    -- what lets `update<K,V>(map: Map K V, key: K, value: V)` take a `Map int Animal` and a
    -- `Dog`, binding `V ↦ Animal`.
    --
    -- Decided over the WHOLE candidate set rather than by folding pairwise, which would make the
    -- verdict depend on argument order once a variable occurs three or more times: widening the
    -- accumulated binding to a supertype would then absorb a later sibling that the original
    -- binding would have rejected. `both3<T>` at a `Dog`, an `Animal` and a `Cat` resolves in
    -- every order — `Animal` dominates both siblings — and a `Dog` with a `Cat` alone conflicts
    -- in every order, since neither is a supertype of the other and their common ancestor is not
    -- among the candidates. Reconciling to a common ancestor is deliberately NOT done: passing a
    -- `Dog` where a `Cat` is also expected is far more often a mistake than an intent.
    match pool.find? (fun cand => pool.all (fun o => isConsistent ctx o cand || isSubtype ctx o cand)) with
    | some winner => (subst.insert name winner, conflicts)
    | none =>
      -- No candidate dominates: report the first mutually unrelated pair, which is the one a
      -- reader can act on.
      match pool.findSome? (fun a =>
              (pool.find? (fun b => !isConsistent ctx a b && !isSubtype ctx a b && !isSubtype ctx b a)).map
                (fun b => (a, b))) with
      | some (a, b) => (subst, (name, a, b) :: conflicts)
      | none => (subst, conflicts)

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
  | .OldGuarantee .. => "OldGuarantee"
  | .OldRelies .. => "OldRelies"
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
  | .Yield => "Yield"
  | .Resume .. => "Resume"
  | .HasNext .. => "HasNext"
  | .Snapshot .. => "Snapshot"
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

/-- The per-yield `relies` clauses; `[]` for a regular procedure. -/
def CoroutineContracts.relies : CoroutineContracts → List Condition
  | .Regular => []
  | .Coroutine r _ _ _ => r

/-- The per-yield `guarantees` clauses; `[]` for a regular procedure. -/
def CoroutineContracts.guarantees : CoroutineContracts → List Condition
  | .Regular => []
  | .Coroutine _ g _ _ => g

/-- The outgoing-channel `yields` bindings; `[]` for a regular procedure. -/
def CoroutineContracts.yields : CoroutineContracts → List Parameter
  | .Regular => []
  | .Coroutine _ _ y _ => y

/-- The incoming-channel `resumes` bindings; `[]` for a regular procedure. -/
def CoroutineContracts.resumes : CoroutineContracts → List Parameter
  | .Regular => []
  | .Coroutine _ _ _ rs => rs

/-- The `ProcedureKind` implied by which contract bundle is present. -/
def CoroutineContracts.kind : CoroutineContracts → ProcedureKind
  | .Regular => .Regular
  | .Coroutine .. => .Coroutine

/-- Replace the clause lists of a `Coroutine` bundle, keeping it a coroutine.
    A no-op on `Regular` (a regular procedure has no clauses to carry). -/
def CoroutineContracts.withClauses (c : CoroutineContracts)
    (relies : List Condition := c.relies) (guarantees : List Condition := c.guarantees)
    (yields : List Parameter := c.yields) (resumes : List Parameter := c.resumes)
    : CoroutineContracts :=
  match c with
  | .Regular => .Regular
  | .Coroutine .. => .Coroutine relies guarantees yields resumes

/-- Map a transformation over the `relies` and `guarantees` clause lists,
    leaving the channel bindings (`yields` / `resumes`) untouched. A no-op on
    `Regular`. -/
def CoroutineContracts.mapConditions (c : CoroutineContracts)
    (f : Condition → Condition) : CoroutineContracts :=
  c.withClauses (relies := c.relies.map f) (guarantees := c.guarantees.map f)

/-- Kind of the procedure, either a regular procedure or a coroutine.
    Recovered from `contracts`. -/
def Procedure.kind (p : Procedure) : ProcedureKind := p.contracts.kind

/-- The coroutine's per-yield `relies` clauses; `[]` for a regular procedure. -/
def Procedure.relies (p : Procedure) : List Condition := p.contracts.relies

/-- The coroutine's per-yield `guarantees` clauses; `[]` for a regular procedure. -/
def Procedure.guarantees (p : Procedure) : List Condition := p.contracts.guarantees

/-- The coroutine's outgoing-channel `yields` bindings; `[]` for a regular procedure. -/
def Procedure.yields (p : Procedure) : List Parameter := p.contracts.yields

/-- The coroutine's incoming-channel `resumes` bindings; `[]` for a regular procedure. -/
def Procedure.resumes (p : Procedure) : List Parameter := p.contracts.resumes

def Procedure.is_coroutine (p : Procedure) : Bool :=
  match p.kind with | .Coroutine => true | _ => false

def Body.isExternal : Body → Bool
  | .External => true
  | _ => false

def Body.isTransparent : Body → Bool
  | .Transparent _ => true
  | _ => false

/-- The body's postconditions. An opaque or abstract body carries them; a transparent or
    external body has none. -/
def Body.postconditions : Body → List Condition
  | .Opaque posts _ _ => posts
  | .Abstract posts   => posts
  | _                 => []

/-- The body's implementation, when it has one — the code a checked condition is verified
    against. A bodiless `.Opaque`, an `.Abstract` body (checked at its concrete overrides
    instead) and an `.External` body have none. -/
def Body.implementation : Body → Option StmtExprMd
  | .Transparent b   => some b
  | .Opaque _ impl _ => impl
  | _                => none

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
  /-- An optional initializer expression evaluated to produce the field's initial value. -/
  initializer : Option StmtExprMd := none

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
  /-- Type parameters for a generic alias (`type Pair<A,B> = …`); empty for a monomorphic alias.
      `TypeAliasElim` binds these to the instantiation args; `TypeLattice.unfold` does the same
      so the consistency relation agrees with elimination. -/
  typeArgs : List Identifier := []
  target : HighTypeMd
  deriving Repr

/-- An opaque type: a named type, optionally generic, whose *implementation is native*
    rather than given in Laurel. Unlike a datatype it has no constructors, so a Laurel
    program can pass values of it around, compare them, and store them, but cannot take
    them apart — the only operations are the procedures declared over it (typically
    `external` ones backed by Core primitives).

    Lowered to a Core opaque type constructor (`Core.TypeDecl.con`), i.e. an SMT
    `declare-sort`. Contrast a zero-constructor `DatatypeDefinition`, which cannot stay
    opaque: Core's `LDatatype` requires a non-empty constructor list, so the schema pass
    injects a synthetic unit constructor and the type collapses to a singleton. An opaque
    type is the right spelling whenever every value must stay distinct.

    Example: `opaque Set<T>;` — the element type is a real type parameter, but `Set` has
    no Laurel-visible structure. -/
structure OpaqueTypeDefinition where
  name : Identifier
  /-- Type parameters (`opaque Set<T>;`); empty for a monomorphic opaque type. Scoped over
      nothing — an opaque type has no constructor arguments for them to appear in — but they
      fix the type's *arity*, which Core's `declare-sort` and every use site must agree on. -/
  typeArgs : List Identifier := []
  deriving Repr

/--
A user-defined type, either a composite type, a constrained type, an algebraic datatype,
an opaque (natively implemented) type, or a type alias.

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
  /-- An opaque type with a native implementation (e.g. `opaque Set<T>;`). -/
  | Opaque (ty : OpaqueTypeDefinition)
  /-- A type alias (e.g. `MyInt = int`). Eliminated before Core translation. -/
  | Alias (ty : TypeAlias)
  deriving Inhabited

def TypeDefinition.name : TypeDefinition → Identifier
  | .Composite ty => ty.name
  | .Constrained ty => ty.name
  | .Datatype ty => ty.name
  | .Opaque ty => ty.name
  | .Alias ty => ty.name

/-- Build a `TypeLattice` from a list of `TypeDefinition`s.
    Aliases populate `unfoldMap` with their target; constrained types populate
    it with their base; composites populate `parentExprMap` with their direct
    parent expressions. Datatypes and opaque types contribute nothing — they're nominal
    and irreducible. -/
def TypeLattice.ofTypes (types : List TypeDefinition) : TypeLattice :=
  types.foldl (init := {}) fun ctx td =>
    match td with
    | .Alias ta => { ctx with unfoldMap := ctx.unfoldMap.insert ta.name.text (ta.typeArgs, ta.target) }
    | .Constrained ct => { ctx with unfoldMap := ctx.unfoldMap.insert ct.name.text ([], ct.base) }
    | .Composite c =>
      { ctx with
        parentExprMap := ctx.parentExprMap.insert c.name.text (c.typeArgs, c.extending) }
    | .Datatype _ | .Opaque _ => ctx

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
  /-- User-defined type definitions (see the `TypeDefinition` constructors). -/
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
