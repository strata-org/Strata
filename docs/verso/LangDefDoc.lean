/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.Stmt
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Imperative.KleeneStmt
import Strata.DL.Imperative.KleeneStmtSemantics
import Strata.DL.Imperative.BasicBlock
import Strata.DL.Imperative.MetaData
import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprResolveAnnotated
import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.Program

open Lambda
open Imperative
open Core

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.docstring.allowMissing false

#doc (Manual) "The Strata Core Language Syntax" =>
%%%
shortTitle := "The Strata Core Language"
%%%

# Introduction

Strata aims to provide a foundation for representing the semantics of programs,
specifications, protocols, architectures, and other aspects of large-scale
distributed systems and their components. It achieves this through languages of
two types. The first type, consisting of the single Strata Core language,
provides a central hub that can serve as a connection point between multiple
types of input artifact and multiple types of analysis, reducing the cost of
implementing N analyses for M languages from N\*M to N+M.

The second type consists of numerous Strata _dialects_.  The Dialect Definition
Mechanism, described
[here](https://github.com/strata-org/Strata/tree/main/docs/verso/DDMDoc.lean),
provides a way to define the syntax and a simple type system for a dialect.  At
the moment, dialects do not directly have semantics (though we may add a
mechanism for defining their semantics in the future) but instead are defined by
translation to or from Strata Core. Said another way, each of these dialects is
a different concrete way to write Strata programs, but all of these dialects are
ultimately represented internally using the same Core language.

Dialects are used to describe both the initial artifacts being analyzed by
Strata and more low-level representations of those artifacts used to communicate
with external reasoning tools such as model checkers or SMT solvers. In both
situations, Strata uses dialects as a mechanism for communicating with external
tools (either language front ends or generic automated reasoning tools like SMT
solvers).

The following "hourglass" diagram illustrates how various existing (blue) or
potential (gray) input dialects could be translated into Strata Core and then
into the input language for various back end tools. Solid lines indicate
translation paths that exist (though experimentally in the connection between
Strata Core and CBMC), and dotted lines indicate translations that illustrate
the sorts of use cases we expect Strata to support but that haven't yet been
implemented.

![Strata hourglass diagram](strata-hourglass.png)

The Strata Core language is constructed using a few building blocks that can be
combined in different ways. This allows concrete dialects to systematically use
different combinations that still share the majority of their implementation. In
Lean (and in principle in most other source languages that could be used to
process Strata programs), the type system can enforce various structural
constraints, ensuring that only expected language constructs show up. The Strata
Core language itself consists of an imperative statement type parameterized by
an expression type, with various more fine-grained adjustments of other
parameters.

The two fundamental building blocks of Strata Core are a representation of
functional programs (`Lambda`), and a representation of imperative programs
(`Imperative`). The `Lambda` language is parameterized by a type system and a
set of built-in types and functions. The `Imperative` language is then
parameterized by the type of expressions it allows in conditions, assignments,
and so on. Currently, those expressions will almost always be some
instantiation of `Lambda`. Both Core building blocks are parameterized by a
metadata type, which by default is instantiated with a map from keys to
structured values that can contain expressions (typically from `Lambda`).

The remainder of this document is structured as follows:

1. Sections 2 and 3 describe `Lambda` and `Imperative` as generic, reusable
   building blocks.
2. Section 4 describes how Strata Core assembles these blocks into a concrete
   verification language with procedures, type declarations, functions, axioms,
   and programs.

The semantics of each layer — operational and denotational for `Lambda`, and
operational for `Imperative` — and how they compose to give meaning to Strata
Core programs, are described in a companion document,
[The Strata Core Language Semantics](https://github.com/strata-org/Strata/blob/main/docs/verso/LangSemDoc.lean).

We do not consider the Core language set in stone. It may evolve over time,
particularly to add new fundamental constructs, and this document will be
updated as it does.

# Lambda

The `Lambda` language is a standard but generic implementation of the lambda
calculus. It is parameterized by a type for metadata and the type of types
(which may be `Unit`, to describe the untyped lambda calculus). It includes the
standard constructs for constants, free and bound variables, abstractions, and
applications. In addition, it includes a special type of constant, an operator,
to represent built-in functions. It extends the standard lambda calculus by
allowing quantifiers (since a key use of the language is to write logical
predicates) and includes dedicated constructors for if-then-else and equality,
both of which occur frequently enough to warrant their own nodes rather than
being built-in operations.

Although `Lambda` can be parameterized by an arbitrary type system, the Strata
code base includes a
[formalization](https://github.com/strata-org/Strata/blob/main/Strata/DL/Lambda/LExprTypeSpec.lean)
of a polymorphic Hindley-Milner type system and an
[implementation](https://github.com/strata-org/Strata/blob/main/Strata/DL/Lambda/LTyUnify.lean)
of an inference algorithm over the type `LTy` (described below). This allows
prenex (Hindley-Milner) polymorphism and the use of arbitrary named type
constructors (as well as special support for bit vector types, to allow them to
be parameterized by size).

## Syntax

The syntax of lambda expressions is provided by the {name LExpr}`LExpr` type.

{docstring Lambda.LExpr}

Identifiers in lambda expressions, using the {name Identifier}`Identifier` type,
can be annotated with metadata.

{docstring Lambda.Identifier}

Specific constructors exist for constants of various scalar types, including
booleans, bit vectors, integers, reals, and strings.

{docstring Lambda.LConst}

The {name LExpr}`LExpr` type can be parameterized by the type used to represent
normal metadata and the type used to represent identifier metadata, as well as
the type of types.

{docstring Lambda.LExprParams}

{docstring Lambda.LExprParamsT}

## Type System

Although {name LExpr}`LExpr` can be parameterized by an arbitrary type system,
Strata currently implements one, based on the types {name LMonoTy}`LMonoTy` and
{name LTy}`LTy`.

The first, {name LMonoTy}`LMonoTy`, represents monomorphic types. A monomorphic
type may contain free type variables (via `ftvar`); these are implicitly
universally quantified. `LMonoTy` is a separate type because some contexts
(e.g., variable declarations, function parameter types) allow only monomorphic
types.

{docstring Lambda.LMonoTy}

Type variables in {name LMonoTy}`LMonoTy` use the {name TyIdentifier}`TyIdentifier` type.

{docstring Lambda.TyIdentifier}

The {name LTy}`LTy` type makes the universal quantification explicit by wrapping
a monomorphic type in prenex universal quantifiers that bind its free type
variables, creating polymorphic type schemes.

{docstring Lambda.LTy}

An expression {name LExpr}`LExpr` parameterized by {name LTy}`LTy` is
well-typed according to the {name LExpr.HasType}`HasType` relation.
This relation depends on two contexts:

1. {name LContext}`LContext`: information that is typically constant during
   expression type checking, but may be extended during statement type checking
   (e.g., when a `funcDecl` statement adds a new function to the factory).
   This includes information about built-in functions, using the
   {name Lambda.Factory}`Factory` type, and built-in types, using the
   {name TypeFactory}`TypeFactory` type. Built-in functions optionally include
   concrete evaluation functions, which can be used in the semantics described
   below.
2. {name Lambda.TContext}`TContext`: data that changes throughout the type
   checking process — a map from free variables in expressions to types, and a
   list of type aliases including the name and definition of each alias.

{docstring Lambda.LContext}

{docstring Lambda.TContext}

Given these two contexts, the {name LExpr.HasType}`HasType` relation describes
the valid type of each expression form.

{docstring Lambda.LExpr.HasType}

After Lambda's type inference ({name LExpr.resolve}`LExpr.resolve`), the type-annotated
expressions follow tighter typing rules which are defined by
{name LExpr.HasTypeA}`LExpr.HasTypeA`. The rule doesn't require typing
contexts.

# Imperative

The `Imperative` language is a standard core imperative calculus, parameterized
by a type of expressions (`PureExpr`) and divided into two pieces: commands and statements.
Commands represent atomic operations that do not induce control flow.
Statements are parameterized by a command type and describe the control flow
surrounding those commands. This parameterization allows clients of `Imperative`
to extend the command type with domain-specific operations (e.g., Strata Core
adds procedure calls). Currently, `Imperative` offers two families of
statements: structured deterministic statements and non-deterministic (Kleene)
statements.

## Commands

The core built-in set of commands includes variable initializations,
deterministic assignments, non-deterministic assignments ("havoc"), assertions,
assumptions, and coverage checks. A coverage check (`cover`) is the dual of
an assertion: it checks whether there _exists_ a reachable path on which the
given condition holds.

{docstring Imperative.Cmd}

Command values can be either deterministic expressions or non-deterministic
(arbitrary) choices, represented by the {name ExprOrNondet}`ExprOrNondet` type.

{docstring Imperative.ExprOrNondet}

## Structured Deterministic Statements

Statements allow commands to be organized into standard control flow
arrangements, including sequencing, alternation, and iteration. Sequencing
statements occurs by grouping them into blocks. Loops can be annotated with
optional invariants and decreasing measures, which can be used for deductive
verification. An `exit` statement transfers control out of the nearest
enclosing block with a matching label. In addition, statements include
`funcDecl` for local function declarations (which extend the expression
evaluator within a scope) and `typeDecl` for local type declarations.

{docstring Imperative.Stmt}

{docstring Imperative.Block}

## Non-deterministic Statements

Non-deterministic statements, inspired by
[Kleene Algebra with Tests](https://www.cs.cornell.edu/~kozen/Papers/kat.pdf)
and
[Guarded Commands](https://en.wikipedia.org/wiki/Guarded_Command_Language),
encode control flow using only non-deterministic choices. A {name KleeneStmt}`KleeneStmt`
can be: an atomic command, a sequential composition, a non-deterministic choice
between two sub-statements, or a loop that executes its body an arbitrary number
of times (possibly zero). Conditions can be encoded when the command type
includes assumptions.

{docstring Imperative.KleeneStmt}

## Control-Flow Graphs

`Imperative` offers a control-flow graph (CFG) as well.
A CFG is a flat collection of labeled basic blocks wired together by terminators
(explicit jumps). This is the natural representation for
lowering unstructured source languages and for interacting with backends that
already think in terms of basic blocks and jumps.

A {name Imperative.BasicBlock}`BasicBlock` is a straight-line list of body
commands.

{docstring Imperative.BasicBlock}

{docstring Imperative.DetTransferCmd}

{docstring Imperative.NondetTransferCmd}

Specializing the transfer type gives the two block flavors,
{name Imperative.DetBlock}`DetBlock` and {name Imperative.NondetBlock}`NondetBlock`.

A {name Imperative.CFG}`CFG` then bundles an entry label with the graph's labeled
blocks.

{docstring Imperative.CFG}

## Metadata

Metadata allows additional information to be attached to nodes in the Strata
AST. This may include information such as the provenance of specific AST nodes
(_e.g._, the locations in source code that gave rise to them), facts inferred by
specific analyses, or indications of the goal of a specific analysis, among many
other possibilities.

Each metadata element maps a field to a value. A field can be named with a
variable or an arbitrary string.

{docstring Imperative.MetaDataElem.Field}

A value can take the form of an expression, an arbitrary string, a source file
range, or a boolean switch.

{docstring Imperative.MetaDataElem.Value}

A metadata element pairs a field with a value.

{docstring Imperative.MetaDataElem}

And, finally, the metadata attached to an AST node consists of an array of
metadata elements.

{docstring Imperative.MetaData}

## Instantiating Imperative

Using the `Imperative` dialect for a concrete language requires filling in three
pieces:

1. *The expression parameter `PureExpr`*, defined in
   `Strata/DL/Imperative/PureExpr.lean`.
   A `PureExpr` bundles the types the dialect will use for identifiers,
   expressions, types, metadata, typing environments, factories, and the
   expression evaluator (`eval`). Instantiating `Imperative` starts by
   constructing a `PureExpr` for the target language (Strata Core does this
   with {name Core.Expression}`Core.Expression`).

   {docstring Imperative.PureExpr}

2. *Structural typeclasses on `PureExpr`.* `Imperative`'s commands and
   statements need to inspect and manipulate expressions in generic ways —
   extracting free variables, constructing Boolean/integer literals, negating
   conditions, and so on. These operations are provided via typeclasses whose
   names start with `Has` (e.g., {name Imperative.HasVarsImp}`HasVarsImp`),
   defined in `Strata/DL/Imperative/PureExpr.lean` and
   `Strata/DL/Imperative/HasVars.lean`. See
   `Strata/Languages/Core/InstWellFormedSemanticsEval.lean` for Strata Core's
   instantiations of these typeclasses.

3. *Well-formedness of the evaluator.* The semantics rules assume the evaluator
   supplied via `PureExpr.eval` respects a few sanity conditions on values,
   variable lookups, and Boolean negation. These predicates, and the bundle
   {name Imperative.WellFormedSemanticEval}`WellFormedSemanticEval` that packages
   them, are described in the companion document, "The Strata Core Language
   Semantics" (see its "Well-Formedness of the Evaluator" section).

The Strata Core language, described next, is a worked example of an
`Imperative` instantiation: it picks `Lambda` expressions for `PureExpr`,
supplies the required `Has`-typeclass instances, and discharges the
well-formedness conditions against `LExpr.evalFully`.

# Strata Core

Strata Core is the concrete verification language built by instantiating the
generic `Lambda` and `Imperative` building blocks with specific types. This
section describes the top-level constructs that make up a Strata Core program.

## Expressions

Strata Core expressions are `Lambda` expressions instantiated with a specific
identifier type (`CoreIdent`) and a monomorphic type system (`LMonoTy`). A
`CoreIdent` identifies either a local variable or an `old` expression (denoting
a pre-state value).

### Built-in Types

Strata Core provides the following built-in types:

- `bool` — booleans
- `int` — unbounded integers
- `real` — rationals (used to model reals)
- `string` — UTF-8 strings
- `regex` — regular expressions over strings
- `bv<n>` — bit vectors of size `n` (e.g., `bv32`, `bv64`)
- `Map<K, V>` — maps from keys of type `K` to values of type `V`
- `Sequence<T>` — finite sequences of elements of type `T`

In addition, function types (`a → b`) are supported as first-class types.
Users can define additional types via type declarations (abstract types, type
synonyms, and algebraic datatypes).

### Built-in Operators

Strata Core provides built-in operators organized by the types they operate on.
The following summarizes each category; the definitive list of operators is
registered in
[`Core.Factory`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Core/Factory.lean)
(see also the
[API reference](https://strata-org.github.io/Strata/api/Strata/Languages/Core/CoreOp.html)).

- *Boolean*: conjunction, disjunction, negation, implication, equivalence.
- *Numeric (int and real)*: addition, subtraction, multiplication, negation,
  division, modulus (Euclidean and truncating variants), comparisons
  (`<`, `≤`, `>`, `≥`). Safe variants of division and modulus generate
  precondition checks for division by zero.
- *Bit vector*: arithmetic (add, sub, mul, div, mod — both signed and
  unsigned), bitwise (and, or, xor, not, shifts), comparisons (signed and
  unsigned), concatenation, and extraction of sub-ranges. Safe arithmetic
  variants generate overflow precondition checks.
- *String*: length, concatenation, substring extraction, prefix and suffix
  checks, conversion to regular expression, and regular expression membership.
- *Regular expression*: constructors (all, allChar, range, none), composition
  (concatenation, union, intersection, complement, star, plus, loop).
- *Map*: constant map, select (lookup), and update (store).
- *Sequence*: length, empty, append, select (index), build, update, contains,
  take, and drop.

Equality (`==`) and if-then-else are provided as built-in `Lambda` expression
constructors rather than operators.

## Type Declarations

Strata Core supports three forms of type declaration:

1. *Abstract types* (`type Name _ ...;`): Opaque type constructors with a
   given arity.
2. *Type synonyms* (`type Name x y = ...;`): Named aliases for existing types,
   which may be parameterized by type variables.
3. *Algebraic datatypes* (`datatype Name(...) { ... };`): Datatypes with
   multiple constructors, each of which can have zero or more typed fields.
   Mutual datatypes are supported. See below for details.

### Algebraic Datatypes

Datatypes are declared using the `datatype` keyword:

```
datatype <Name>(<TypeParams>) {
  <Constructor1>(<field1>: <type1>, ...),
  <Constructor2>(<field2>: <type2>, ...),
  ...
};
```

Strata Core datatypes must satisfy several well-formedness properties: they must
be inhabited (subject to a syntactic check that tries to determine a provably
inhabited constructor), uniform (the type parameters cannot change through
recursion), strictly positive (all recursive occurrences of a type in a
constructor do not appear to the left of any arrow), and non-nested (disallowing
e.g. `datatype Foo() { A(x: List<Foo>) }`).

Datatypes may be polymorphic and recursive:

```
datatype Color () { Red(), Green(), Blue() };

datatype Option<T> () { None(), Some(val: T) };

datatype List<T> () { Nil(), Cons(head: T, tail: List<T>) };
```

When a datatype is declared, Strata automatically generates three kinds of
auxiliary functions:

1. *Constructors*: functions that create values of the datatype (e.g.,
   `None() : Option<T>`, `Cons(head: T, tail: List<T>) : List<T>`).
2. *Tester functions*: for each constructor, a function that returns `true` if
   a value was created with that constructor. The naming convention is
   `<Datatype>..is<Constructor>` (e.g., `Option..isNone`, `List..isCons`).
3. *Field accessors*: for each field, Strata generates safe and unsafe variants.
   The default (safe) versions (e.g., `List..head`) add a precondition check
   requiring that the argument is an instance of the given constructor. The
   unsafe versions (e.g., `List..head!`) do not check this — the result is
   unspecified (an arbitrary value of the return type) if called on the wrong
   constructor.

## Functions

Strata Core functions are pure, named operations with typed input parameters
and a return type. A function may have an optional body (an expression over the
declared parameters); if absent, it is uninterpreted. Functions may also have
preconditions that restrict their domain.

The concrete syntax for a function declaration without a body is:

```
function Name<TypeArgs>(x₁ : T₁, ..., xₙ : Tₙ) : ReturnType;
```

A function with a body:

```
function Name<TypeArgs>(x₁ : T₁, ..., xₙ : Tₙ) : ReturnType
{
  body_expression
};
```

A function may be prefixed with `inline` to request inlining during the partial
evaluation transform, when applied.

### Recursive Functions

Strata supports two kinds of recursive functions: *structural recursion* over
algebraic datatypes, and *int-valued recursion* with integer termination
measures. Both single and mutually recursive functions are supported.
Recursive functions cannot be marked `inline`.

#### Structural Recursion (ADT)

Structural recursive functions are declared with the `rec` keyword, and exactly
one parameter must be annotated with `@[cases]` to indicate the algebraic
datatype argument for per-constructor axiom generation: one unfolding axiom is
generated for each constructor of the datatype, case-splitting on the `@[cases]`
parameter.

```
rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};
```

An optional `decreases` clause specifies which parameter is used as the
termination measure. It appears after the preconditions and before the body.
If omitted, the `@[cases]` parameter is used. If provided, it overrides only the
termination check — `@[cases]` still controls axiom generation.

```
rec function zipLen (@[cases] xs : IntList, ys : IntList) : int
  decreases ys
{
  if IntList..isNil(xs) then 0
  else if IntList..isNil(ys) then 0
  else 1 + zipLen(IntList..tl(xs), IntList..tl(ys))
};
```

#### Int-Valued Recursion

When the `decreases` clause specifies an expression of type `int` (rather than
a datatype-typed parameter), the function uses int-valued termination checking.
These functions do NOT require `@[cases]`.

```
rec function fib (n : int) : int
  decreases n
{
  if n <= 1 then n else fib(n - 1) + fib(n - 2)
};
```

The `decreases` expression may be an arbitrary integer expression over the
function's parameters:

```
rec function diagonal (m : int, n : int) : int
  requires m >= 0;
  requires n >= 0;
  decreases m + n
{
  if m <= 0 then (if n <= 0 then 0 else diagonal(m, n - 1))
  else diagonal(m - 1, n)
};
```

#### General Rules

Every recursive function must have at least a `@[cases]` annotation or a
`decreases` clause; Strata rejects recursive functions without a termination hint.
If a function has both `@[cases]` and an int-valued `decreases` clause,
`@[cases]` enables per-constructor axiom generation and partial evaluation,
while `decreases` is used for termination checking.

Mutually recursive functions are declared as multiple functions within a single
`rec` block:

```
rec function treeSize (@[cases] t : RoseTree) : int
{
  if RoseTree..isLeaf(t) then 1 else listSize(RoseTree..children(t))
}
function listSize (@[cases] xs : RoseList) : int
{
  if RoseList..isRNil(xs) then 0
  else treeSize(RoseList..hd(xs)) + listSize(RoseList..tl(xs))
};
```

#### Termination Checking

Termination checking is always on for all `rec` functions.

For _structural recursion_, Strata checks that recursive calls pass a
structurally smaller argument at the termination measure position. A rank
function is generated for the datatype, and each recursive call must have
strictly smaller rank than the caller's parameter.

For _int-valued recursion_, two obligations are checked at each recursive
call site:
- The measure at the call site is non-negative (`0 <= call_measure`).
- The measure strictly decreases (`call_measure < caller_measure`).

A function that fails its termination check will produce a verification failure
on its `_terminates_` obligations.

#### Current Limitations

- Recursive functions must be declared at the top level (not as local
  declarations inside procedures).
- Only single-expression termination measures are supported; lexicographic
  measures are not yet supported.
- There is no way currently to give additional information for the
  proofs of non-negativity for int-valued measures. For example,
  using the measure `listLen(l1) + listLen(l2)` will produce currently
  unprovable obligations about the nonnegativity of `listLen` over
  arbitrary lists.

## Axioms

Axioms are propositions assumed to be true throughout a Strata Core program.
It is the responsibility of the user to ensure that axioms are consistent.

The concrete syntax is:

```
axiom [label]: expression;
```

## Commands and Statements

Strata Core extends the generic `Imperative` commands with a procedure call
command. A {name CmdExt}`CmdExt` is either a standard `Imperative.Cmd` or
a `call` to a named procedure with a list of arguments.

{docstring Core.CmdExt}

Each call argument specifies whether the corresponding parameter is passed by
value (input), by mutable reference (input-output), or as an output-only
variable.

{docstring Core.CallArg}

A Strata Core `Statement` is an `Imperative.Stmt` parameterized by Core's
expression type and extended command type. Strata provides convenience
abbreviations: `Statement.init`, `Statement.set`, `Statement.havoc`,
`Statement.assert`, `Statement.assume`, `Statement.call`, and
`Statement.cover`.

## Procedures

A *procedure* is the main verification unit in Strata Core. It is a named
signature with typed input and output parameters, a specification (contract),
and an optional implementation body.

The concrete syntax of a procedure declaration is (`[]` denotes optional):

```
procedure Name<TypeArgs>([out/inout] x₁ : T₁, ..., [out/inout] xₙ : Tₙ)
spec {
  [free] requires [label]: P;
  [free] ensures  [label]: Q;
}
{ body };
```

The {name Procedure.Header}`Procedure.Header` structure captures the procedure's
name, type parameters, and input/output signatures.

{docstring Core.Procedure.Header}

### Parameters

Each procedure has three groups of parameters:

1. *Input parameters* (`name : T`): Passed by value from the caller to the
   callee. They are immutable within the procedure body.
2. *Output parameters* (`out name : T`): Passed by value from the callee back
   to the caller. They are mutable within the procedure body and their final
   values are returned to the caller.
3. *Input-output parameters* (`inout name : T`): Appear in both input and
   output roles. The input value is the pre-state and the output value is the
   post-state.

Parameter names must be disjoint from each other.

### Specification

A procedure's specification ({name Procedure.Spec}`Procedure.Spec`) consists of
two parts: preconditions (`requires`) that must hold before invocation, and
postconditions (`ensures`) that must hold on return. Postconditions may reference
`old v` for pre-state values of inout variables.

{docstring Core.Procedure.Spec}

Each specification clause is represented by {name Procedure.Check}`Procedure.Check`,
pairing a boolean expression with an optional `Free` attribute and metadata.

{docstring Core.Procedure.Check}

The {name Procedure.CheckAttr}`Procedure.CheckAttr` type controls whether a
clause is checked or free. A free precondition is assumed by the implementation
but not asserted at call sites; a free postcondition is assumed upon return from
calls but not checked on exit from implementations.

{docstring Core.Procedure.CheckAttr}

### The `old` expression

Postconditions and procedure bodies are *two-state contexts*: they can refer to
both the pre-state (on entry) and the post-state (on exit) of a procedure
invocation. The pre-state value of an inout parameter `v` is denoted by `old v`.
`old` is not allowed in preconditions.

### Procedure calls

A procedure is invoked via the `call` statement:

```
call ProcName([out/inout] e₁, ..., [out/inout] eₙ);
```

Note that `out` and `inout` keywords can only be attached when `eᵢ` is a variable.

### Body and verification

If a procedure has a non-empty body, the preconditions are assumed to hold on
entry, the body is executed, and the postconditions must hold on exit. If the
body is empty, the procedure is abstract and can only be reasoned about via its
contract.

### The Procedure type

{docstring Core.Procedure}

## Programs

A Strata Core program is an ordered list of declarations. Each declaration is
one of:

- a type declaration (abstract type, type synonym, or algebraic datatype),
- an axiom,
- a `distinct` declaration (asserting that a list of expressions are pairwise distinct),
- a procedure,
- a (non-recursive) function, or
- a mutually recursive function block.

{docstring Core.Decl}

{docstring Core.Program}
