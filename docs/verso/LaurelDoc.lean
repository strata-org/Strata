/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.LaurelAST
import Strata.Languages.Laurel.LaurelTypes
import Strata.Languages.Laurel.LaurelCompilationPipeline
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.ModifiesClauses

open Strata.Laurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in the same process and
-- environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

/-- Markdown documentation for all Laurel passes, including their
    `comesBefore`/`comesAfter` ordering rationales. Note: pass
    `documentation`/`reason` strings are rendered as Markdown, so avoid raw
    `<angle-bracket>` text (it is treated as inline HTML and crashes Verso's
    converter); use backticks for inline code instead. -/
def laurelPipelineDocsMarkdown : String :=
  let entries := allPasses.map fun pass =>
    let base := s!"- **{pass.name}**: {pass.documentation}"
    let beforeDeps := pass.comesBefore.map fun cb =>
      s!"  - Comes before **{cb.pass.name}** because: {cb.reason}"
    let afterDeps := pass.comesAfter.map fun ca =>
      s!"  - Comes after **{ca.pass.name}** because: {ca.reason}"
    let deps := beforeDeps ++ afterDeps
    if deps.isEmpty then base
    else base ++ "\n" ++ "\n".intercalate deps
  "\n".intercalate entries.toList

/-- Markdown dependency graph for the Laurel passes, derived from the
    `comesBefore`/`comesAfter` properties. -/
def laurelPipelineDependencyGraphMarkdown : String := Id.run do
  -- Collect all edges: (source, target, reason) where source comesBefore target
  let mut edges : List (String × String × String) := []
  for pass in allPasses do
    -- `pass.comesBefore` declares: pass must run before cb.pass, i.e. pass → cb.pass
    for cb in pass.comesBefore do
      edges := edges ++ [(pass.name, cb.pass.name, cb.reason)]
    -- `pass.comesAfter` declares: pass must run after ca.pass, i.e. ca.pass → pass
    for ca in pass.comesAfter do
      edges := edges ++ [(ca.pass.name, pass.name, ca.reason)]

  -- Deduplicate edges with the same (source, target), keeping the first reason.
  edges := edges.foldl (init := []) fun acc e =>
    if acc.any (fun a => a.1 == e.1 && a.2.1 == e.2.1) then acc else acc ++ [e]

  -- Build the graph as a markdown list showing dependencies
  let mut md := "**Dependency edges** (A → B means A must run before B):\n\n"
  if edges.isEmpty then
    md := md ++ "*No ordering constraints declared.*\n"
  else
    for (src, tgt, reason) in edges do
      md := md ++ s!"- **{src}** → **{tgt}**\n  - *{reason}*\n"

  -- Add a textual rendering of the pipeline order with dependency annotations
  md := md ++ "\n**Pipeline execution order** (→ X: must run before X; ← X: must run after X):\n\n"
  md := md ++ "```\n"
  let mut idx := 1
  for pass in allPasses do
    let beforeDeps := pass.comesBefore.map (s!" → {·.pass.name}")
    let afterDeps := pass.comesAfter.map (s!" ← {·.pass.name}")
    let deps := beforeDeps ++ afterDeps
    let depStr := if deps.isEmpty then "" else String.join deps
    md := md ++ s!"{idx}. {pass.name}{depStr}\n"
    idx := idx + 1
  md := md ++ "```\n"
  return md

/-- Block command that generates documentation for all Laurel pipeline passes.
    Usage inside a `#doc` block: `{laurelPipelineDocs}` -/
@[block_command]
def laurelPipelineDocs : Verso.Doc.Elab.BlockCommandOf Unit := fun () => do
  let md := laurelPipelineDocsMarkdown
  let some ast := MD4Lean.parse md
    | Lean.throwError "Failed to parse laurelPipelineDocumentation as Markdown"
  let blocks ← ast.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
  `(Verso.Doc.Block.concat #[$blocks,*])

/-- Block command that generates a dependency graph for the Laurel pipeline passes
    based on the `comesBefore` and `comesAfter` properties.
    Usage inside a `#doc` block: `{laurelPipelineDependencyGraph}` -/
@[block_command]
def laurelPipelineDependencyGraph : Verso.Doc.Elab.BlockCommandOf Unit := fun () => do
  let md := laurelPipelineDependencyGraphMarkdown
  let some ast := MD4Lean.parse md
    | Lean.throwError "Failed to parse laurelPipelineDependencyGraph as Markdown"
  let blocks ← ast.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
  `(Verso.Doc.Block.concat #[$blocks,*])

-- A set-apart *example* box. Renders its contents inside a tinted, bordered
-- panel with an "Example" header, so concrete examples stand out from the
-- surrounding explanatory prose. Authored via the `:::example` directive below.
block_extension Block.«example» (title : Option String) where
  data := Lean.toJson (title : Option String)
  traverse _ _ _ := pure none
  toHtml := some fun _goI goB _id data contents => open Verso.Output.Html in do
    let title : Option String :=
      match Lean.fromJson? (α := Option String) data with
      | .ok t => t
      | .error _ => none
    let label := title.getD "Example"
    pure {{
      <div class="laurel-example">
        <div class="laurel-example-header">{{ label }}</div>
        <div class="laurel-example-body">{{← contents.mapM goB}}</div>
      </div>
    }}
  extraCss := [
r#"
.laurel-example {
  border: 1px solid #98B2C0;
  border-left: 4px solid #4A90E2;
  border-radius: 0.4rem;
  background: #F5F9FF;
  margin-top: var(--verso--box-vertical-margin);
  margin-bottom: var(--verso--box-vertical-margin);
  overflow: hidden;
}
.laurel-example-header {
  font-family: var(--verso-structure-font-family);
  font-style: italic;
  font-size: 0.875rem;
  font-weight: bold;
  color: #2A5680;
  background: #E4EEF8;
  padding: 0.3rem var(--verso--box-padding);
}
.laurel-example-body {
  padding: 0.2rem var(--verso--box-padding);
}
"#
  ]
  toTeX := some fun _goI goB _id _data contents => open Verso.Output.TeX in open Verso.Doc.TeX in do
    pure <| .seq <| ← contents.mapM fun b => do
      pure <| .seq #[← goB b, .raw "\n"]

/-- Configuration for the `:::example` directive: an optional title shown in the
    box header (defaults to "Example"). -/
structure LaurelExampleConfig where
  title : Option String := none

open Verso.ArgParse in
instance : Verso.ArgParse.FromArgs LaurelExampleConfig Verso.Doc.Elab.DocElabM where
  fromArgs := LaurelExampleConfig.mk <$>
    ((positional' `title <&> some) <|> pure none)

/-- Sets its contents apart in a styled *example* box (see `Block.example`).
    Optionally takes a title: `:::example "Arithmetic join"` … `:::`. -/
@[directive]
def «example» : Verso.Doc.Elab.DirectiveExpanderOf LaurelExampleConfig
  | {title}, stxs => do
    let args ← stxs.mapM Verso.Doc.Elab.elabBlock
    ``(Verso.Doc.Block.other (Block.«example» $(Lean.quote title)) #[ $[ $args ],* ])

#doc (Manual) "The Laurel Language" =>
%%%
shortTitle := "Laurel"
%%%

# Introduction

Laurel is an intermediate verification language designed to serve as a target for popular
garbage-collected languages that include imperative features, such as Java, Python, and
JavaScript, where those languages have been extended to include verification specific constructs.
Laurel tries to include any features that are common to those three languages.

This manual follows the language from the ground up: it first describes Laurel's
types, then its unified expression/statement model, then procedures and whole
programs. It then turns to type checking, done in a bidirectional way, and finally to the translation
pipeline that lowers a checked Laurel program to Strata Core.

## Features

In the feature lists below, items marked *(WIP)* are designed or planned but not
yet fully implemented; everything else is available today.

Laurel enables doing various forms of analyses :
- Type checking
- Testing
- (WIP) Property-based testing
- (WIP) Bounded symbolic execution
- Unbounded symbolic execution
- (WIP) Data-flow analysis

## Shared language features

Here are some Laurel language features that are shared between the source languages:
- Statements such as loops and return statements
- Mutation of variables, including in expressions
- Reading and writing of fields of references
- Object oriented concepts such as inheritance, type checking, up and down casting and
  dynamic dispatch
- (WIP) Error handling via exceptions
- (WIP) Procedures types and procedures as values
- (WIP) Parametric polymorphism

Laurel does not distinguish between statements and expressions.
Expression-like or statement-like constructs can occur in the same positions.
Each statement-expression has a type, which for statement-like constructs might be void.

## Verification features
On top of the above features, Laurel adds features that are useful specifically for verification:
- Assert and assume statements
- Loop invariants
- Pre and postconditions for procedures
- Modifies and reads clauses for procedures
- (WIP) Decreases clauses for procedures and loops
- (WIP) Immutable fields and constructors that support assigning to them
- (WIP) Constrained types
- (WIP) Type invariants
- Forall and exists expressions
- (WIP) Old and fresh expressions
- Unbounded integer and real types
- To be designed constructs for supporting proof writing

## Verification design choices
A peculiar choice of Laurel is that it does not require imperative code to be encapsulated
using a functional specification. A reason for this is that sometimes the imperative code is
as readable as the functional specification. For example:
```
procedure increment(counter: Counter)
  // In Laurel, this ensures clause can be left out
  ensures counter.value == old(counter.value) + 1
{
  counter.value := counter.value + 1;
};
```

## Internal constructors and properties
Some constructors and properties in the Laurel AST are marked for internal usage and should not be needed by Laurel users.
Having these internal properties and constructors allows us to define an incremental translation to Core which improves maintainability.

# Types

Laurel's types come in two groups: those a user can write — primitives,
collections, and user-defined types — and a few internal constructors the
implementation introduces that have no surface syntax.

The {name Strata.Laurel.HighType}`HighType` type enumerates every type Laurel
tracks. Alongside the user-writable types it also includes internal constructors
(such as `Unknown` and `MultiValuedExpr`) that the compiler introduces
during resolution and later passes; these have no surface syntax.

{docstring Strata.Laurel.HighType}

## User-Defined Types

User-defined types come in two categories: composite types and constrained types.

Composite types have fields and procedures, and may extend other composite types. Fields
declare whether they are mutable and specify their type.

{docstring Strata.Laurel.CompositeType}

{docstring Strata.Laurel.Field}

Constrained types are defined by a base type and a constraint over the values of the base
type. Algebraic datatypes can be encoded using composite and constrained types.

{docstring Strata.Laurel.ConstrainedType}

{docstring Strata.Laurel.TypeDefinition}

# Sequences and Arrays
%%%
tag := "sec-sequences-arrays"
%%%

Laurel provides two collection types that share a subscript syntax but differ in their
semantics:

- `Seq<T>` — immutable value sequences. Operations like functional update produce new
  sequences, leaving the input unchanged.
- `Array<T>` — mutable, heap-backed arrays.

Their equality and aliasing behaviour is covered under [Equality and aliasing](#equality-and-aliasing) below.

Currently `Array<T>` is supported only for `T = int`; other element types are
rejected by the pre-pass validator. `Seq<T>` supports any element type.

## Sequence literals

Square-bracket literals construct a `Seq<T>`:

```
var s: Seq<int> := [1, 2, 3];
```

The empty literal `[]` produces `Sequence.empty()`.

## Subscript syntax

The expression `s[i]` reads the element at index `i`:

```
assert s[0] == 1;
```

On a `Seq<T>`, `s[i := v]` produces a new sequence with index `i` set to `v`:

```
var t: Seq<int> := s[0 := 99];  // t differs from s at index 0
```

On an `Array<T>`, `a[i] := v` updates the array in place:

```
var a: Array<int> := [1, 2, 3];
a[0] := 42;
assert a[0] == 42;
```

Out-of-bounds access is a proof obligation. `Sequence.select`,
`Sequence.update`, `Sequence.take`, and `Sequence.drop` carry preconditions
that the index or length argument is in range; the subscript sugar inherits
them. A proof obligation is generated at each subscript site — both
in imperative code and in pure positions like `requires`/`ensures` clauses,
quantifier bodies, and function bodies. If the index cannot be shown to be
in bounds, verification fails with an `outOfBoundsAccess` diagnostic. This
matches how division by zero is checked.

## Sequence operations

The `Sequence` namespace exposes the following operations:

- `Sequence.empty()` — the empty sequence
- `Sequence.build(s, v)` — append `v` to the end of `s`
- `Sequence.select(s, i)` — read index `i`; equivalent to `s[i]`
- `Sequence.update(s, i, v)` — functional update; equivalent to `s[i := v]`
- `Sequence.length(s)` — length
- `Sequence.append(s1, s2)` — concatenate two sequences
- `Sequence.contains(s, v)` — membership test
- `Sequence.take(s, n)` — prefix of length `n`
- `Sequence.drop(s, n)` — suffix after the first `n` elements

## Array length

`Array.length(a)` returns the length of an array. It requires its argument to be
of type `Array<T>`.

## Array to sequence conversion

`Sequence.fromArray(a)` returns a `Seq<T>` snapshot of an `Array<T>`'s current
contents. The snapshot is independent: subsequent mutations to the array are
not reflected in the returned sequence.

```
var a: Array<int> := [1, 2, 3];
var s: Seq<int> := Sequence.fromArray(a);
a[0] := 99;
assert s[0] == 1;   // the snapshot still holds the original value
assert a[0] == 99;
```

This is the supported idiom for extracting values out of an array. Laurel does
not support implicit `Array<T>` → `Seq<T>` conversion, nor the reverse: there is
no `Seq<T>` → `Array<T>` conversion. Construct an array directly from a literal,
e.g. `var a: Array<int> := [1, 2, 3]`.

## Common mistakes

A pre-pass validator flags five common misuses with helpful messages:

- Using `a[i := v]` (functional update) on an `Array<T>`:

  ```
  var a: Array<int> := [1, 2, 3];
  var b: Array<int> := a[0 := 99];
  //                   ~~~~~~~~~~
  // error: `a[i := v]` is not supported on `Array<T>`: arrays are mutable.
  ```

- Using `s[i] := v` (destructive update) on a `Seq<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  s[0] := 42;
  // ~~~~
  // error: `s[i] := v` is not allowed: sequences (`Seq<T>`) are immutable.
  ```

- Calling `Array.length` on something that is not an `Array<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  assert Array.length(s) == 3;
  //     ~~~~~~~~~~~~~~~
  // error: `Array.length` requires an argument of type `Array<T>`, got `Seq<int>`.
  ```

- Calling `Sequence.fromArray` on something that is not an `Array<T>`:

  ```
  var s: Seq<int> := [1, 2, 3];
  var t: Seq<int> := Sequence.fromArray(s);
  //                 ~~~~~~~~~~~~~~~~~~~~~
  // error: `Sequence.fromArray` requires an argument of type `Array<T>`,
  //        got `Seq<int>`.
  ```

- Declaring `Array<T>` with a `T` other than `int` (not yet implemented at the
  Laurel layer):

  ```
  var a: Array<bool> := [true, false];
  //     ~~~~~~~~~~~
  // error: `Array<T>` is currently only supported for `T = int`.
  ```

## Internal representation

Arrays are represented internally by a synthetic `$Array` composite with a single
`$data: Seq<int>` field (the `int` element type matches the current
`Array<int>`-only restriction). The `$` prefix is a naming convention used for
compiler-internal names to avoid collisions with user-declared types. The
`$Array` composite is only injected into programs that actually use `Array<T>`.

## Equality and aliasing
%%%
tag := "equality-and-aliasing"
%%%

`Seq<T>` has *value* semantics and `Array<T>` has *reference* semantics, and
this is what distinguishes the two types.

A `Seq<T>` is compared by content: two sequences are equal exactly when they
hold the same elements, regardless of how each was constructed. Sequences are
immutable, so there is no aliasing to worry about.

An `Array<T>` is a heap reference. Assigning an array to a new variable creates
an *alias* — both names refer to the same underlying array, so a mutation
through one is visible through the other — and `==` compares *identity*, not
contents:

```
var a1: Array<int> := [1, 2, 3];
var b: Array<int> := a1;        // alias of a1
b[0] := 99;
assert a1[0] == 99;            // mutation visible through a1
assert a1 == b;                 // holds: same reference

var a2: Array<int> := [1, 2, 3];
assert a1 != a2;                // holds: distinct references, equal contents
```

### Arrays in datatypes

`Array<T>` may be used as a datatype constructor argument:

```
datatype Wrapped { Wrap(arr: Array<int>) }
```

Reference semantics carry through the field: a datatype value that stores an
array compares by reference on that field. Two values built from the same
array are equal; two built from distinct arrays are not, even with identical
contents:

```
var a1: Array<int> := [1, 2, 3];
var a2: Array<int> := [1, 2, 3];
var w1: Wrapped := Wrap(a1);
var w2: Wrapped := Wrap(a1);   // same array as w1
var w3: Wrapped := Wrap(a2);   // distinct array, equal contents
assert w1 == w2;               // holds: same reference
assert w1 != w3;               // holds: different references
```

For a datatype field with value semantics, store a `Seq<T>` instead — take a
snapshot of the array's contents with `Sequence.fromArray(arr)`:

```
datatype WrappedSeq { WrapSeq(items: Seq<int>) }
// ...
var w1: WrappedSeq := WrapSeq(Sequence.fromArray(a1));
var w2: WrappedSeq := WrapSeq(Sequence.fromArray(a2));
assert w1 == w2;               // holds when a1, a2 have equal contents
```

# Expressions and Statements

Laurel uses a unified `StmtExpr` type that contains both expression-like and statement-like
constructs. This avoids duplication of shared concepts such as conditionals and variable
declarations.

## Operations

{docstring Strata.Laurel.Operation}

## The StmtExpr Type

{docstring Strata.Laurel.StmtExpr}

## Metadata

All AST nodes can carry metadata via the `AstNode` wrapper.

{docstring Strata.Laurel.AstNode}

# Procedures

Procedures are the main unit of specification and verification in Laurel.

{docstring Strata.Laurel.Procedure}

{docstring Strata.Laurel.Parameter}

{docstring Strata.Laurel.Body}

# Programs

A Laurel program consists of procedures, global variables, type definitions, and constants.

{docstring Strata.Laurel.Program}

# Type checking

Type checking is woven into the resolution pass: every
{name Strata.Laurel.StmtExpr}`StmtExpr` gets a {name Strata.Laurel.HighType}`HighType`, and
mismatches against the surrounding context become diagnostics. The implementation is in
`Resolution.lean`.

## Design

### Bidirectional type checking

There are two operations on expressions, written here in standard
bidirectional notation:

```
Γ ⊢ e ⇒ A            -- "e synthesizes A"     (Synth.resolveStmtExpr)
Γ ⊢ e ⇐ A            -- "e checks against A"  (Check.resolveStmtExpr)
```

Synthesis returns a type inferred from the expression itself; checking
verifies that the expression has a given expected type. Each construct
picks a mode based on whether its type is determined locally (synth) or
by context (check). The two judgments are connected by a single
change-of-direction rule, *subsumption*:

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

The two judgments are implemented as
{name Strata.Laurel.Resolution.Synth.resolveStmtExpr}`Synth.resolveStmtExpr` and
{name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr`:

{docstring Strata.Laurel.Resolution.Synth.resolveStmtExpr}

{docstring Strata.Laurel.Resolution.Check.resolveStmtExpr}

### Gradual typing

The relation `<:` (used in \[⇐\] Sub) is built from three Lean functions —
{name Strata.Laurel.isSubtype}`isSubtype`, {name Strata.Laurel.isConsistent}`isConsistent`,
and {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`:

{docstring Strata.Laurel.isSubtype}

{docstring Strata.Laurel.isConsistent}

{docstring Strata.Laurel.isConsistentSubtype}

## Typing rules

Each construct is given as a derivation. `Γ` is the current lexical scope (see
{name Strata.Laurel.ResolveState}`ResolveState`'s `scope`); it threads identically through
every premise and conclusion unless a rule explicitly extends it (written `Γ, x : T`).

Each rule is tagged with `[⇒]` (synthesis) or `[⇐]` (checking) to make the
direction explicit. The {ref "rules-procedure"}[*Procedure*] rule is the one
exception: it is a top-level well-formedness judgment and carries no direction
tag.

The following notation recurs throughout the rules:

- $`A <: B` — subtyping ({name Strata.Laurel.isSubtype}`isSubtype`); see
  *Gradual typing* above. In a *checking* premise or side condition (e.g.
  \[⇐\] Sub, \[⇐\] If-NoElse, \[⇐\] Assign, the check-mode operator rules, and
  \[⇐\] Hole-Some) the boundary check is the gradual consistent-subtype
  relation $`<:_\sim` below — the implementation routes every such check
  through {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`, never
  bare $`<:` — so $`\mathsf{Unknown}` is admitted on either side.
- $`A \sim B` — the *consistency* relation
  {name Strata.Laurel.isConsistent}`isConsistent`: symmetric, with
  $`\mathsf{Unknown}` acting as a wildcard.
- $`A <:_\sim B` — the *consistent-subtype* relation
  {name Strata.Laurel.isConsistentSubtype}`isConsistentSubtype`, the gradual
  combination of the two above.
- $`\mathsf{Numeric}\;T` — a predicate holding when $`T` is consistent with one
  of $`\mathsf{TInt}`, $`\mathsf{TReal}`, $`\mathsf{TFloat64}`, or
  $`\mathsf{TBv}_w` (a bitvector of any width $`w`), with $`\mathsf{Unknown}`
  admitted as the gradual escape hatch.
- $`\dashv \Gamma'` — a rule's *output scope*: the judgment threads $`\Gamma` in
  and produces $`\Gamma'` out. Only \[⇐\] Var-Declare extends the scope; the
  block rules thread it statement-to-statement (the $`\Gamma_{i-1} \to
  \Gamma_i` chain in \[⇐\] Block / \[⇒\] Block-Synth).
- $`\rightsquigarrow \text{error: …}` — the rule emits an error and aborts; no
  type is produced.
- $`[\text{emits …}]` — the rule produces its type but also emits a diagnostic.
- $`\mapsto` — elaboration: the construct is rewritten to the form on the right.

The Index below links to each construct's subsection.

### Index

- {ref "rules-subsumption"}[*Subsumption*] — \[⇐\] Sub
- {ref "rules-literals"}[*Literals*] — \[⇒\] Lit-Int, \[⇒\] Lit-Bool, \[⇒\] Lit-String, \[⇒\] Lit-Decimal
- {ref "rules-variables"}[*Variables*] — \[⇒\] Var-Local, \[⇒\] Var-Field, \[⇒\] Var-Declare
- {ref "rules-control-flow"}[*Control flow*] — \[⇐\] If, \[⇐\] If-NoElse,
  \[⇒\] If-Synth, \[⇒\] If-Synth-NoElse;
  \[⇐\] Block, \[⇒\] Block-Synth, \[⋄\] Synth-Discard,
  \[⇒\] Empty-Block; \[⇒\] Exit;
  \[⇒\] Return-None-Void, \[⇒\] Return-None-Single, \[⇒\] Return-None-Multi,
  \[⇒\] Return-Some, \[⇒\] Return-Void-Error,
  \[⇒\] Return-Multi-Error; \[⇒\] While
- {ref "rules-verification-statements"}[*Verification statements*] — \[⇒\] Assert, \[⇒\] Assume
- {ref "rules-assignment"}[*Assignment*] — \[⇒\] Assign, \[⇐\] Assign
- {ref "rules-calls"}[*Calls*] — \[⇒\] Static-Call, \[⇒\] Static-Call-Multi,
  \[⇒\] Instance-Call, \[⇒\] Instance-Call-Multi
- {ref "rules-primitive-operations"}[*Primitive operations*] — \[⇒\] Op-Bool, \[⇒\] Op-Cmp, \[⇒\] Op-Eq,
  \[⇒\] Op-Arith, \[⇒\] Op-Concat; \[⇐\] Op-Arith, \[⇐\] Op-Bool
- {ref "rules-object-forms"}[*Object forms*] — \[⇒\] New-Ok, \[⇒\] New-Fallback; \[⇒\] AsType; \[⇒\] IsType;
  \[⇒\] RefEq; \[⇒\] PureFieldUpdate
- {ref "rules-subscript"}[*Subscript*] — \[⇒\] Subscript-Read, \[⇒\] Subscript-Update, \[⇒\] SubscriptWrite
- {ref "rules-verification-expressions"}[*Verification expressions*] — \[⇒\] Quantifier, \[⇒\] Assigned, \[⇐\] Old,
  \[⇒\] Old-Synth, \[⇒\] Fresh, \[⇐\] ProveBy, \[⇒\] ProveBy-Synth
- {ref "rules-self-reference"}[*Self reference*] — \[⇒\] This-Inside, \[⇒\] This-Outside
- {ref "rules-untyped-forms"}[*Untyped forms*] — \[⇒\] Abstract / All
- {ref "rules-contract-of"}[*ContractOf*] — \[⇒\] ContractOf-Bool, \[⇒\] ContractOf-Set, \[⇒\] ContractOf-Error
- {ref "rules-holes"}[*Holes*] — \[⇐\] Hole-Some, \[⇐\] Hole-None, \[⇒\] Hole-Synth-None, \[⇒\] Hole-Synth-Some
- {ref "rules-procedure"}[*Procedure*] — Procedure

### Subsumption
%%%
tag := "rules-subsumption"
%%%

$$`\frac{\Gamma \vdash e \Rightarrow A \quad A <: B}{\Gamma \vdash e \Leftarrow B} \quad \text{([⇐] Sub)}`

Fallback in {name Strata.Laurel.Resolution.Check.resolveStmtExpr}`Check.resolveStmtExpr` whenever no bespoke check
rule applies.

### Literals
%%%
tag := "rules-literals"
%%%

$$`\frac{}{\Gamma \vdash \mathsf{LiteralInt}\;n \Rightarrow \mathsf{TInt}} \quad \text{([⇒] Lit-Int)}`

{docstring Strata.Laurel.Resolution.Synth.litInt}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralBool}\;b \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Lit-Bool)}`

{docstring Strata.Laurel.Resolution.Synth.litBool}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralString}\;s \Rightarrow \mathsf{TString}} \quad \text{([⇒] Lit-String)}`

{docstring Strata.Laurel.Resolution.Synth.litString}

$$`\frac{}{\Gamma \vdash \mathsf{LiteralDecimal}\;d \Rightarrow \mathsf{TReal}} \quad \text{([⇒] Lit-Decimal)}`

{docstring Strata.Laurel.Resolution.Synth.litDecimal}

### Variables
%%%
tag := "rules-variables"
%%%

$$`\frac{\Gamma(x) = T}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Local}\;x) \Rightarrow T} \quad \text{([⇒] Var-Local)}`

{docstring Strata.Laurel.Resolution.Synth.varLocal}

$$`\frac{\Gamma \vdash e \Rightarrow \_ \quad \Gamma(f) = T_f}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Field}\;e\;f) \Rightarrow T_f} \quad \text{([⇒] Var-Field)}`

{docstring Strata.Laurel.Resolution.Synth.varField}

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, T_x\rangle) \Rightarrow \mathsf{TVoid} \quad \dashv \quad \Gamma, x : T_x} \quad \text{([⇒] Var-Declare)}`

$`x \notin \mathrm{dom}(\Gamma)` is a soft side condition rather than a
hard premise: when $`x` is already bound in the current scope the rule still
fires, $`[\text{emits “Duplicate definition …”}]`, and extends the scope —
but with an *unresolved* placeholder instead of $`x : T_x`, so later uses of
$`x` don't cascade further type errors.

{docstring Strata.Laurel.Resolution.Check.varDeclare}

### Control flow
%%%
tag := "rules-control-flow"
%%%

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \Gamma \vdash \mathit{elseBr} \Leftarrow T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Leftarrow T} \quad \text{([⇐] If)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Leftarrow T \quad \mathsf{TVoid} <: T}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Leftarrow T} \quad \text{([⇐] If-NoElse)}`

{docstring Strata.Laurel.Resolution.Check.ifThenElse}

When an `if` appears in *operand* position — where no expected type is
available to push down (e.g. as an operand of $`==` / $`<` / $`+\!+`,
whose operands are synthesized) — the synth counterpart fires instead.
With an `else`, both branches are synthesized and their types must be
mutually consistent ($`\sim`, the symmetric gradual relation);
inconsistent branches $`[\text{emits “'if' branches have incompatible
types X and Y”}]` and synthesize $`\mathsf{Unknown}`. The result is the
join $`T_t \sqcup T_e` of the two branch types, so when one branch is a
hole ($`\mathsf{Unknown}`) the join promotes to the other branch's
concrete type, and the synthesized type is independent of branch order.
Without an `else`, the missing branch cannot produce a value, so the `if`
synthesizes $`\mathsf{TVoid}`.

:::example "`if` in operand position"
- `(if c then 1 else 2) == y` — both branches $`\mathsf{TInt}`, so the `if` synthesizes $`\mathsf{TInt}`
- `if c then 1 else <?>` — the hole branch promotes; synthesizes $`\mathsf{TInt}`
- `if c then 1 else "x"` — incompatible branches: *'if' branches have incompatible types 'int' and 'string'*, synthesizes $`\mathsf{Unknown}`
- `if c then 1` (no `else`) — synthesizes $`\mathsf{TVoid}`
:::

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow T_t \quad \Gamma \vdash \mathit{elseBr} \Rightarrow T_e \quad T_t \sim T_e}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Rightarrow T_t \sqcup T_e} \quad \text{([⇒] If-Synth)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow \_}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] If-Synth-NoElse)}`

{docstring Strata.Laurel.Resolution.Synth.ifThenElse}

A non-empty block is typed by splitting its statement list into the
*last* statement and the statements before it. The last statement
carries the block's value and inherits the surrounding expected type;
each earlier statement runs only for its effect — written
$`\Gamma \vdash s\;\diamond` (*effect position*: the statement's value
is discarded). The check and synth rules share this shape, differing
only in how the last statement is treated:

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \;\diamond \;\dashv\; \Gamma_i \;\;(1 \le i \le n) \quad \Gamma_n \vdash \mathit{last} \Leftarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n; \mathit{last}]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block)}`

$$`\frac{\Gamma_0 = \Gamma \quad \Gamma_{i-1} \vdash s_i \;\diamond \;\dashv\; \Gamma_i \;\;(1 \le i \le n) \quad \Gamma_n \vdash \mathit{last} \Rightarrow T}{\Gamma \vdash \mathsf{Block}\;[s_1; \ldots; s_n; \mathit{last}]\;\mathit{label} \Rightarrow T} \quad \text{([⇒] Block-Synth)}`

\[⇐\] Block fires whenever an expected type $`T` is supplied (procedure
bodies, branches, loop bodies, assignment RHS, call arguments);
\[⇒\] Block-Synth fires in operand position, where no expected type is
available (e.g. $`\{\,x := 1;\; x\,\} == y`), synthesizing the last
statement's type as the block's value type.

When the block itself sits in statement position ($`T = \mathsf{TVoid}`)
the last statement is in effect position too: its premise becomes
$`\mathit{last}\;\diamond` rather than $`\mathit{last} \Leftarrow
\mathsf{TVoid}`, so a trailing call discards its result and
$`\{\ldots;\,\mathit{foo}()\}` type-checks as a statement even when
`foo` returns a non-void type.

The effect-position judgment $`\Gamma \vdash s\;\diamond` synthesizes
the statement and discards the result:

$$`\frac{\Gamma \vdash s \Rightarrow \_ \;\dashv\; \Gamma'}{\Gamma \vdash s \;\diamond \;\dashv\; \Gamma'} \quad \text{([⋄] Synth-Discard)}`

Every expression in statement position is synthesized and its type
discarded. Statement-shaped forms (`Var-Declare`, `Assign`, `Assert`,
`Assume`, `While`, `Exit`, `Return`) synthesize $`\mathsf{TVoid}`;
value-producing forms (calls, `IncrDecr`, literals, etc.) synthesize
their natural type, which is then discarded. This means any expression
is accepted in statement position — the `f(x);` idiom works regardless
of `f`'s return type, and `x++;` is admitted even though `++`
synthesizes the target's type.

Only `Var (.Declare …)` actually extends the scope $`\Gamma_i`; every
other statement leaves it unchanged. The block opens a fresh nested
scope, so declarations made inside don't leak out — once the block ends,
the surrounding $`\Gamma` is restored. It also emits a
`"dead code after '<terminator>'"` diagnostic when an `Exit` or
`Return` is followed by further statements in the same block.

Pushing $`T` into the last statement (rather than synthesizing the whole
block and applying \[⇐\] Sub at the boundary) means a type mismatch is
reported at the offending subexpression's source location, and the
expectation keeps propagating through nested `Block` / `IfThenElse` /
`Hole` / `Quantifier` constructs that have their own check rules.

$$`\frac{}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Empty-Block)}`

The empty block has a fixed type and is the only block-level rule that
synthesizes unconditionally. \[⇐\] Block and \[⇒\] Block-Synth always
split off a *last* statement, so they never reach an empty list; the
empty case is hit only when the block is literally empty at the dispatch
site. When an empty block appears in check position with
`expected ≠ TVoid`, the standard \[⇐\] Sub rule fires at the boundary
(`Check.resolveStmtExpr`'s subsumption-fallback wildcard arm, requiring
$`\mathsf{TVoid} <: \mathit{expected}`).

{docstring Strata.Laurel.Resolution.Synth.emptyBlock}

{docstring Strata.Laurel.Resolution.Synth.block}

{docstring Strata.Laurel.Resolution.Check.block}

The $`\Gamma \vdash s\;\diamond` judgment — the \[⋄\] Synth-Discard
rule above — is the single definition of what counts as a statement in
effect position, factored out into
{name Strata.Laurel.Resolution.Check.statement}`Check.statement`:

{docstring Strata.Laurel.Resolution.Check.statement}

$$`\frac{l \in \Gamma_{\mathrm{lbl}}}{\Gamma \vdash \mathsf{Exit}\;l \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Exit)}`

`exit` is an unconditional jump out of the enclosing labeled block.
It synthesizes $`\mathsf{TVoid}` unconditionally. Labels live in their
own namespace $`\Gamma_{\mathrm{lbl}}`, populated by the surrounding
`Block` rule when its $`\mathit{label}` is `some l`. An
$`\mathsf{Exit}\;l` targeting a label not in $`\Gamma_{\mathrm{lbl}}`
is rejected.

{docstring Strata.Laurel.Resolution.Check.exit}

In the Return rules below, $`\overline{T_o}` denotes the declared
output-parameter type list of the enclosing procedure (an implicit
parameter of the rules — the procedure binds it once on entry).

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Void)}`

$$`\frac{\overline{T_o} = [T]}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Single)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-None-Multi)}`

$$`\frac{\overline{T_o} = [T] \quad \Gamma \vdash e \Leftarrow T}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Return-Some)}`

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “void procedure cannot return a value”}} \quad \text{([⇒] Return-Void-Error)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “multi-output procedure cannot use 'return e'; assign to named outputs instead”}} \quad \text{([⇒] Return-Multi-Error)}`

`return` is the only rule whose premises depend on the enclosing
procedure's declared outputs. The rule synthesizes $`\mathsf{TVoid}`
because `return` is a control-flow terminator: it never falls through
and produces no value for the surrounding context. The returned value
(if any) is checked against the procedure's declared output. The error
arms fire when $`\overline{T_o}`'s arity does not match the syntactic
shape of `return e`.

Regardless of which arm fires, $`e` is always elaborated — it is
checked against the declared output in the single-output case,
otherwise synthesized — so any errors inside $`e` are reported in
addition to the arity diagnostic.

The three Return-None rules all accept `return;` unconditionally.
Void-output procedures accept it naturally (Return-None-Void);
single-output procedures accept it without a subtype check
(Return-None-Single); multi-output procedures accept it as an
early-exit shorthand that leaves the named outputs at whatever they
were last assigned to (Return-None-Multi).

When the surrounding context has no enclosing procedure body (e.g.
inside a constant initializer), `answerType = none` and all Return
checks are skipped; well-formed input never produces this case.

{docstring Strata.Laurel.Resolution.Check.return}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{invs}_i \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{decreases} \Rightarrow U \quad \mathsf{Numeric}\;U \quad \Gamma \vdash \mathit{body} \Leftarrow \mathsf{Unknown}}{\Gamma \vdash \mathsf{While}\;\mathit{cond}\;\mathit{invs}\;\mathit{decreases}\;\mathit{body} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] While)}`

The body is checked at $`\mathsf{Unknown}`: control either re-enters
the loop or falls through, so the body's value type is never observed
by the surrounding context. A loop is a statement and yields no value,
so the rule synthesizes $`\mathsf{TVoid}`.

The optional $`\mathit{decreases}` clause is synthesized and required
to have a numeric type via the same $`\mathsf{Numeric}` predicate
used by the arithmetic primitive operations. $`\mathsf{Numeric}` is
a predicate (it admits $`\mathsf{TInt}`, $`\mathsf{TReal}`,
$`\mathsf{TFloat64}`, $`\mathsf{TBv}_w` (a bitvector of any width), and
$`\mathsf{Unknown}` as the gradual escape hatch), not a single type, so
the clause runs in synth mode rather than check mode.

{docstring Strata.Laurel.Resolution.Check.while}

### Verification statements
%%%
tag := "rules-verification-statements"
%%%

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assert}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assert)}`

{docstring Strata.Laurel.Resolution.Check.assert}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assume}\;\mathit{cond} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Assume)}`

{docstring Strata.Laurel.Resolution.Check.assume}

### Assignment
%%%
tag := "rules-assignment"
%%%

$$`\frac{\Gamma \vdash \mathit{targets}_i \Rightarrow T_i \quad \Gamma \vdash e \Leftarrow \mathit{ExpectedTy}}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathit{ExpectedTy}} \quad \text{([⇒] Assign)}`

where `ExpectedTy = T_1` if `|targets| = 1` and `MultiValuedExpr [T_1; …; T_n]` otherwise.
The target's declared type `T_i` comes from the variable's scope entry (for
{name Strata.Laurel.Variable.Local}`Local` and {name Strata.Laurel.Variable.Field}`Field`)
or from the {name Strata.Laurel.Variable.Declare}`Declare`-bound parameter type. The
RHS receives `ExpectedTy` via `Check.resolveStmtExpr`, so bidirectional rules in the
RHS propagate the assignment's type into nested constructs. The
assignment synthesizes `ExpectedTy` — populating the surrounding
context with the target's type while the RHS is checked against it.

{docstring Strata.Laurel.Resolution.Synth.assign}

$$`\frac{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Rightarrow \mathit{ExpectedTy} \quad T = \mathsf{TVoid} \lor \mathit{ExpectedTy} <: T}{\Gamma \vdash \mathsf{Assign}\;\mathit{targets}\;e \Leftarrow T} \quad \text{([⇐] Assign)}`

The check rule synthesizes the assignment's type via \[⇒\] Assign
and then runs the standard \[⇐\] Sub boundary check `ExpectedTy <: T`
— *unless* `T = TVoid`, the marker for statement position. Pushing
`TVoid` through subsumption would only succeed when the LHS is itself
void, which would reject every non-void assignment used as a
statement, so the subsumption is skipped and the synthesized value is
discarded.

{docstring Strata.Laurel.Resolution.Check.assign}

### Calls
%%%
tag := "rules-calls"
%%%

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and output } [T'] \text{ (single output)} \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow T'} \quad \text{([⇒] Static-Call)}`

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T_1; \ldots; T_n],\; n \ge 2 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Static-Call-Multi)}`

{docstring Strata.Laurel.Resolution.Synth.staticCall}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and output } [T'] \text{ (single output)} \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow T'} \quad \text{([⇒] Instance-Call)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and outputs } [T_1; \ldots; T_n],\; n \ge 2 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Instance-Call-Multi)}`

The callee is resolved against either an instance procedure or a
static procedure (the latter handles uniformly-dispatched call syntax
where the receiver is forwarded as `self`). Output arity is forwarded
identically to
{name Strata.Laurel.Resolution.Synth.staticCall}`Synth.staticCall`'s
single-vs-multi split. In both call families the single- and multi-output
rules differ only in the *output* arity; argument checking is the same, and
surplus arguments (beyond the declared parameters, or when the callee is
unresolved) are checked against $`\mathsf{Unknown}` rather than flagged as an
arity error. A zero-output ($`n = 0`) procedure call is the third case in the
arity split: it synthesizes $`\mathsf{TVoid}` rather than a
$`\mathsf{MultiValuedExpr}`.

{docstring Strata.Laurel.Resolution.Synth.instanceCall}

### Primitive operations
%%%
tag := "rules-primitive-operations"
%%%

`Numeric` abbreviates "consistent with one of {name Strata.Laurel.HighType.TInt}`TInt`,
{name Strata.Laurel.HighType.TReal}`TReal`,
{name Strata.Laurel.HighType.TFloat64}`TFloat64`, or
{name Strata.Laurel.HighType.TBv}`TBv` (a bitvector of any width)", with
`Unknown` admitted as the gradual escape hatch.

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad U_i <: \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Bool)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad \mathsf{Numeric}\;U_i \quad \mathit{op} \in \{\mathsf{Lt}, \mathsf{Leq}, \mathsf{Gt}, \mathsf{Geq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Cmp)}`

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad T_l \sim T_r \quad \mathit{op} \in \{\mathsf{Eq}, \mathsf{Neq}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;[\mathit{lhs}; \mathit{rhs}] \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Op-Eq)}`

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad \mathsf{Numeric}\;U_i \quad T = \bigsqcup_i U_i \text{ (consistency join)} \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Op-Arith)}`

The arithmetic synth rule mirrors $`[⇒]\,\text{Op-Eq}` but generalised
to $`n` operands. Each operand is synthesized and required to be
$`\mathsf{Numeric}` (i.e. $`\mathsf{TInt}`, $`\mathsf{TReal}`,
$`\mathsf{TFloat64}`, $`\mathsf{TBv}_w` (a bitvector of any width), or
the gradual $`\mathsf{Unknown}`). The
result type is the *consistency join* $`\bigsqcup_i U_i` — a fold of
the operand types under
{name Strata.Laurel.isConsistent}`isConsistent`'s flat lattice:
$`\mathsf{Unknown} \sqcup T = T`, $`T \sqcup T = T`, and any other
combination is rejected. The fold runs via `join`, a pure function, so
the search has no diagnostic side-effects.

:::example "Arithmetic operand join"
- `1 + 2` synthesizes $`\mathsf{TInt}`
- `1.5 + 2.5` synthesizes $`\mathsf{TReal}`
- `<?> + 1` synthesizes $`\mathsf{TInt}` — the $`\mathsf{Unknown}` operand promotes to its neighbour
- `<?> + <?>` synthesizes $`\mathsf{Unknown}`
- `1 + 2.0` is rejected: *cannot apply '+' to operands of types 'int', 'real'*
:::

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad U_i <: \mathsf{TString} \quad \mathit{op} = \mathsf{StrConcat}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow \mathsf{TString}} \quad \text{([⇒] Op-Concat)}`

{docstring Strata.Laurel.Resolution.Synth.primitiveOp}

The arithmetic and boolean families also have a check-mode rule, used
when the surrounding context provides an `expected` type. The rule
pushes the operand type into each operand via
`Check.resolveStmtExpr`, replacing the synth-then-`checkSubtype`
discipline with bidirectional check.

$$`\frac{\mathsf{Numeric}\;T \quad \Gamma \vdash \mathit{args}_i \Leftarrow T \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Leftarrow T} \quad \text{([⇐] Op-Arith)}`

$$`\frac{\mathsf{TBool} <: T \quad \Gamma \vdash \mathit{args}_i \Leftarrow \mathsf{TBool} \quad \mathit{op} \in \{\mathsf{And}, \mathsf{Or}, \mathsf{AndThen}, \mathsf{OrElse}, \mathsf{Not}, \mathsf{Implies}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Leftarrow T} \quad \text{([⇐] Op-Bool)}`

{docstring Strata.Laurel.Resolution.Check.primitiveOp}

### Object forms
%%%
tag := "rules-object-forms"
%%%

$$`\frac{\mathit{ref} \text{ is a composite or datatype, or is unresolved, or is absent from } \Gamma}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{UserDefined}\;\mathit{ref}} \quad \text{([⇒] New-Ok)}`

$$`\frac{\mathit{ref} \text{ resolves to a non-type kind}}{\Gamma \vdash \mathsf{New}\;\mathit{ref} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] New-Fallback)}`

The $`\mathsf{Unknown}` fallback fires *only* when $`\mathit{ref}` resolves to
a present definition whose kind is neither composite nor datatype. An
unresolved or out-of-scope $`\mathit{ref}` takes the New-Ok branch instead, so
the kind diagnostic that `resolveRef` already emitted is not duplicated.

{docstring Strata.Laurel.Resolution.Synth.new}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow U \quad U \sim T \lor U <: T \lor T <: U}{\Gamma \vdash \mathsf{AsType}\;\mathit{target}\;T \Rightarrow T} \quad \text{([⇒] AsType)}`

{docstring Strata.Laurel.Resolution.Synth.asType}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow U \quad U \sim T \lor U <: T \lor T <: U}{\Gamma \vdash \mathsf{IsType}\;\mathit{target}\;T \Rightarrow \mathsf{TBool}} \quad \text{([⇒] IsType)}`

{docstring Strata.Laurel.Resolution.Synth.isType}

$$`\frac{\Gamma \vdash \mathit{lhs} \Rightarrow T_l \quad \Gamma \vdash \mathit{rhs} \Rightarrow T_r \quad \mathsf{isReference}\;T_l \quad \mathsf{isReference}\;T_r \quad T_l \sim T_r}{\Gamma \vdash \mathsf{ReferenceEquals}\;\mathit{lhs}\;\mathit{rhs} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] RefEq)}`

`isReference T` holds when `T` is a {name Strata.Laurel.HighType.UserDefined}`UserDefined`
or {name Strata.Laurel.HighType.Unknown}`Unknown` type. `~` is the consistency relation
{name Strata.Laurel.isConsistent}`isConsistent` — symmetric, with the
{name Strata.Laurel.HighType.Unknown}`Unknown` wildcard.

{docstring Strata.Laurel.Resolution.Synth.refEq}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T_t \quad \Gamma(f) = T_f \quad \Gamma \vdash \mathit{newVal} \Leftarrow T_f}{\Gamma \vdash \mathsf{PureFieldUpdate}\;\mathit{target}\;f\;\mathit{newVal} \Rightarrow T_t} \quad \text{([⇒] PureFieldUpdate)}`

{docstring Strata.Laurel.Resolution.Synth.pureFieldUpdate}

### Subscript
%%%
tag := "rules-subscript"
%%%

The {ref "sec-sequences-arrays"}[*sequence and array*] subscript forms. The
read `s[i]` and functional update `s[i := v]` are values; the destructive write
`a[i] := v` is a statement. In each, the *element type* $`U` is the only thing
needed from the target: the index is checked against $`\mathsf{TInt}` and the
update/written value against $`U`, so `a[0] := true` on an `Array<int>` is
rejected here. The remaining $`\mathsf{Seq}`/$`\mathsf{Array}` misuse rules and
bounds-safety obligations are handled by
{name Strata.Laurel.validateSubscriptUsage}`ValidateSubscriptUsage` and
{name Strata.Laurel.subscriptElimPass}`SubscriptElim`, not here.

The element type is computed by a total $`\mathsf{elem}(T)` metafunction that
also decides whether the target is indexable at all. Three cases:

- $`\mathsf{unfold}\;T` is $`\mathsf{Seq}\;U` or $`\mathsf{Array}\;U`:
  $`\mathsf{elem}(T) = U`.
- $`T` is *gradual* — $`\mathsf{Unknown}` (an unresolved name or hole) or
  $`\mathsf{TCore}` — : $`\mathsf{elem}(T) = \mathsf{Unknown}`, tolerated
  silently. The index and value checks are then vacuous (anything is consistent
  with $`\mathsf{Unknown}`) and a read synthesizes $`\mathsf{Unknown}`, so no
  cascading error piles on top of the name-resolution error that was already
  reported.
- $`T` is any *concrete* non-collection (e.g. $`\mathsf{TInt}`, a composite, a
  $`\mathsf{Map}`): the subscript is rejected with `expected a sequence or
  array`, and $`\mathsf{elem}(T) = \mathsf{Unknown}` is returned only to
  suppress follow-on errors on the index and value. This mirrors how
  $`\mathsf{Fresh}` / $`\mathsf{RefEq}` reject a concrete non-reference target
  while letting $`\mathsf{Unknown}` flow.

Only the concrete-non-collection case emits a diagnostic; the gradual case is
the $`\mathsf{New}`-$`\mathsf{Fallback}`-style escape hatch.

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T \quad \Gamma \vdash i \Leftarrow \mathsf{TInt}}{\Gamma \vdash \mathsf{Subscript}\;\mathit{target}\;i\;\mathsf{none} \Rightarrow \mathsf{elem}(T)} \quad \text{([⇒] Subscript-Read)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T \quad \Gamma \vdash i \Leftarrow \mathsf{TInt} \quad \Gamma \vdash v \Leftarrow \mathsf{elem}(T)}{\Gamma \vdash \mathsf{Subscript}\;\mathit{target}\;i\;(\mathsf{some}\;v) \Rightarrow T} \quad \text{([⇒] Subscript-Update)}`

{docstring Strata.Laurel.Resolution.Synth.subscript}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow T \quad \Gamma \vdash i \Leftarrow \mathsf{TInt} \quad \Gamma \vdash v \Leftarrow \mathsf{elem}(T)}{\Gamma \vdash \mathsf{SubscriptWrite}\;\mathit{target}\;i\;v \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] SubscriptWrite)}`

{docstring Strata.Laurel.Resolution.Check.subscriptWrite}

Sequence/array literals and operations (`[…]`, `Sequence.select`,
`Array.length`, …) desugar to calls on polymorphic primitives, typed by the
{ref "rules-calls"}[*Calls*] escape hatch in
{name Strata.Laurel.Resolution.Synth.staticCall}`Synth.staticCall`: their result
type is inferred structurally from the arguments rather than checked against the
primitives' placeholder `int` signatures (so `[1, 2, 3]` synthesizes
`Seq<int>`).

### Verification expressions
%%%
tag := "rules-verification-expressions"
%%%

$$`\frac{\Gamma, x : T \vdash \mathit{body} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Quantifier}\;\mathit{mode}\;\langle x, T\rangle\;\mathit{trig}\;\mathit{body} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Quantifier)}`

{docstring Strata.Laurel.Resolution.Synth.quantifier}

$$`\frac{\Gamma \vdash \mathit{name} \Rightarrow \_}{\Gamma \vdash \mathsf{Assigned}\;\mathit{name} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Assigned)}`

{docstring Strata.Laurel.Resolution.Synth.assigned}

$$`\frac{\Gamma \vdash v \Leftarrow T}{\Gamma \vdash \mathsf{Old}\;v \Leftarrow T} \quad \text{([⇐] Old)}`

{docstring Strata.Laurel.Resolution.Check.old}

`old` is type-transparent, so it also synthesizes: in operand position
(e.g. the postcondition pattern `ensures counter.value == old(counter.value) + 1`,
where $`==` synthesizes its operands) $`v` is synthesized and its type
returned unchanged.

$$`\frac{\Gamma \vdash v \Rightarrow T}{\Gamma \vdash \mathsf{Old}\;v \Rightarrow T} \quad \text{([⇒] Old-Synth)}`

{docstring Strata.Laurel.Resolution.Synth.old}

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \mathsf{isReference}\;T}{\Gamma \vdash \mathsf{Fresh}\;v \Rightarrow \mathsf{TBool}} \quad \text{([⇒] Fresh)}`

{docstring Strata.Laurel.Resolution.Synth.fresh}

$$`\frac{\Gamma \vdash v \Leftarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Leftarrow T} \quad \text{([⇐] ProveBy)}`

{docstring Strata.Laurel.Resolution.Check.proveBy}

Like `old`, `ProveBy` is type-transparent in `v`, so it also
synthesizes: in operand position $`v` is synthesized for its type $`T`,
$`\mathit{proof}` is synthesized only for its name-resolution side
effects (its type discarded), and $`T` is returned.

$$`\frac{\Gamma \vdash v \Rightarrow T \quad \Gamma \vdash \mathit{proof} \Rightarrow \_}{\Gamma \vdash \mathsf{ProveBy}\;v\;\mathit{proof} \Rightarrow T} \quad \text{([⇒] ProveBy-Synth)}`

{docstring Strata.Laurel.Resolution.Synth.proveBy}

### Self reference
%%%
tag := "rules-self-reference"
%%%

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{some}\;T}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{UserDefined}\;T} \quad \text{([⇒] This-Inside)}`

$$`\frac{\Gamma.\mathit{instanceTypeName} = \mathsf{none}}{\Gamma \vdash \mathsf{This} \Rightarrow \mathsf{Unknown} \quad [\text{emits “‘this’ is not allowed outside instance methods”}]} \quad \text{([⇒] This-Outside)}`

{docstring Strata.Laurel.Resolution.Synth.this}

### Untyped forms
%%%
tag := "rules-untyped-forms"
%%%

$$`\frac{}{\Gamma \vdash \mathsf{Abstract}\,/\,\mathsf{All}\;\ldots \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Abstract / All)}`

{docstring Strata.Laurel.Resolution.Synth.abstract}

{docstring Strata.Laurel.Resolution.Synth.all}

### ContractOf
%%%
tag := "rules-contract-of"
%%%

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}, \mathit{unresolved}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Precondition}\;\mathit{fn} \Rightarrow \mathsf{TBool} \qquad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{PostCondition}\;\mathit{fn} \Rightarrow \mathsf{TBool}} \quad \text{([⇒] ContractOf-Bool)}`

$$`\frac{\mathit{fn} = \mathsf{Var}\;(\mathsf{.Local}\;\mathit{id}) \quad \Gamma(\mathit{id}) \in \{\mathit{staticProcedure}, \mathit{instanceProcedure}, \mathit{unresolved}\}}{\Gamma \vdash \mathsf{ContractOf}\;\mathsf{Reads}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown} \qquad \Gamma \vdash \mathsf{ContractOf}\;\mathsf{Modifies}\;\mathit{fn} \Rightarrow \mathsf{TSet}\;\mathsf{Unknown}} \quad \text{([⇒] ContractOf-Set)}`

$$`\frac{\mathit{fn} \text{ is not a } \mathsf{Var}\;(\mathsf{.Local}) \text{ resolving to a procedure or unresolved name}}{\Gamma \vdash \mathsf{ContractOf}\;\ldots\;\mathit{fn} \rightsquigarrow \text{error: “‘contractOf’ expected a procedure reference”}} \quad \text{([⇒] ContractOf-Error)}`

The $`\mathit{unresolved}` kind is admitted so an already-reported
name-resolution error is not duplicated; ContractOf-Error fires only when
$`\mathit{fn}` resolves to a *present* non-procedure definition (or is not a
local reference at all).

{docstring Strata.Laurel.Resolution.Synth.contractOf}

### Holes
%%%
tag := "rules-holes"
%%%

$$`\frac{T_h <: T}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T_h) \Leftarrow T} \quad \text{([⇐] Hole-Some)}`

{docstring Strata.Laurel.Resolution.Check.holeSome}

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Leftarrow T \quad \mapsto \quad \mathsf{Hole}\;d\;(\mathsf{some}\;T)} \quad \text{([⇐] Hole-None)}`

{docstring Strata.Laurel.Resolution.Check.holeNone}

In synth position no expected type is available to push into the hole, so
an unannotated hole synthesizes the gradual $`\mathsf{Unknown}` while an
annotated hole synthesizes its annotation $`T_h` (this is what lets
`<?> + 1` synthesize $`\mathsf{TInt}`).

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;\mathsf{none} \Rightarrow \mathsf{Unknown}} \quad \text{([⇒] Hole-Synth-None)}`

$$`\frac{}{\Gamma \vdash \mathsf{Hole}\;d\;(\mathsf{some}\;T_h) \Rightarrow T_h} \quad \text{([⇒] Hole-Synth-Some)}`

### Procedure
%%%
tag := "rules-procedure"
%%%

A procedure body is synthesized (not checked against a computed
expected type) and is resolved under a scope that includes the
procedure's input and output parameters. The Return rules above refer
to the same output list $`\overline{T_o}` that the procedure binds
here.

$$`\frac{\overline{T_o} = \mathit{proc}.\mathit{outputs}.\mathit{types} \quad \Gamma_\mathit{global},\,\mathit{params}(\mathit{proc}) \vdash \mathit{proc}.\mathit{body} \Rightarrow \_}{\Gamma_\mathit{global} \vdash \mathsf{Procedure}\;\mathit{proc}} \quad \text{(Procedure)}`

The body is synthesized and its type is discarded — there is no
constraint from the output list pushed into the body. Outputs are
matched only via `return e` (checked against $`\overline{T_o}` by
{name Strata.Laurel.Resolution.Check.return}`Check.return`) or via
named-output assignment.

{docstring Strata.Laurel.resolveProcedure}

{docstring Strata.Laurel.resolveInstanceProcedure}

# Implementation

The static semantics of Laurel are defined by `Resolution.lean`. This is where Laurel references are resolved and where type checking is done. Calling `resolve` will produce diagnostics and a `SemanticModel` that can be used to navigate between definitions and references.
If new references or definitions are created during compilation, `resolve` must be called again to get a complete model.

## Translation Pipeline

The Laurel to Core translation pipeline uses these IRs:
- Laurel
- UnorderedCoreWithLaurelTypes
- CoreWithLaurelTypes
- Core

Most of the passes are in the Laurel IR.
The transparency pass goes from `Laurel` to `UnorderedCoreWithLaurelTypes`.
The CoreGroupingAndOrdering goes from `UnorderedCoreWithLaurelTypes` to `CoreWithLaurelTypes`
And the LaurelToCoreSchemaPass goes from `CoreWithLaurelTypes` to `Core`.

## Passes

The following passes making up the compilation of Laurel to Core:

{laurelPipelineDocs}

## Pass Dependency Graph

The following graph shows the ordering constraints between passes.

{laurelPipelineDependencyGraph}

# Differences between Laurel and Core

## Language design

### Parameter lists
Parameter lists. In Laurel, input and output parameters are defined in a separate list. Inout parameters are defined by repeating the parameter name in both lists. In Core, there is a single parameter list where each parameter defines its kind (in/out/inout).

At the call-site, Laurel requires calls with multiple out parameters to occur inside an assignment, like this:
`assign x, y := multiOutCall(a, b)`
Core uses the argument list to assign the output parameters, like this:
`multiOutCall(a, b, out x, out y)`

In Laurel, an inout parameter only influences the callee's code, since it means there is a single variable that is used as input and output. On the calling side however, there is no concept of inout parameters. This is different from Core, where inout variables affect the calling side. Example of an inout being called in Core, `hasInout(inout x)`.

### Assignments to fresh and existing declarations
In Laurel, assignments can have multiple targets. Each target can be either an existing variable or a local declaration. Example:
```
var x: int;
var z: int;
assign x, var y: int, z := hasThreeOutputs()
```
In Core, when calling a procedure with multiple outputs, each output parameter must be assigned to an existing local variable. Example:
```
var x: int;
var y: int;
var z: int;
hasThreeOutputs(out x, out y, out z);
```

## Implementation

In Laurel, all verification concepts, such as assume statements, pre and postconditions, and transparency of procedures, are part of the language. In Core however, there is the concept of metadata. Concepts that relate to only one or a few analyses might not be considered concepts of the Core language, and will then be represented using metadata instead of being given a typed representation in the AST.
