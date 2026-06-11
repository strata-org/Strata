/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel
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

/-- Block command that generates documentation for all Laurel pipeline passes.
    Usage inside a `#doc` block: `{laurelPipelineDocs}` -/
@[block_command]
def laurelPipelineDocs : Verso.Doc.Elab.BlockCommandOf Unit := fun () => do
  let entries := laurelPipeline.map fun pass =>
    let base := s!"- **{pass.name}**: {pass.documentation}"
    if pass.comesBefore.isEmpty then base
    else
      let deps := pass.comesBefore.map fun cb =>
        s!"  - Comes before **{cb.pass.name}** because: {cb.reason}"
      base ++ "\n" ++ "\n".intercalate deps

  let md := "\n".intercalate entries.toList
  let some ast := MD4Lean.parse md
    | Lean.throwError "Failed to parse laurelPipelineDocumentation as Markdown"
  let blocks ← ast.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
  `(Verso.Doc.Block.concat #[$blocks,*])

/-- Block command that generates a dependency graph for the Laurel pipeline passes
    based on the `comesBefore` property.
    Usage inside a `#doc` block: `{laurelPipelineDependencyGraph}` -/
@[block_command]
def laurelPipelineDependencyGraph : Verso.Doc.Elab.BlockCommandOf Unit := fun () => do
  -- Collect all edges: (source, target, reason) where source comesBefore target
  let mut edges : List (String × String × String) := []
  for pass in laurelPipeline do
    for cb in pass.comesBefore do
      edges := edges ++ [(pass.name, cb.pass.name, cb.reason)]

  -- Build the graph as a markdown list showing dependencies
  let mut md := "**Dependency edges** (A → B means A must run before B):\n\n"
  if edges.isEmpty then
    md := md ++ "*No ordering constraints declared.*\n"
  else
    for (src, tgt, reason) in edges do
      md := md ++ s!"- **{src}** → **{tgt}**\n  - *{reason}*\n"

  -- Add a textual rendering of the pipeline order with dependency annotations
  md := md ++ "\n**Pipeline execution order:**\n\n"
  md := md ++ "```\n"
  let mut idx := 1
  for pass in laurelPipeline do
    let deps := pass.comesBefore.map (s!" → {·.pass.name}")
    let depStr := if deps.isEmpty then "" else String.join deps
    md := md ++ s!"{idx}. {pass.name}{depStr}\n"
    idx := idx + 1
  md := md ++ "```\n"

  let some ast := MD4Lean.parse md
    | Lean.throwError "Failed to parse laurelPipelineDependencyGraph as Markdown"
  let blocks ← ast.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
  `(Verso.Doc.Block.concat #[$blocks,*])

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
programs. It then turns to type checking — a per-construct reference for the
bidirectional rules — and finally to the translation pipeline that lowers a
checked Laurel program to Strata Core.

## Features

In the feature lists below, items marked *(WIP)* are designed or planned but not
yet fully implemented; everything else is available today.

Laurel enables doing various forms of verification:
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
(such as `THeap`, `Unknown`, and `MultiValuedExpr`) that the compiler introduces
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

The type of a block is the type of its last statement; non-last
statements can be of any type. The block rule
({ref "rules-control-flow"}[Block]) is what supplies the value type
for a block: it routes the surrounding $`T` to the last statement
and ignores the value of every non-last statement.

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
  and produces $`\Gamma'` out. Only \[⇐\] Var-Declare and \[⇐\] Block-Cons use
  this to extend the scope.
- $`\rightsquigarrow \text{error: …}` — the rule emits an error and aborts; no
  type is produced.
- $`[\text{emits …}]` — the rule produces its type but also emits a diagnostic.
- $`\mapsto` — elaboration: the construct is rewritten to the form on the right.

The Index below links to each construct's subsection.

### Index

- {ref "rules-subsumption"}[*Subsumption*] — \[⇐\] Sub
- {ref "rules-literals"}[*Literals*] — \[⇒\] Lit-Int, \[⇒\] Lit-Bool, \[⇒\] Lit-String, \[⇒\] Lit-Decimal
- {ref "rules-variables"}[*Variables*] — \[⇒\] Var-Local, \[⇒\] Var-Field, \[⇐\] Var-Declare
- {ref "rules-control-flow"}[*Control flow*] — \[⇐\] If, \[⇐\] If-NoElse,
  \[⇒\] If-Synth, \[⇒\] If-Synth-NoElse;
  \[⇐\] Block-Singleton, \[⇐\] Block-Cons,
  \[⇐\] Discard-Call-Cons, \[⇐\] Discard-Call-Last, \[⇒\] Skip, \[⇒\] Block-Synth; \[⇐\] Exit;
  \[⇐\] Return-None-Void, \[⇐\] Return-None-Single, \[⇐\] Return-None-Multi,
  \[⇐\] Return-Some, \[⇐\] Return-Void-Error,
  \[⇐\] Return-Multi-Error; \[⇐\] While
- {ref "rules-verification-statements"}[*Verification statements*] — \[⇐\] Assert, \[⇐\] Assume
- {ref "rules-assignment"}[*Assignment*] — \[⇒\] Assign, \[⇐\] Assign
- {ref "rules-calls"}[*Calls*] — \[⇒\] Static-Call, \[⇒\] Static-Call-Multi,
  \[⇒\] Instance-Call, \[⇒\] Instance-Call-Multi
- {ref "rules-primitive-operations"}[*Primitive operations*] — \[⇒\] Op-Bool, \[⇒\] Op-Cmp, \[⇒\] Op-Eq,
  \[⇒\] Op-Arith, \[⇒\] Op-Concat; \[⇐\] Op-Arith, \[⇐\] Op-Bool
- {ref "rules-object-forms"}[*Object forms*] — \[⇒\] New-Ok, \[⇒\] New-Fallback; \[⇒\] AsType; \[⇒\] IsType;
  \[⇒\] RefEq; \[⇒\] PureFieldUpdate
- {ref "rules-verification-expressions"}[*Verification expressions*] — \[⇒\] Quantifier, \[⇒\] Assigned, \[⇐\] Old,
  \[⇒\] Old-Synth, \[⇒\] Fresh, \[⇐\] ProveBy, \[⇒\] ProveBy-Synth
- {ref "rules-self-reference"}[*Self reference*] — \[⇒\] This-Inside, \[⇒\] This-Outside
- {ref "rules-untyped-forms"}[*Untyped forms*] — \[⇒\] Abstract / All
- {ref "rules-contract-of"}[*ContractOf*] — \[⇒\] ContractOf-Bool, \[⇒\] ContractOf-Set, \[⇒\] ContractOf-Error
- {ref "rules-holes"}[*Holes*] — \[⇐\] Hole-Some, \[⇐\] Hole-None
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

$$`\frac{x \notin \mathrm{dom}(\Gamma)}{\Gamma \vdash \mathsf{Var}\;(\mathsf{.Declare}\;\langle x, T_x\rangle) \Leftarrow A \quad \dashv \quad \Gamma, x : T_x} \quad \text{([⇐] Var-Declare)}`

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
types X and Y”}]` and synthesize $`\mathsf{Unknown}`. Without an
`else`, the missing branch cannot produce a value, so the `if`
synthesizes $`\mathsf{TVoid}`.

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow T_t \quad \Gamma \vdash \mathit{elseBr} \Rightarrow T_e \quad T_t \sim T_e}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;(\mathsf{some}\;\mathit{elseBr}) \Rightarrow T_t} \quad \text{([⇒] If-Synth)}`

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{thenBr} \Rightarrow \_}{\Gamma \vdash \mathsf{IfThenElse}\;\mathit{cond}\;\mathit{thenBr}\;\mathsf{none} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] If-Synth-NoElse)}`

{docstring Strata.Laurel.Resolution.Synth.ifThenElse}

A non-empty block is typed by structural recursion on the statement
list: the last statement inherits the surrounding expected type, and
each non-last statement is checked at $`\mathsf{TVoid}`, *except*
calls — which are synthesized and have their result type dropped. The
same Discard-Call carve-out also fires for the *last* statement when
the block itself is in statement position (i.e. $`T = \mathsf{TVoid}`),
so $`\{\ldots;\,\mathit{foo}()\}` is accepted as a statement even when
`foo` returns a non-void type. The Discard-Call carve-outs are the only
block-level rules that aren't already consequences of the rules for
individual statements.

$$`\frac{\Gamma \vdash s \Leftarrow T}{\Gamma \vdash \mathsf{Block}\;[s]\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block-Singleton)}`

$$`\frac{\Gamma \vdash s \Leftarrow \mathsf{TVoid} \quad \dashv \quad \Gamma' \quad \Gamma' \vdash \mathsf{Block}\;\mathit{rest}\;\mathit{label} \Leftarrow T \quad \mathit{rest} \ne []}{\Gamma \vdash \mathsf{Block}\;(s :: \mathit{rest})\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Block-Cons)}`

$$`\frac{s = \mathsf{StaticCall}\;\ldots \lor s = \mathsf{InstanceCall}\;\ldots \quad \Gamma \vdash s \Rightarrow \_ \quad \Gamma \vdash \mathsf{Block}\;\mathit{rest}\;\mathit{label} \Leftarrow T \quad \mathit{rest} \ne []}{\Gamma \vdash \mathsf{Block}\;(s :: \mathit{rest})\;\mathit{label} \Leftarrow T} \quad \text{([⇐] Discard-Call-Cons)}`

$$`\frac{s = \mathsf{StaticCall}\;\ldots \lor s = \mathsf{InstanceCall}\;\ldots \quad \Gamma \vdash s \Rightarrow \_}{\Gamma \vdash \mathsf{Block}\;[s]\;\mathit{label} \Leftarrow \mathsf{TVoid}} \quad \text{([⇐] Discard-Call-Last)}`

\[⇐\] Block-Cons resolves $`s` under the incoming $`\Gamma` and
recurses on the tail under the possibly-extended scope $`\Gamma'`. In
practice only `Var (.Declare …)` actually extends the scope; every
other construct leaves it unchanged. The block opens a fresh nested
scope, so declarations made inside don't leak out — once the block
ends, the surrounding $`\Gamma` is restored. The block also emits a
`"dead code after '<terminator>'"` diagnostic when an `Exit` or
`Return` is followed by additional statements in the same block.

Statement forms (`Var-Declare`, `Assign`, `Assert`, `Assume`,
`While`, `Exit`, `Return`, `IfThenElse`) all check against
$`\mathsf{TVoid}`. They fit there for one of two reasons: most yield
no value (so the unit type $`\mathsf{TVoid}` is exactly right), and
the terminators `Exit`/`Return` accept *any* expected type (their
rules leave the value type free — see \[⇐\] Exit and the Return rules
below — because control leaves before any value is needed). Bare
expressions like `5;` fail via \[⇐\] Sub: the synthesized type is not
consistent with $`\mathsf{TVoid}`. The two Discard-Call rules are what
allow the standard `f(x);` idiom for a non-void-returning `f` —
without them, $`s \Leftarrow \mathsf{TVoid}` would force every call to
have a $`\mathsf{TVoid}`-compatible result type.

Pushing $`T` into the last statement (rather than synthesizing the
whole block and applying \[⇐\] Sub at the boundary) means a type
mismatch is reported at the offending subexpression's source
location, and the expectation continues to propagate through nested
`Block` / `IfThenElse` / `Hole` / `Quantifier` constructs that have
their own check rules.

$$`\frac{}{\Gamma \vdash \mathsf{Block}\;[]\;\mathit{label} \Rightarrow \mathsf{TVoid}} \quad \text{([⇒] Skip)}`

The empty block has a fixed type and is the only block-level rule that
synthesizes — written $`\mathsf{skip} : \mathsf{TVoid}` in the
source-language presentation. The recursive Block-Cons / Block-Singleton
rules above never bottom out into an empty tail, so the empty case is
reached only when the block is empty at the dispatch site. When an
empty block appears in check position with `expected ≠ TVoid`, the
standard \[⇐\] Sub rule fires at the boundary
(`Check.resolveStmtExpr`'s subsumption-fallback wildcard arm, requiring
$`\mathsf{TVoid} <: \mathit{expected}`).

{docstring Strata.Laurel.Resolution.Synth.emptyBlock}

A *non-empty* block also synthesizes when used in operand position
(e.g. $`\{\,x := 1;\; x\,\} == y`). It mirrors \[⇐\] Block-Cons /
\[⇐\] Block-Singleton — fresh scope, optional label, non-last
statements checked in effect position ($`\diamond`), dead-code
diagnostics — but *synthesizes* the last statement instead of checking
it, and returns that type as the block's value type.

$$`\frac{\Gamma \vdash s \;\diamond \;(\text{for each non-last } s) \quad \Gamma \vdash \mathit{last} \Rightarrow T}{\Gamma \vdash \mathsf{Block}\;(\mathit{init} \mathbin{+\!+} [\mathit{last}])\;\mathit{label} \Rightarrow T} \quad \text{([⇒] Block-Synth)}`

{docstring Strata.Laurel.Resolution.Synth.block}

{docstring Strata.Laurel.Resolution.Check.block}

The Discard-Call carve-outs and the "checks against $`\mathsf{TVoid}`"
behaviour for non-last (and discarded-last) statements are factored out
into {name Strata.Laurel.Resolution.Check.statement}`Check.statement`,
the single definition of what counts as a statement in effect position
($`\Gamma \vdash s\;\diamond`):

{docstring Strata.Laurel.Resolution.Check.statement}

$$`\frac{l \in \Gamma_{\mathrm{lbl}}}{\Gamma \vdash \mathsf{Exit}\;l \Leftarrow A} \quad \text{([⇐] Exit)}`

`exit` is an unconditional jump out of the enclosing labeled block.
Because control leaves before any value is needed, the rule accepts
*any* expected value type $`A` — it leaves $`A` free, with no
$`\mathsf{TVoid}` side condition — so an `exit` slots into any
position, even one expecting a value. Labels live in their own
namespace $`\Gamma_{\mathrm{lbl}}`, populated by the surrounding
`Block` rule when its $`\mathit{label}` is `some l`. An
$`\mathsf{Exit}\;l` targeting a label not in $`\Gamma_{\mathrm{lbl}}`
is rejected.

{docstring Strata.Laurel.Resolution.Check.exit}

In the Return rules below, $`\overline{T_o}` denotes the declared
output-parameter type list of the enclosing procedure (an implicit
parameter of the rules — the procedure binds it once on entry).

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Leftarrow A} \quad \text{([⇐] Return-None-Void)}`

$$`\frac{\overline{T_o} = [T] \quad \mathsf{TVoid} <:_\sim T}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Leftarrow A} \quad \text{([⇐] Return-None-Single)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;\mathsf{none} \Leftarrow A} \quad \text{([⇐] Return-None-Multi)}`

$$`\frac{\overline{T_o} = [T] \quad \Gamma \vdash e \Leftarrow T}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \Leftarrow A} \quad \text{([⇐] Return-Some)}`

$$`\frac{\overline{T_o} = []}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “void procedure cannot return a value”}} \quad \text{([⇐] Return-Void-Error)}`

$$`\frac{\overline{T_o} = [T_1; \ldots; T_n] \quad (n \ge 2)}{\Gamma \vdash \mathsf{Return}\;(\mathsf{some}\;e) \rightsquigarrow \text{error: “multi-output procedure cannot use 'return e'; assign to named outputs instead”}} \quad \text{([⇐] Return-Multi-Error)}`

`return` is the only rule whose premises depend on the enclosing
procedure's declared outputs. The conclusion's value type $`A` is left
free — the rule accepts any expected type — because `return` is a
control-flow terminator: it never falls through, so it can stand in
any position, even one expecting a value. The returned value (if any)
is checked against the procedure's declared output, not against $`A`.
The error arms fire when $`\overline{T_o}`'s arity does not match the
syntactic shape of `return e`.

Regardless of which arm fires, $`e` is always elaborated — it is
checked against the declared output in the single-output case,
otherwise synthesized — so any errors inside $`e` are reported in
addition to the arity diagnostic.

The three Return-None rules treat the missing payload as having type
$`\mathsf{TVoid}`. Void-output procedures accept it unconditionally
(Return-None-Void); single-output procedures require
$`\mathsf{TVoid} <:_\sim T` (Return-None-Single), accepting void
returns and rejecting `return;` in an `int`/`bool`/etc. procedure;
multi-output procedures accept it as an early-exit shorthand that
leaves the named outputs at whatever they were last assigned to
(Return-None-Multi).

When the surrounding context has no enclosing procedure body (e.g.
inside a constant initializer), `answerType = none` and all Return
checks are skipped; well-formed input never produces this case.

{docstring Strata.Laurel.Resolution.Check.return}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{invs}_i \Leftarrow \mathsf{TBool} \quad \Gamma \vdash \mathit{decreases} \Rightarrow U \quad \mathsf{Numeric}\;U \quad \Gamma \vdash \mathit{body} \Leftarrow \mathsf{Unknown}}{\Gamma \vdash \mathsf{While}\;\mathit{cond}\;\mathit{invs}\;\mathit{decreases}\;\mathit{body} \Leftarrow A} \quad \text{([⇐] While)}`

The body is checked at $`\mathsf{Unknown}`: control either re-enters
the loop or falls through, so the body's value type is never observed
by the surrounding context. A loop is a statement and yields no value,
so the rule accepts any expected type $`A` (it leaves $`A` free),
exactly like the other statement forms.

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

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assert}\;\mathit{cond} \Leftarrow A} \quad \text{([⇐] Assert)}`

{docstring Strata.Laurel.Resolution.Check.assert}

$$`\frac{\Gamma \vdash \mathit{cond} \Leftarrow \mathsf{TBool}}{\Gamma \vdash \mathsf{Assume}\;\mathit{cond} \Leftarrow A} \quad \text{([⇐] Assume)}`

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

$$`\frac{\Gamma(\mathit{callee}) = \text{static-procedure with inputs } Ts \text{ and outputs } [T_1; \ldots; T_n],\; n \ne 1 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise)}}{\Gamma \vdash \mathsf{StaticCall}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Static-Call-Multi)}`

{docstring Strata.Laurel.Resolution.Synth.staticCall}

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and output } [T'] \text{ (single output)} \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow T'} \quad \text{([⇒] Instance-Call)}`

$$`\frac{\Gamma \vdash \mathit{target} \Rightarrow \_ \quad \Gamma(\mathit{callee}) = \text{instance- or static-procedure with inputs } [\mathit{self}; Ts] \text{ and outputs } [T_1; \ldots; T_n],\; n \ne 1 \quad \Gamma \vdash \mathit{args}_i \Leftarrow Ts_i \text{ (pairwise; self dropped)}}{\Gamma \vdash \mathsf{InstanceCall}\;\mathit{target}\;\mathit{callee}\;\mathit{args} \Rightarrow \mathsf{MultiValuedExpr}\;[T_1; \ldots; T_n]} \quad \text{([⇒] Instance-Call-Multi)}`

The callee is resolved against either an instance procedure or a
static procedure (the latter handles uniformly-dispatched call syntax
where the receiver is forwarded as `self`). Output arity is forwarded
identically to
{name Strata.Laurel.Resolution.Synth.staticCall}`Synth.staticCall`'s
single-vs-multi split. In both call families the single- and multi-output
rules differ only in the *output* arity; argument checking is the same, and
surplus arguments (beyond the declared parameters, or when the callee is
unresolved) are checked against $`\mathsf{Unknown}` rather than flagged as an
arity error.

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

$$`\frac{\Gamma \vdash \mathit{args}_i \Rightarrow U_i \quad \mathsf{Numeric}\;U_i \quad T = \bigsqcup_i U_i \text{ (consistency LUB)} \quad \mathit{op} \in \{\mathsf{Neg}, \mathsf{Add}, \mathsf{Sub}, \mathsf{Mul}, \mathsf{Div}, \mathsf{Mod}, \mathsf{DivT}, \mathsf{ModT}\}}{\Gamma \vdash \mathsf{PrimitiveOp}\;\mathit{op}\;\mathit{args} \Rightarrow T} \quad \text{([⇒] Op-Arith)}`

The arithmetic synth rule mirrors $`[⇒]\,\text{Op-Eq}` but generalised
to $`n` operands. Each operand is synthesized and required to be
$`\mathsf{Numeric}` (i.e. $`\mathsf{TInt}`, $`\mathsf{TReal}`,
$`\mathsf{TFloat64}`, $`\mathsf{TBv}_w` (a bitvector of any width), or
the gradual $`\mathsf{Unknown}`). The
result type is the *consistency LUB* $`\bigsqcup_i U_i` — a fold of
the operand types under
{name Strata.Laurel.isConsistent}`isConsistent`'s flat lattice:
$`\mathsf{Unknown} \sqcup T = T`, $`T \sqcup T = T`, and any other
combination is rejected. So `1 + 2` synthesizes $`\mathsf{TInt}`,
`1.5 + 2.5` synthesizes $`\mathsf{TReal}`, `<?> + 1` synthesizes
$`\mathsf{TInt}` (the $`\mathsf{Unknown}` operand promotes to its
neighbour), `<?> + <?>` synthesizes $`\mathsf{Unknown}`, and
`1 + 2.0` is rejected with a "cannot apply '+' to operands of types
'int', 'real'" diagnostic. The fold runs via `join`, a
pure function, so the search has no diagnostic side-effects.

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

### Procedure
%%%
tag := "rules-procedure"
%%%

A procedure body is checked against an expected type $`A` and is
resolved under a scope that includes the procedure's input and output
parameters. The Return rules above refer to the same output list
$`\overline{T_o}` that the procedure binds here.

$$`\frac{\overline{T_o} = \mathit{proc}.\mathit{outputs}.\mathit{types} \quad A = \mathsf{procedureBodyType}(\mathit{proc}) \quad \Gamma_\mathit{global},\,\mathit{params}(\mathit{proc}) \vdash \mathit{proc}.\mathit{body} \Leftarrow A}{\Gamma_\mathit{global} \vdash \mathsf{Procedure}\;\mathit{proc}} \quad \text{(Procedure)}`

The body's value type $`A` is computed by `procedureBodyType`: a
single-output functional procedure expects $`A = T` (its body's last
statement is the result), while every other procedure expects
$`A = \mathsf{Unknown}` (its body is run as a statement and the last
statement's value is discarded; outputs are observed via `return e`,
matched against $`\overline{T_o}` by
{name Strata.Laurel.Resolution.Check.return}`Check.return`, or via
named-output assignment).

{docstring Strata.Laurel.resolveProcedure}

{docstring Strata.Laurel.resolveInstanceProcedure}

# Implementation

The static semantics of Laurel are defined by `Resolution.lean`. This is where Laurel references are resolved and where type checking is done. Calling `resolve` will produce diagnostics and a `SemanticModel` that can be used to navigate between definitions and references.
If new references or definitions are created during compilation, `resolve` must be called again to get a complete model.

## Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then invoking the Core
verification pipeline. The Laurel compilation pipeline consists of three parts:
- Lowering, consisting of many phases. Maps Laurel to Laurel
- Ordering, consisting of a single pass. Maps Laurel to OrderedLaurel
- Translation, consisting of a single pass. Maps OrderedLaurel to Core.

Ideally the translation pass only translates between types but does not change the structure of the program.

## Lowering Passes

The following passes are part of the lowering group:

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
