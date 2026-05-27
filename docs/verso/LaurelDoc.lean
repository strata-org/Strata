/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Laurel.Laurel
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

open Verso.Doc.Elab (DocElabM)

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
        s!"  - Comes before **{cb.name.name}** because: {cb.reason}"
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
      edges := edges ++ [(pass.name, cb.name.name, cb.reason)]

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
    let deps := pass.comesBefore.map (s!" → {·.name.name}")
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

Laurel's type system includes primitive types, collection types, and user-defined types.

## Primitive Types

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

# Translation Pipeline

Laurel programs are verified by translating them to Strata Core and then invoking the Core
verification pipeline. The Laurel compilation pipelines consists of three parts:
Lowering, consisting of many phases. Maps Laurel to Laurel
Ordering, consisting of a single pass. Maps Laurel to OrderedLaurel
Translation, consisting of a single pass. Maps OrderedLaurel to Core.

Ideally the translation pass only translates between types but does not change the structure of the program.

## Lowering Passes

The following passes are part of the lowering group:

{laurelPipelineDocs}

## Pass Dependency Graph

The following graph shows the ordering constraints between passes.

{laurelPipelineDependencyGraph}
