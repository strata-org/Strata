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


/-- Block command that includes the Laurel test README as subsections.
    Usage inside a `#doc` block: `{testingStrategyDocs}` -/
@[block_command]
def testingStrategyDocs : Verso.Doc.Elab.BlockCommandOf Unit := fun () => do
  let md := include_str "../../StrataTest/Languages/Laurel/README.md"
  let some ast := MD4Lean.parse md
    | Lean.throwError "Failed to parse testingStrategyDocs as Markdown"
  let blocks ← ast.blocks.mapM (Markdown.blockFromMarkdown · (handleHeaders := Markdown.strongEmphHeaders))
  `(Verso.Doc.Block.concat #[$blocks,*])


#doc (Manual) "The Laurel Implementor Guide" =>
%%%
shortTitle := "Laurel Implementor Guide"
%%%

# Language definition
The Laurel language definition consists of its types, its grammar and its semantics. Currently the
semantics is split into a static part, called the resolver, and a yet to be built dynamic part.

The parts of the language definition map onto the implementation files as follows:

- *Type* — `LaurelAST.lean` defines the Laurel AST, including the program structure (`StmtExpr`,
  declarations, procedures) and the type language (`HighType`). `LaurelTypes.lean` computes the
  `HighType` of an expression from these annotations, and `TypeHierarchy.lean` captures the
  subtyping relation between user-defined types.
- *Grammar* — `Grammar/LaurelGrammar.st` is the DDM dialect that defines Laurel's concrete syntax;
  it is loaded into Lean by `Grammar/LaurelGrammar.lean`.
  `Grammar/ConcreteToAbstractTreeTranslator.lean` turns the parsed concrete tree into the
  `LaurelAST` type, and `Grammar/AbstractToConcreteTreeTranslator.lean` goes the other way to render
  an AST back to concrete syntax.
- *Static semantics (resolver)* — `Resolution.lean` resolves references and type checks the
  program, producing diagnostics and a `SemanticModel` (defined in `SemanticModel.lean`) that links
  references to their definitions.
- *Dynamic semantics* — Laurel does not yet have a standalone interpreter; its runtime meaning is
  given operationally by the compilation to Core described below. The pass files under
  `Strata/Languages/Laurel/` and the pipeline in `LaurelCompilationPipeline.lean` therefore
  constitute the dynamic semantics, delegating to Core's own execution and verification semantics.

*Laurel program type definition*
The Laurel type definition allows many more programs than are required for the language as it is
documented for the user. The reason for this is the compilation of Laurel to different languages.
However, despite being wide, the Laurel language type is kept as precise as possible given the
flexibility that it needs.

In the Laurel type, constructors are combined when this does not reduce precision. For example,
instead of having a separate constructor for `StmtExpr.Forall` and for `StmtExpr.Exists`, there is a
single `StmtExpr.Quantifier` with a boolean field to determine its type. A more complicated example:
calls to statically defined user procedures, to datatype constructors, and to datatype destructors
all go through the same `StmtExpr.StaticCall` constructor; resolution distinguishes them by the
resolved kind of the callee rather than by AST constructor. A further consolidation is in progress
(WIP): calls to primitive operators and to user-defined instance procedures are planned to go
through this same call constructor as well.

All information in the Laurel AST is strongly typed. There are no fields that can hold unstructured
data, which could be used by extensions to Strata. Instead, Strata extensions should attach data to
AST nodes by referencing them through source locations.

*Resolution*
The static semantics of Laurel are defined by `Resolution.lean`. This is where Laurel references are
resolved and where type checking is done. Calling `resolve` will produce diagnostics and a
`SemanticModel` that can be used to navigate between definitions and references.

Identifiers that occur in a Laurel program carry an optional `uniqueId: int`. During resolution,
every identifier that defines a new symbol is given a unique identifier, and every identifier that
refers to a definition is given the unique identifier of the definition it references. The
`SemanticModel` uses these unique identifiers to provide navigation features.

Right now, Laurel reserves identifier names that start with `$` for use in its compilation passes.
In the future we may improve the passes so they never generate names that collide with user provided
names.

# Testing strategy

{testingStrategyDocs}

# Proofs

Right now the only proofs in the Laurel implementation are termination proofs. We do not yet require
any Laurel code to have more proofs than that. We are planning to define a semantics for Laurel in
terms of Lean, and we will prove that the Laurel compilation passes preserve those
semantics.

# Compilation to Core
To enable its verification analyses, Laurel compiles to Core. Compilation happens over many passes.
A compilation pass may not change the semantics of the program. User errors may only be reported
during resolution (`resolve`, which the pipeline re-runs after passes that set `needsResolves`),
never by a pass — there are no exceptions to this rule. Every diagnostic emitted by a pass is a bug
report (`DiagnosticType.StrataBug`), where a "bug" includes features that are planned but not yet
supported: for example, `InlineLocalVariables` reporting an assignment to a variable it has inlined.
A compilation pass may only refer to AST nodes that relates to its business
logic: it may not define AST traversals without using helper methods, to allow adding new AST nodes
without breaking existing compilation passes. The generic traversal helpers live in
`MapStmtExpr.lean`: `mapStmtExprM` (bottom-up monadic rewrite of a `StmtExpr` tree),
`mapStmtExprPrePostM` (pre- and post-order rewrite), `foldStmtExprM`/`foldStmtExpr` (accumulate over
every node), and `collectStmtExprList` (gather a list from every node). The same file lifts these to
the surrounding structure with `mapProcedureBodiesM`, `mapProgramM`, and the `*HighTypes*` variants
(e.g. `mapStmtExprHighTypesM`, `mapProgramHighTypesM`) that rewrite the `HighType` annotations. A
pass pattern-matches the handful of constructors it cares about in the function it passes to one of
these and falls through for the rest, so it never spells out the full `StmtExpr` case split.

If new references or definitions are created during compilation, the program must be re-resolved to
get a complete model. A pass does not call `Resolution.resolve` itself; instead it sets
`needsResolves := true` in its definition, and the pipeline driver
(`LaurelCompilationPipeline.lean`) runs `resolve` after the pass and threads the refreshed
`SemanticModel` into the next pass. The passes `HeapParameterization`, `TypeHierarchy`, and
`ModifiesClauses` (in pipeline order) are logically one step: the first two set
`needsResolves := false` to suppress the intermediate re-resolutions, and the last member
(`ModifiesClauses`) sets `needsResolves := true`, so the group is re-resolved once at its end.

*Eliminated constructs stay eliminated*
Several passes exist to eliminate a construct: after `EliminateReturnStatements` no `Return`
occurs, after `EliminateIncrDecrAndCompoundAssign` no `IncrDecr` or `CompoundAssign`, and after the
hole passes (`InferHoleTypes` types every hole, `EliminateDeterministicHoles` replaces deterministic
holes with fresh opaque `$hole_N` procedures, `LiftImperativeExpressions` havocs the
non-deterministic ones) no `.Hole`. Later passes rely on these facts, so a pass must not reintroduce
a construct past its elimination point. Breaking this rarely fails at the offending pass; it
surfaces where the reliance is, which can be as late as the Core translation — a leaked hole is
reported there as `holes should have been eliminated before translation`, far from the pass that
leaked it. The same distance applies to the other eliminated constructs.

## Translation Pipeline

The Laurel to Core translation pipeline uses these IRs:
- Laurel
- UnorderedCoreWithLaurelTypes
- CoreWithLaurelTypes
- Core

Most of the passes are in the Laurel IR.
The transparency pass goes from `Laurel` to `UnorderedCoreWithLaurelTypes`.
The ordering pass goes from `UnorderedCoreWithLaurelTypes` to `CoreWithLaurelTypes`.
And the LaurelToCoreSchemaPass goes from `CoreWithLaurelTypes` to `Core`.

## Passes

The following passes make up the compilation of Laurel to Core:

{laurelPipelineDocs}

## Pass Dependency Graph

The following graph shows the ordering constraints between passes.

{laurelPipelineDependencyGraph}
