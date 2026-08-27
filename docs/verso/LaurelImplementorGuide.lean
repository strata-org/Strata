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
semantics is split into a static part, called the resolver, and a yet-to-be-built operational part.

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
- *Operational semantics* — Laurel does not yet have a standalone interpreter; its runtime meaning is
  given operationally by the compilation to Core described below. The pass files under
  `Strata/Languages/Laurel/` and the pipeline in `LaurelCompilationPipeline.lean` therefore
  constitute the operational semantics, delegating to Core's own execution and verification semantics.

*Laurel program type definition*
The Laurel type definition allows many more programs than are required for the language as it is
documented for the user. The Laurel AST has some constructs that are only used by the compilation
passes, but not by the source languages, to enable gradual compilation to Core. Because of these
extra constructs we call the Laurel AST wide.

If two Laurel language constructs share semantic properties, we try to capture that sharing in the
AST by having a shared constructor. For example,
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
In the future we may improve the passes so they never generate names that collide with user-provided
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
report (`MessageKind.strataBug`), where a "bug" includes features that are planned but not yet
supported: for example, `InlineLocalVariables` reporting an assignment to a variable it has inlined.
A compilation pass may only refer to AST nodes that relate to its business
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
`SemanticModel` into the next pass. The passes `YieldElim`,
`HeapParameterization`, `TypeHierarchy`, and `ModifiesClauses` (in pipeline order) are
logically one step: all but the last set `needsResolves := false` to suppress the intermediate
re-resolutions, and the last member (`ModifiesClauses`) sets `needsResolves := true`, so the group
is re-resolved once at its end. The coroutine lowering relies on this: `YieldElim` emits transient
`Snapshot`/labeled-`Old` artifacts (and a `havocHeap()` call) that have no resolution support
and must reach `HeapParameterization` — which lowers them — without an intervening re-resolve.

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

# Concurrency

Coroutines are lowered along one of two paths, selected by the
`LaurelTranslateOptions.verifyCoroutine` flag. The default path elaborates each
coroutine into an executable state machine; the opt-in verification path generates
verification conditions directly from the coroutine body under rely/guarantee. The two
paths live in `CoroutineElaboration.lean` and `YieldElim.lean` respectively.
`CoroutineElaboration` runs before `LiftInstanceProcedures` (it emits instance calls that
pass must lift); the coroutine-lowering pass `YieldElim` runs later,
just before `HeapParameterization`.

## Verification path: `YieldElim`

`YieldElim` (enabled by `verifyCoroutine := true`) verifies each coroutine as a
straight-line procedure, so the verifier never reasons about a dispatch loop. It
rewrites every `yield` in the body into an inline block

```
assert ⋀guarantees;
snapshot $old_heap;   // = $heap, pre-havoc (for the rely's old)
havocHeap();          // the environment acts (a havoc)
assume ⋀relies;
snapshot $old_heap    // = $heap, post-havoc (start of the next step)
```

and clears the coroutine's `relies`/`guarantees` clauses, turning it into a regular
procedure. The `assert` discharges the coroutine's own step guarantee; the
`havocHeap()` call (a bodiless `opaque modifies *` preamble procedure) models the
environment acting while suspended; the `assume` grants the rely about that
environment step. `havocHeap`'s monotonic-counter postcondition records that the
environment step allocates but never deallocates, so a post-yield allocation cannot
alias a pre-yield reference.

Both clause families are two-state, and each relates a prior heap to the current
`$heap`. A single reassigned snapshot `$old_heap` serves both sides, since a coroutine
step is linear:

- A guarantee's `old(...)` — spelled `oldGuarantee(...)` in body asserts and loop
  invariants — reads `$old_heap` while it holds the *start of the current step*
  (procedure entry, or the post-havoc heap after the previous yield).
- A rely's `old(...)` — spelled `oldRelies(...)` — reads `$old_heap` after the
  pre-havoc reassignment, so an assumed rely is `R($old_heap, $heap)` = "what the
  environment did across this step".

Both are emitted as a labeled `Old (some $old_heap)`, which heap parameterization
evaluates against `$old_heap`; heap-param also declares the `$old_heap` local (seeded to
the entry heap) and lowers each `Snapshot` to `$old_heap := $heap`. The per-yield asserts
cover each `resume → yield` step; a separate pass step (`addExitGuarantees`) asserts
the guarantee on every path out of the body (before each `return` and at the body end),
covering the final `resume → halt` segment that the caller also observes.

`YieldElim` runs *before* `HeapParameterization`: it never touches `$heap` directly,
emitting `Snapshot`/labeled-`Old`/`havocHeap()` for heap-param to lower. Resolution
is disabled across that gap, so those transient artifacts reach heap-param untouched.
`YieldElim` also handles the caller-side dual (the `coroutineRelyHeap` step): it threads a
per-instance `$h1_co` snapshot through resume callers and adds the `$h_rely_old`
parameter to the generated `resume` procedures. Unlike the body rewrite, this caller-side
step runs regardless of `verifyCoroutine`, since the default elaboration path also emits
the `oldRelies`/`oldGuarantees` markers it lowers.

## Execution path: state-machine linearization

The default path (`CoroutineElaboration.lean`) compiles a coroutine body into a
state-machine lookup table indexed by a `$pc` field on a generated `<c>State`
composite, with `resume` and `has_next` instance procedures. Linearization assigns each
straight-line fragment of the body a `$pc` label and rewrites control flow into
transitions between labels: a `yield` stamps the resume target and returns to the
scheduler (a suspend), while ordinary sequencing falls through to the next label (a
transition). `resume` dispatches on `$pc`; `has_next` is `$pc != END`. This form is
convenient for concrete execution but reasons through the heap and `$pc` at every step,
which is why the verification path bypasses it.

## Contract representation

The four coroutine clause families (`relies`, `guarantees`, `yields`, `resumes`) live
on `Procedure.contracts : CoroutineContracts`, a sum type whose `Coroutine` case
carries all four lists and whose `Regular` case carries none. `Procedure.kind` is
recovered from which case is present, so a regular procedure cannot hold a stray
`relies` clause. Both lowering paths consume these clauses and reset `contracts` to
`Regular`, so downstream passes treat the result as an ordinary procedure.

## Exception lowering

`EliminateExceptions` is the largest single rewrite in the pipeline, so it is worth spelling out
beyond its entry in the pass list above. It is a Laurel-to-Laurel pass: it rewrites every exceptional
construct into ordinary Laurel, so that the Laurel-to-Core translator never has to know exceptions
exist.

*The `Result` encoding.* A Core procedure has one exit; a throwing Laurel procedure has two, so its
result becomes a sum type — `Good(value)` for a normal return and `Bad(err)` for an exit by throwing,
with the error component at the procedure's declared `throws` type so both outcomes stay precisely
typed. A caller inspects `Result..isGood` / `Result..isBad` and either unwraps the value or
re-propagates the exception. `Result` is not part of the always-on prelude: the pass injects it, and
only into programs that actually use exceptions (a `throws` procedure, a `throw`, or a call to a
throwing procedure), so a program that never throws does not carry it. It is an ordinary datatype,
free for SMT, so it does not perturb heap reasoning.

*The in-flight exception rides in synthesized locals.*

- `$thrown : bool` — an exception is in flight.
- `$exc_<i>` — one per `try`, typed at that `try`'s least common ancestor exception type. A
  `finally`-only `try` reuses the enclosing region's local.
- `$exc` — procedure-level, at the declared `throws` type, for exceptions that leave the body.
- `$returning : bool` — a `return` unwinding out of enclosing `try` blocks, so their `finally` arms
  still run.
- `$exiting_<label> : bool` — one per label, for an `exit` whose target lies outside a `try` it has
  to unwind through; cleared once the jump is delivered to its label.

Propagating outward into a region whose exception local is narrower inserts an assumed checked
downcast, which is sound because the escape analysis has already proved that only subtypes of that
type can travel the edge.

*The shapes it produces.* A `throw v` assigns its region's exception local, sets `$thrown`, and exits
to the nearest enclosing `try` or to the body-exit block. A `try` becomes two nested labeled blocks
plus the `finally` arm and a re-dispatch: the inner block is where the body's `throw` exits to, the
guarded catch chain runs after it first-match-wins, and the re-dispatch is what continues an unwinding
`throw`, `return`, or `exit` outward. Each pending completion is snapshotted and cleared around the
`finally` arm, so an arm that itself completes abruptly supersedes it — Java's JLS 14.20.2 rule. A
call to a throwing procedure binds its `Result` to a temporary and then propagates on `Bad` or unwraps
the value on `Good`. The body is wrapped in a body-exit block, after which the result is assembled:
`Bad` of the in-flight exception if one is in flight, `Good` of the value otherwise.

*Contracts become guarded postconditions* over the assembled result. A good-path `ensures P` becomes
`Result..isGood($result) ==> P`. The declared `throws T` becomes
`Result..isBad($result) ==> Result..err($result) is T`, derived from the type rather than from any
authored clause, since it holds on every throwing path. Each `throwsOn C { … }` case becomes its
forcing claim `C ==> Result..isBad($result)` plus, for every `ensures P` it contains,
`C & Result..isBad($result) ==> P`, with the name bound by `throws (e: T)` substituted by
`Result..err($result)`.

Splitting a case this way rather than emitting one `C ==> (isBad & P)` matters twice over. A cast in
`P` lowers to an embedded `assert (e is T)` (see `HeapParameterization`), which is discharged from the
enclosing antecedents — so the idiomatic `ensures e is T ==> (e as T)#f …` only verifies with `isBad`
and `C` on the left. And a body that never throws on a guarded path then fails as exactly one
condition: the forcing claim fails while every postcondition is vacuous.

*What is synthesized and what is preserved.* The forcing claim and the declared-type postcondition are
synthesized by this pass, so their mode is computed here — assumed for a bodiless procedure, both
checked and assumed otherwise. A case's `ensures` is *authored*, so its mode is carried through
instead, exactly as the normal-path arm carries a top-level `ensures`. That distinction is not
theoretical: `ThrowsOnBlock.postconditions` is public AST and frontends construct Laurel programs
directly rather than parsing them, so a pass that computed the mode here would silently turn a
frontend's assume-only case postcondition into a checked obligation — verifying, but against a
contract nobody wrote. The forcing claim stays computed even if `free` reaches the surface, because a
free forcing claim would assert nothing about the body, which is the one thing a case exists to do. A
case's `summary` is likewise carried through, which is why that part of the surface already works.

*The heap frames are the exception to that.* They quantify over `$heap` and the field constants,
which do not exist until heap parameterization has run, so this pass cannot build them. It clears each
case's postconditions but leaves `throwsOn` itself on the procedure, and `ModifiesClauses` later builds
the `Result..isGood`-guarded normal frame, one `Result..isBad & Cᵢ`-guarded frame per case, and the
exhaustiveness claim `Result..isBad($result) ==> (C₁ ∨ … ∨ Cₙ)` over the guards. That claim is checked
for a procedure with a body and assumed for a bodiless one, like every other clause there.

*A procedure with no case gets no exhaustiveness claim.* The empty disjunction is `false`, so emitting
it unconditionally would read as "never throws" and reject every procedure that declares `throws` and
states nothing else — which is most of them. `ModifiesClauses` therefore suppresses the claim when
`throwsOn` is empty, which is what makes stating cases opt-in: a procedure says nothing about its
throwing paths until it states one, and once it states any, it has to account for all of them. The
declared-type postcondition is unaffected, so such a procedure still tells callers *what* it threw,
just not when.

*One gap in the guards.* A guard is documented as a pre-state predicate, but the conditions it is
lowered into are postconditions and its heap reads are not wrapped in `old(...)`, so a guard such as
`c#value < 0` is evaluated against the post-state heap. Guards over parameters are unaffected, since
those are immutable. Heap-reading guards are therefore unsupported rather than merely untested.

*Why the pass runs before `HeapParameterization`.* Heap parameterization, and the type-hierarchy
transform after it, erase every composite reference to the synthesized `Composite` type. A pass
running later would therefore have nothing but `Composite` to type the in-flight exception at, and
every handler's field access would need a downcast. Running first, the pass can read each `catch`
binding's resolved least-common-ancestor type and use it directly.

*One rule the analysis and the lowering have to share.* Catch-or-declare is checked during resolution
(`validateExceptionEscapes`), not by a pass, following the rule above that user errors are reported
only by `resolve`. It has to agree with the lowering on one point: a `finally` arm that definitely
completes abruptly discards whatever completion was pending. So the escape analysis treats a body or
handler `throw` as *not* escaping through such an arm — otherwise it would reject
`try { throw e } finally { return }`, a program whose lowering swallows the exception. The analysis
stays an under-approximation: only completions it can prove abrupt count.

*Two shapes are rejected instead of lowered.* `validateExceptionLowerability` rejects them at
resolution with a not-yet-supported diagnostic, because the alternatives would be an internal error or
a silent miscompile: a call to a `throws` procedure in a nested expression position (only a whole
statement or a whole assignment right-hand side is handled), and a `catch` handler that re-declares
its own exception binding (the binding substitution matches by name and is not scope-aware).

*Reading the actual output.* The pass's real output is pinned as golden cases in
`StrataTest/Languages/Laurel/Idiomaticity/EliminateExceptionsTest.lean` — a bodiless throwing
procedure with a contract, a `try` / `catch` around a throwing call, a void-returning throwing
procedure, and the `finally` unwinding cases among them. That file is the place to look for the
concrete shapes rather than a transcription here, which would go stale the first time the pass
changes.

*What reaches the backends.* Nothing exception-specific: datatypes, labeled blocks and exits, and
ordinary postconditions. Backends that want to reason about exceptional control flow can still
exploit what survives — `Good` versus `Bad` marks the two ways a procedure can finish, `$thrown`
together with the exception locals identifies an in-flight exception, and catch blocks stay
identifiable. By the time the program reaches Core those locals are typed `Composite` like every
other composite reference, including inside the result type's arguments, so a backend recovers the
specific exception type from its type tag rather than from the static type. These are directions for
exception-aware backends rather than something the current backends rely on.
