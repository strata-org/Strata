/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

#doc (Manual) "IR Translation Design Philosophy" =>
%%%
shortTitle := "IR Translation Design Philosophy"
%%%

This document describes the design philosophy Strata follows for
translations between intermediate representations (IRs), and how
that philosophy concretely shapes the module layout. It is
intended for contributors adding a new front-end, a new backend,
or a new IR to Strata, and for reviewers asking "does this
translation live in the right place?"

# TL;DR

> Translations live with the side that has many counterparts and
> depend on the central side that everyone shares. Core is the
> narrow waist of an hourglass that everything depends on; Core
> depends on no front-end, no analysis, and no external tool.

Concretely:

- Front-ends own `toCore` (Python, Java, Boole, Boogie, ...).
- Analyses own `fromCore` (the deductive verifier, the Core →
  GOTO translator, ...).
- A translation that does not belong cleanly to either side may
  live as a standalone translation module that depends on both.
- *Core depends on none of these*, so adding any one of them
  does not perturb the others.

This document is a companion to the package decomposition
proposal in
[issue #1168](https://github.com/strata-org/Strata/issues/1168).
*Versioning policy, breaking-change semantics, and SLAs are
explicitly out of scope* here and will be covered in a separate
document.

# Terminology

A few terms recur with specific meanings:

- *Source artifact* — the user-supplied input that a translation
  starts from: a `.py` file, a Java `.class`, an assembly listing,
  even a binary. The source artifact is _not_ in any Strata IR
  yet.
- *Front-end* — the Strata-side component that ingests source
  artifacts and produces a Strata IR (typically a high-level
  dialect). Examples: `StrataPython`, `StrataBoole`.
- *Central IR* — an IR many producers and many consumers share.
  In Strata, *Core* is the central IR.
- *Analysis* — anything that consumes a Strata IR and produces a
  result _about_ the program. Two flavors:
  - *In-process analysis* (no external tool): for example a
    Core-level type checker, the Core interpreter / partial
    evaluator, an abstract-interpretation pass, the Core → GOTO
    translator, the deductive VC generator.
  - *External-tool analysis*: an in-process Strata component
    that prepares input for and consumes output from an external
    program. Examples: the SMT analysis (encodes Core to SMT-LIB
    and calls cvc5/z3), the CBMC analysis (translates Core to
    GOTO and calls CBMC).
- *External tool* — the separate program: cvc5, CBMC. It lives
  outside the Strata process and is not Strata code.
- *Transform* — a translation whose output is the same kind of
  thing as its input (e.g., Core → Core). The distinction between
  a transform and an analysis is fuzzy: as a rule of thumb, a
  _transform_ gives you a transformed version of the input, while
  an _analysis_ gives you a _fact_ about the input. An analysis
  may be implemented as a transform plus a projection.

The word *backend* is deliberately avoided in this document
because it conflates analyses with external tools. Where the
distinction matters, the more specific term is used.

# The structural pattern: an hourglass

Strata's structural pattern is an *hourglass*: many front-ends
fan in to a single narrow waist (Core), and many analyses fan
back out of it.

```
      Python    Java    Boole       SMT       ...
         \       |        |          /         /
          \      |        |         /         /
           \     |        |        /         /
            ▼    ▼        ▼       ▼         ▼
            ┌───────────────────────────────┐
            │      Core IR (the waist)      │
            └───────────────────────────────┘
            ▼    ▼        ▼          ▼
           /     |        |           \
          /      |        |            \
         /       |        |             \
   deductive   model     abstract      .....
   verifier    checker   interpreter
```

Many sources translate *into* Core; many consumers translate
*out of* Core (Laurel omitted for clarity). Without the waist,
an N×M coupling between sources and consumers would explode; with
the waist, the graph collapses to N + M paths.

The smallest non-trivial instance is N = M = 2. For example,
Python and Java both verified by both the deductive verifier and
CBMC:

```
      Python                 Java
          \                   /
           \                 /
            ▼               ▼
            ┌───────────────┐
            │     Core      │   (the waist)
            └───────────────┘
            ▼               ▼
           /                 \
          /                   \
   deductive verifier       CBMC
```

Four end-to-end paths exist (Python→verifier, Python→CBMC,
Java→verifier, Java→CBMC) but only four spokes attach to Core
(Python→Core, Java→Core, Core→verifier, Core→CBMC). Without the
waist, those four paths would require four direct translations,
and adding a fifth front-end or fifth analysis would multiply the
new direct edges. The waist is what stops the explosion.

For the hourglass pattern to deliver, *Core must remain
genuinely central* — it must remain the _waist_, narrow and
shared. Two structural properties follow:

- *Core depends on nothing on either side.* Every dependency
  Core picks up — on a specific front-end, analysis, or external
  tool — widens the waist and couples a future contributor to
  that dependency, whether they want it or not.
- *Core should be as small as possible.* Every front-end and
  every analysis must understand Core in full; the fewer concepts
  the waist defines, the easier it is to learn and the cheaper it
  is to maintain compatibility across all spokes. A wide waist
  defeats the hourglass.

# The three ways to write a translation

A translation `IR1 → IR2` can be expressed in three equivalent
ways that differ only in _where the function lives_ and therefore
_who imports whom_:

```
-- Form A: defined in IR1's module
module IR1
  def toIR2 (x : IR1.AST) : IR2.AST := ...

-- Form B: defined in IR2's module
module IR2
  def fromIR1 (x : IR1.AST) : IR2.AST := ...

-- Form C: standalone module
module IR1ToIR2
  def translate (x : IR1.AST) : IR2.AST := ...
```

The functions are extensionally the same; the difference is in
the import graph:

: Form A

  Lives in the `IR1` module. Imports: `IR1 → IR2` (IR1 depends
  on IR2).

: Form B

  Lives in the `IR2` module. Imports: `IR2 → IR1` (IR2 depends
  on IR1).

: Form C

  Lives in a third module. Imports: `IR1ToIR2 → IR1` and
  `IR1ToIR2 → IR2` (the module depends on both; neither IR
  depends on the translation).

That single arrow direction is what determines who can extend
what and what the dependency graph looks like.

# How to choose: the one-to-many test

Apply this in order:

1. *Is one side the central IR (Core) and the other not?* Then
   the translation lives on the *non-Core* side, which imports
   Core. Core never imports a non-Core target.
2. *Is one side a single component and the other side a
   _family_ of components that all need to translate to/from
   it?* That is, is the relationship *one-to-many*? The
   translation lives on the *many* side. Each of the many
   imports the one; the one imports none of the many.
3. *Is the translation neither side's natural concern, or large
   enough to warrant its own home?* Place it in a *standalone
   translation module* that depends on both endpoints. Neither
   endpoint imports the standalone module.

A practical heuristic for new IRs: when one IR already exists in
Strata and the other is being introduced, the already-existing
one is the central side; the new one owns the translation in
both directions.

The principle generalizes beyond Core. If multiple analyses come
from a higher-level dialect (`Laurel`, say), then `fromLaurel`
belongs in each analysis package, not in Laurel. The same
many-to-one-to-many test applies recursively.

# Implications

## 1. Dependency direction is extensibility direction

If `toIR2` lives in IR1, *adding a new target IR3 means
modifying IR1*. IR1 grows every time someone adds a consumer.

If `fromIR1` lives in IR2, *adding a new target IR3 means
writing IR3 alone*. IR1 is untouched.

The side that needs to *stay extensible-around without being
touched* is the central side. Strata multiplies front-ends,
analyses, and external-tool adapters over time; Core is the
narrow waist all of them attach to. Therefore translations that
consume Core live on the consumer side, and translations that
produce Core live on the producer side. Core depends on none of
them.

This is _not_ a claim about how often each side changes. Core
itself evolves. The claim is that *new producers and new
consumers must be addable without widening the waist, or widen
generically*.

## 2. Open / closed

`toIR2` defined in IR1 is *closed* to extension — every new
target requires editing IR1. `fromIR1` defined in IR2 (or in a
standalone module) is *open* — new targets are additive.

The IR you most want closed-for-modification but
open-for-extension _around_ is the central IR. So translations
_out of_ Core live with the consumer; translations _into_ Core
live with the producer.

## 3. Knowledge ownership

Translations should live with the component that owns the
_details_ of the side that varies:

- A front-end author owns the source language's details and the
  faithful mapping into Core. `Laurel.toCore` lives with Laurel.
- An analysis author owns the analysis's input requirements (CFG
  shape, post-PE residual form, etc.) and any external-tool
  specifics. The translation lives with the analysis.

This is _not_ a claim that Core authors don't understand SMT or
GOTO. They do. The claim is that *detail about a non-Core side
belongs to the non-Core component*, so adding new analyses does
not force the Core team to learn N tool dialects or force the
Core codebase to adopt the complexity and size of N tools.

If `Core.toCBMC` lived in Core, Core would carry CBMC details
that every other consumer must build through, even when those
consumers have nothing to do with CBMC.

## 4. Cyclic-dependency risk

If both `Laurel.toCore` and `Core.fromLaurel` exist, one of them
is redundant — and at some point someone will write a helper that
calls both, producing an import cycle. Pick exactly one location
per arrow.

The standalone-module form (Form C above) sidesteps this: the
module depends on both endpoints, but neither endpoint depends on
the module, so cycles cannot form.

## 5. Testing locality

Tests for a translation belong with the translation. With
front-ends owning `toCore`, Python's translation tests live with
Python and run when Python changes. Core's test suite stays
small. Inverting the layout would pollute Core's tests with every
front-end's test load.

End-to-end tests that span the entire pipeline (e.g., Python all
the way through SMT) live in a top-level test module that imports
all the participating components. This module is allowed to
depend on everything; it is the _only_ place that may.

A consequence: a CR that touches a front-end will trigger
building the end-to-end test module. That is intentional: the
end-to-end module is the place where cross-component regressions
are detected.

## 6. Composability through multiple IRs

The rule applies recursively. Strata today uses
`Python → Laurel → Core`:

- `Python.toLaurel` lives with Python (Python depends on Laurel).
- `Laurel.toCore` lives with Laurel (Laurel depends on Core).
- Laurel does not depend on Python; Core does not depend on
  Laurel.

This does not imply a _total_ order on dialects. A dialect like
SMT or B3 may legitimately appear at multiple positions in
different pipelines (front-end-like in some contexts,
analysis-like in others; see "An IR can be both producer and
consumer" below). The DAG just needs to remain a DAG — there is
no required spine.

Whenever two or more front-ends share two or more analyses
through Core, the hourglass collapses an N×M tangle of would-be
direct translations into N + M spokes.

## 7. Centrality lets Core evolve independently

Keeping translations _out of_ Core means Core's source files
change only when Core's _language_ changes — not when a
front-end gains a feature, an analysis is added, or an external
tool changes its dialect. "Did we touch the central IR?" becomes
trivially answerable from `git log` over Core's directory.
Whether such a change counts as a _breaking_ change is governed
by the separate versioning policy referenced at the top of this
document.

(Multi-boundary changes — e.g., adding a Core feature that
requires DDM changes — are coordinated in the same way any
cross-package change is: land the dependency-direction change
first, then the dependent change. This document does not specify
the cross-team coordination workflow.)

## 8. Lowering vs. raising

Two complementary directions exist for any pipeline:

- *Lowering* — source-shaped → analysis-shaped (Python →
  Laurel → Core, Core → GOTO, Core → SMT).
- *Raising* — analysis-shaped → source-shaped (a solver
  counterexample model rendered as `foo.py:42`).

Both directions usually live with the source-facing endpoint of
each step, so that Core stays free of source-language detail in
both directions. Crucially, *raising is not a single hop*: an
end-to-end raising path mirrors the lowering chain. Mapping an
SMT model back to a Python source location requires SMT → Core
raising, then Core → Laurel raising, then Laurel → Python
raising. Each step lives where the corresponding lowering step
lives.

This means counterexample raising is needed at _every_ level for
the deepest level to be useful — not just at the front-end.

## 9. An IR can be both producer and consumer

Some IRs naturally play both roles. The SMT dialect is the
prototypical case:

- As an analysis target: Strata produces SMT-LIB from Core
  (`Core → SMT-LIB`), so the SMT side imports Core and owns the
  encoder.
- As a (future) front-end: Strata may parse `.smt` files into
  Core, e.g. for parallel processing. In that role the SMT side
  again imports Core and owns `SMT.toCore`.

Both roles satisfy the rule: the SMT side imports Core in both
directions; Core imports neither. There is no contradiction. B3
is another dialect that may legitimately appear at multiple
pipeline positions.

## 10. Standalone translation modules

Sometimes a translation does not belong cleanly to either side —
neither the source nor the target wants to own it, the
translation has its own substantial machinery (passes, options,
diagnostics) that would clutter both endpoints, or the same
translation is shared by multiple consumers.

In that case the translation lives as a *standalone module*
that depends on both the source and the target:

```
  Source IR ◀── translation module ──▶ Target IR
                  (depends on both,
                   nothing depends on it)
```

The central IR still depends on nothing. The translation module
sits _outside_ both IRs, depending inward on each. New consumers
of either IR are not affected.

Pick standalone-module placement when:

- the translation is large enough to warrant its own home;
- placing it on either side would force that side to import the
  other for no other reason;
- the translation has its own lifecycle (passes, configuration)
  that should not be versioned with either endpoint;
- the translation logically belongs to _neither_ endpoint.

The remaining constraint: *the central IR still imports neither
endpoint*, and the translation module imports the IRs, not the
other way around.

## 11. Core-to-Core translations

Transforms over Core (loop elimination, call elimination, SSA,
ANF encoding, structured-to-unstructured, ...) are the special
case where both endpoints are Core itself.

The default placement is *with the definition of Core*, in the
same package — there is no extensibility argument because the
"non-Core side" doesn't exist. The relevant question becomes: do
these transforms need to be importable independently of the full
Core surface? If frontends only need to depend on Core's data
definitions (not its transforms), splitting Core into a narrow
`CoreDef` and a broader `CoreTransforms` lets frontends depend
on the smaller one. (This is a future option, not a current
state.)

The transform-vs-analysis distinction blurs here: many "analyses"
are implemented as transforms (a transform that residualizes the
program, plus a projection that reads off the result). Where the
output is still a Core program, the placement is "with Core";
where the output is something else (a list of obligations, a GOTO
program), the rule defaults back to "with the consumer."

# How this applies to Strata

The current module layout already reflects most of this
philosophy:

```
Strata/Languages/Python/
    ...                       -- Python AST, Python → Laurel passes
                              -- (imports Laurel; Laurel does not
                              -- import Python)

Strata/Languages/Laurel/
    LaurelToCoreTranslator.lean
                              -- Laurel.toCore : LaurelAST → CoreAST
                              -- (imports Core; Core does not import
                              -- Laurel)

Strata/Languages/Core/
    Core.lean, Program.lean, ...
                              -- Core's definition, invariants, WF.
                              -- Imports DDM (foundational; not a
                              -- translation). Imports no
                              -- language- or analysis-specific
                              -- code.

Strata/Backends/CBMC/
    GOTO/CoreToGOTOPipeline.lean
                              -- CBMC.fromCore : CoreAST → GOTO
                              -- (imports Core; Core does not
                              -- import the CBMC translator)
```

The pattern: *every translation lives with the extensible
endpoint*, and that endpoint imports the central one.

## Relation to the proposed repository split (issue #1168)

The repository-split proposal in
[issue #1168](https://github.com/strata-org/Strata/issues/1168)
(see also `docs/RepositorySplitProposal.md`) makes a subset of
these interfaces _physical_ package boundaries:

: `Strata` (main)

  DL, Core, Laurel, SMT dialect, CBMC translator, deductive
  verifier (kept together for now).

: `StrataDDM`

  Dialect Definition Mechanism (already independent).

: `StrataPython`

  Python dialect + `Python → Laurel` translation.

: `StrataBoole`

  Boole dialect + translation to Core.

: `StrataBoogie`

  `Boogie → Strata` translator (separate repo).

: `StrataCLI`

  Top-level executables (separate repo).

: `StrataExperiments`

  Holding pen for experimental code.

Under this split, the philosophy becomes a build-system-enforced
rule for the boundaries that _do_ cross packages:

- `StrataPython` owns `Python.toLaurel` and depends on the main
  `Strata` package; the main package does not depend on
  `StrataPython`.
- `StrataBoole` owns `Boole.toCore` and depends on the main
  `Strata` package; the main package does not depend on
  `StrataBoole`.
- `StrataBoogie` produces `.core.st` / `.laurel.st` artifacts on
  disk — its interface to Strata is the file format, not an
  in-process API.
- `StrataDDM` depends on nothing else in Strata; the main package
  and every front-end depend on it.

The proposal *temporarily keeps the SMT dialect, the CBMC
translator, the deductive verifier, Laurel, and DL together with
Core* in the main `Strata` package, because substantial shared
infrastructure is expected during the initial restructuring. This
is a pragmatic near-term arrangement, not a permanent endorsement;
the eventual goal remains decoupling. A plausible future home for
the analysis-side components is something like a `StrataAnalyses`
package that talks to external tools or in-process analysis
engines. The SMT dialect is named in the proposal as the most
likely first candidate for extraction.

For interfaces that remain _inside_ the main `Strata` package
(Core ↔ Laurel, Core ↔ CBMC translator, Core ↔ SMT dialect, DL ↔
Core), the philosophy applies as a coding convention rather than
a build-time constraint. Holding the line as a coding convention
keeps Core inert and makes any future package extraction a
mechanical move rather than a refactor.

## Applying the principle to Laurel ↔ Core, Core ↔ SMT, and Core ↔ CBMC

The same rule used for the cross-package boundaries also governs
these intra-package translations. The applied rule per direction:

*Laurel → Core (lowering).* Lives in
`Strata/Languages/Laurel/`, not in `Strata/Languages/Core/`.
Laurel imports Core; Core does not import Laurel.

The reasoning is the many-to-one-to-many test, not "who knows
what." Laurel is one of _many_ producers feeding Core (Python
goes through Laurel, future front-ends may too); placing the
translation in Core would couple Core to Laurel's vocabulary —
modifies-clause expansion, short-circuit desugaring, hole
elimination — which other consumers do not need.

This direction matches today's `LaurelToCoreTranslator.lean`.

*Core → Laurel (raising, if added).* Should live in
`Strata/Languages/Laurel/`. Even though the source is Core, the
_target_ is a spoke and Core is the waist; Laurel imports Core,
not the reverse. The general guidance — both lowering and
raising live at the source-facing end — applies here.

*Core → SMT-LIB (encoding).* Should live with the SMT analysis
(today `Strata/DL/SMT/`, possibly a future `Strata/Backends/SMT/`
or `StrataAnalyses`), not in
`Strata/Languages/Core/SMTEncoder.lean`.

The reasoning is the _same_ as for Laurel → Core, applied
symmetrically: the SMT analysis is one of _many_ consumers of
Core (today: deductive verifier; CBMC translator; future:
abstract interpretation, model checkers, ...). Placing the
encoder in Core would couple Core to SMT-specific vocabulary —
sorts, theories, axiomatization choices, quantifier instantiation
hints — that other consumers do not need.

This is the principled answer to the symmetry question raised in
review: Laurel → Core lives outside Core not because "Laurel
maintainers know best," but because Laurel is one of many
producers. Core → SMT lives outside Core for the same structural
reason: SMT is one of many consumers. Stability of SMT-LIB or
CBMC's GOTO format is not the test; many-to-one is.

The current placement is the deviation called out below.

*SMT result → Core (counterexample raising).* Lives with the
SMT analysis. Mapping a solver model back into Core-level
expressions is the SMT analysis's job; Core only owns the
_shape_ of the result it ingests (`VCResult`, `ProofObligation`),
not the conversion logic.

*Core → GOTO (CBMC translator).* Already correct: lives in
`Strata/Backends/CBMC/GOTO/`, imports Core, Core does not import
the CBMC translator. Concrete model: `procedureToGotoCtx`,
`functionToGotoCtx`, `CProverGOTO.Context.toJson` are all in the
translator package, and the serialized `.goto.json` schema is
the wire format the external CBMC tool consumes.

When referring to "CBMC" in this document: the _external CBMC
binary_ is the analysis tool; the _Strata-side translator_ is
the in-process component that produces GOTO JSON for it. They
are different things — the dialect is not the tool.

*CBMC result → Core (counterexample raising, if added).*
Symmetric to the SMT case: lives in the CBMC translator package.
Core defines the result shape; the translator populates it.

Across all six directions the test is the same — _which side has
many counterparts and which side must remain extensible-around
without being touched?_ The "many" side owns the translation;
Core stays inert. The deviations from this rule today are:

1. `Strata/Languages/Core/SMTEncoder.lean` — Core imports
   SMT-specific code. See the note below.
2. `Strata/DL/Imperative/ToCProverGOTO.lean` — A `ToX`
   translation lives with the source side (DL/Imperative)
   instead of with the CBMC translator. Restructuring this into
   the backend follows the same principle.
3. Any future helper that materializes Laurel-shaped output from
   Core would belong in Laurel, not Core.

## A note on `Strata/Languages/Core/SMTEncoder.lean`

The SMT encoder currently lives under `Strata/Languages/Core/`.
Strictly under this philosophy, an SMT encoder reading Core
would live with the SMT analysis (in `Strata/DL/SMT/` or a
successor), and Core would not import anything SMT-specific.

The current placement is a pragmatic choice — VC generation and
SMT encoding are tightly coupled in the deductive verifier — but
it is a deviation. The proposed resolution (referenced from the
package decomposition document) is the right shape: *split
`SMTEncoder.lean` along SMT-specific and Core-specific axes* —
move generic SMT context structures into the SMT package, keep
the Core-specific encoding logic with Core. The two concerns are
close to logically independent today.

If future analyses follow the same fine-grained encoding pattern,
the same split applies: the analysis-specific bits live with the
analysis; only the Core-shaped projection logic is allowed to
live with Core.

# When to break the rule

Three legitimate reasons to put `fromIR1` _inside_ IR1:

1. *The target is part of the same library boundary.* A
   Core-internal "post–partial-evaluation residual" form, for
   example: both ends live in Core, no extensibility concern,
   no external API surface.
2. *The target is canonical and unique.* If there will only
   ever be one external form — e.g. Ion serialization as _the_
   binary format — keeping `Core.toIon` inside Core is fine.
   The extensibility argument only matters when there is more
   than one target.
3. *The translation is the inverse of a parser.*
   Pretty-printing is arguably not even a translation — it
   produces text rather than an in-memory AST — but it is worth
   calling out explicitly: it conventionally lives next to
   parsing, both belong with the language definition, and no
   one-to-many question arises.

For everything else — multiple front-ends, multiple analyses,
multiple external-tool adapters, evolving IRs — keep
translations on the *outside* and the central IR on the
*inside*.

# Checklist for adding a new translation

1. *Apply the one-to-many test:*
   1. If one side is Core, the translation lives on the non-Core
      side.
   2. If one side is _one_ and the other is _many_, the
      translation lives on the _many_ side.
   3. If neither side has a natural claim, place it in a
      standalone translation module that depends on both.
2. The module that owns the translation imports the central /
   one side. The central / one side *does not import* the
   module that owns the translation.
3. Place the tests next to the translation. End-to-end tests
   spanning multiple components live in a separate top-level
   test module.
4. Confirm the dependency graph remains a DAG (no cycles).
5. If the translation needs to preserve provenance (source
   ranges, metadata, related-positions), thread it through
   explicitly — provenance is part of the IR contract, not a
   side channel.
6. Distinguish _in-process analysis_ placement (purely Strata
   code) from _external-tool_ placement (talks to a separate
   program). They can be the same package today, but the
   boundary should be visible so they can be split later.
7. If raising (counterexamples, source-mapped diagnostics) is
   needed, plan it at _every_ level — raising mirrors the
   lowering chain, not just the front-end.

If the answer to (1) is "they're equally central," the two IRs
probably want a third, smaller IR between them, or one of them
is trying to be both a producer and a consumer and should be
split.

# Why this matters at scale

Every property the high-level architecture relies on for scale
— caching translations by content hash, parallelizing analyses,
swapping external tools, adding new front-ends without
recompiling Core, running differential testing across analyses
— depends on the central IR being inert. The moment Core starts
importing language- or analysis-specific code, those properties
degrade:

- Caching keys become coupled across unrelated front-ends.
- A change to one analysis forces rebuilds of the whole graph.
- Differential testing has to special-case which analysis
  "owns" shared code.
- New front-ends can't be added without modifying Core.

Keeping translations on the outside is therefore not just a
stylistic preference; it is the structural property that lets
Strata grow in features without growing in coupling.
