# Front-End Hosting & Governance

This document covers where to host your Strata front-end code, how to structure it, and how to interact with the Strata team. For the technical guide on building a front-end, see [Front-End Guide](frontend_guide.md). For testing and validation, see [Testing & Validation](frontend_testing.md).

## Where should my front-end code be hosted?

There are three ways to host a new front-end, each with different tradeoffs for developers and users. The right choice depends on your project's maturity, how tightly you want to coordinate with the Strata team, and how much autonomy you need.

### Option 1: Inside the official Strata repository

Your front-end lives alongside the core Strata code in [strata-org/Strata](https://github.com/strata-org/Strata).

**Developer experience:**
- Direct access to all internal APIs with no dependency indirection.
- When Strata maintainers make breaking changes to internal APIs (e.g., renaming a Laurel constructor, changing a DDM type), they can fix your front-end in the same PR. You don't wake up to a broken build after a Strata update. Your front-end is built and tested on every Strata CI run. This catches regressions early, but also means your tests must pass for anyone's PR to merge. You need to coordinate with Strata maintainers on code review, style, and structure. There is more process overhead.

**User experience:** Users get your front-end automatically when they clone Strata and run `lake build`. Zero extra setup. Running `lake exe StrataVerify MyFile.yourlang.st` works out of the box. Your front-end appears in the same documentation, examples directory, and test suite. It feels like a first-class part of Strata.

**Requirements:** Inclusion in the official repository requires approval from the Strata maintainers. A typical path is to develop in a fork or separate repository first, then propose inclusion once the front-end is mature. To be accepted, it must meet a quality bar that ensures long-term maintainability:

- A clear translation pipeline with tests covering the supported language features.
- Accurate propagation of source code locations through the translation pipeline, enabling meaningful error messages.
- Consistent code structure following the patterns described in the [codebase structure](#how-should-i-structure-my-front-end-codebase) section.
- Documentation of design decisions and known limitations.
- Differential testing infrastructure that validates the translation against the source language's reference implementation, where feasible.

Front-ends that are officially maintained by AWS within the strata-org repository are held to a higher standard, including ongoing maintenance commitments and broader test coverage.

### Option 2: Separate repository in the `strata-org` GitHub organization

Your front-end lives in its own repository (e.g., `strata-org/strata-yourlang`) under the Strata GitHub organization.

**Developer experience:**
- You have your own repository with your own CI, release cadence, and PR process.
- You depend on Strata as a Lake dependency (a `[[require]]` in your `lakefile.toml` pointing at `strata-org/Strata`), pinning to a specific Strata revision and updating on your own schedule.
- When Strata makes a breaking change, you are responsible for updating your code to match. There is a lag between Strata changes and your adaptation.
- Being in the `strata-org` organization provides visibility to Strata maintainers, which makes coordination easier, but does not imply the same level of support as the official repository.
- Less coordination overhead than option 1, but you give up some autonomy (org admins control repository settings and permissions).

**User experience:**
- Users need to add your repository as a Lake dependency or clone it separately. It's an extra setup step.
- Users may hit version mismatches — your front-end might be pinned to a specific Strata revision while they are on main. They need to be aware of compatibility.
- Discoverability is good — users browsing the `strata-org` GitHub organization will find your front-end alongside Strata itself.

### Option 3: Separate repository outside the `strata-org` organization

Your front-end lives in your own GitHub organization or personal account.

**Developer experience:**
- Maximum autonomy. Your repository, your organization, your rules. No coordination with Strata maintainers required.
- Same Lake dependency mechanism as option 2 — you pin to a Strata revision and update when you want.
- Same responsibility for tracking breaking changes as option 2.
- The downside is isolation: Strata maintainers have no visibility into your project. If they are considering a breaking change, they won't know to check whether it affects you.

**User experience:** Same setup burden as option 2 (add a Lake dependency, build separately). Discoverability is comparable to option 2: the Strata repository maintains a list of known external front-ends, so users browsing Strata will find your project. However, there is no organizational endorsement — the listing makes your front-end discoverable but does not imply that the Strata team vouches for its quality or maintenance status. Version compatibility is entirely on the user to figure out. The listing in Strata can include a note about which Strata version your front-end was last tested against, but there is no organizational mechanism to enforce that it stays up to date.

### How to choose

| Dimension | In Strata repo | Separate repo in `strata-org` | Separate repo outside |
|---|---|---|---|
| Breaking change protection | Strata maintainers fix your code | You fix it yourself | You fix it yourself |
| User setup | Zero (comes with Strata) | One extra Lake dependency | One extra Lake dependency |
| Development velocity | Slower (shared CI, reviews) | Medium (own CI, some coordination) | Fastest (fully independent) |
| Discoverability | Automatic | Good (same org) | Good (listed in Strata repo) |
| Trust signal to users | Strongest (part of official project) | Good (endorsed by org) | Neutral (listed, not endorsed) |
| Maintenance commitment | Shared with Strata team | Yours, but visible to org | Entirely yours |

A natural progression is to start with option 3 (or option 2 if you can get org access) to iterate quickly with minimal coordination overhead, then move to option 1 once the front-end is mature and meets the quality bar. If your front-end doesn't yet meet the bar for option 1, that's fine — we can work with you to define a path to get there.

---

## How should I structure my front-end codebase?

This structure applies regardless of where your front-end is hosted — whether inside the Strata repository, in a separate `strata-org` repo, or in your own repository. Add each new dialect under [`Strata/Languages/YourDialect/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/). The existing dialects follow a consistent pattern, with the following categories of files:

1. **Root module file (`YourDialect.lean`)** — Re-exports everything. This is the entry point. Keep it minimal, just imports.

2. **Grammar / Parsing** — Every dialect that parses `.st` files has a subdirectory for this. The naming varies: Core uses [`DDMTransform/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Core/DDMTransform/), Laurel uses [`Grammar/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/Grammar/). Typical contents:
   - A grammar definition file (`Grammar.lean` or `Parse.lean`) — DDM grammar definition (concrete syntax tree)
   - A CST-to-AST translation file (`Translate.lean`, `ASTtoCST.lean`, or `ConcreteToAbstractTreeTranslator.lean`)
   - Optionally a `.st` grammar file (like Laurel's [`LaurelGrammar.st`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/Grammar/LaurelGrammar.st))

3. **AST and type definitions** — The core data structures of your dialect. Look at how [`C_Simp`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/C_Simp/) defines its expression/statement types by reusing the Lambda and Imperative expression and statement types:
   - Define type aliases for expressions using `Lambda.LExpr` or Core expressions
   - Define commands and statements using `Imperative.Stmt`/`Imperative.Cmd`
   - Add dialect-specific constructs (like Laurel's `Identifier`, `Operation`, `TypeHierarchy`)

4. **Translation to a lower dialect** — The key file. This could translate directly to Core, or go through an intermediate dialect such as Laurel.

5. **Dialect-specific passes** — You may want to do pre-translation transformations on your own AST. Laurel is the best example here with multiple passes:
   - [`Resolution.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/Resolution.lean) — Name resolution
   - [`DesugarShortCircuit.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/DesugarShortCircuit.lean) — Desugar complex expressions
   - [`LiftImperativeExpressions.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LiftImperativeExpressions.lean) — Normalize expressions
   - [`HeapParameterization.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/HeapParameterization.lean) — Heap modeling
   - [`EliminateHoles.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/EliminateHoles.lean), [`InferHoleTypes.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/InferHoleTypes.lean) — Type inference

6. **Analysis entry point (such as verification)** — Orchestrates a full pipeline: parse → transform → translate → analyze.

Add a mirrored test structure under [`StrataTest/Languages/YourDialect/`](https://github.com/strata-org/Strata/blob/main/StrataTest/Languages/):
- Unit test `.lean` files at the top level
- `examples/` or `tests/` subdirectory for `.st` test programs
- `expected_*/` directories for golden-file testing if needed

Don't reinvent expression or statement representations. [`C_Simp`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/C_Simp/) shows an example of this. Your dialect should parameterize over these existing building blocks when possible and only add what's genuinely new.

---

## How do I ask for Strata features for my front-end and what support can I expect from Strata maintainers?

If a feature you need would benefit multiple source languages (e.g., a new Laurel construct, a Core transformation, or a DDM capability), it will be considered and prioritized by the Strata maintainers. Open an issue on the [strata-org/Strata](https://github.com/strata-org/Strata) repository describing the feature, the use case, and which languages would benefit.

For features that are specific to a single front-end, the Strata team can help by reviewing pull requests and providing guidance on how to integrate with existing infrastructure, but the implementation responsibility stays with the front-end team.
