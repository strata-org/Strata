# Best Practices for New Front-End Definitions

## Executive Summary

This guide provides documentation for developers building new front ends to Strata. This document is intended for compiler engineers, programming language researchers, and verification tool developers who want to integrate their source languages with the Strata analysis ecosystem. Whether you're adding support for a new programming language, domain-specific language, or extending an existing front-end, this guide will walk you through good architectural decisions, implementation patterns, and development practices.

## Why This Matters

Building a correct front-end is challenging. It requires a deep understanding of both your source language's semantics and Strata's IR design. Poor translation choices can lead to unsound verification results or make certain properties impossible to verify. This guide distills lessons learned from existing implementations to help you avoid common pitfalls and build robust, maintainable front ends.

## Getting Started

The guide consists of answers to several key questions, organized to support both linear reading and targeted references. New developers should start with the architecture overview and core translation concepts before diving into implementation details. Experienced developers can jump directly to specific sections addressing their immediate needs.

## Architecture & Design

### What are the main components of a Strata front-end?

A Strata front end parses text written in an existing source language and translates it to a representation in a Strata dialect. To do this, it needs several components:

- **A parser for the source language.** We typically recommend that this be the standard parser for the source language, perhaps the one used by a standard production compiler, interpreter, or analyzer for that language, to ensure that it accurately captures the structure of all source programs of interest and can be maintained as easily as possible as the language evolves. This will often be implemented in the source language itself, or at the very least in a language different than Lean, the language used to implement Strata.

- **Data structures to represent the Strata dialect.** Although it would be possible to traverse the AST of the source language and directly generate the textual or binary representation of a Strata dialect, doing so would involve complex code that is difficult to understand and audit. So, we recommend an AST-to-AST translation from the source language to the Strata dialect. The Strata Dialect Definition Mechanism (DDM) can generate an AST in Java, Lean, or Python from a high-level description of the dialect in the DDM DSL that can serve as the target of this translation.

- **Code to translate between the source language and the Strata dialect.** Given ASTs for both the source language and a Strata dialect, one component of the front end will need to traverse an instance of the former to produce an instance of the latter. This will generally need to be written by hand (or using an AI agent), and its complexity will depend on how different the chosen Strata dialect is from the source language. It's possible for a Strata dialect to exactly mirror the structure of a source language, in which case this translation will be straightforward and mechanical (and possibly even auto-generated, as in the Python dialect described below).

- **A serializer for the Strata dialect.** Given that the parser and translator are likely written in a different language than Strata itself, it will usually be necessary to serialize the AST produced by the previous component to send it to the Strata implementation. The DDM will also generate such a serializer (and de-serializer) when it generates the AST for a dialect.

### What are examples of existing front ends (Python, Java) and their design decisions? What is the recommended translation pipeline (e.g., source language → high-level Strata → Core)?

Two of the existing Strata front ends, Java and Python, illustrate our two recommended approaches to front end development and the tradeoffs between them.

- **The Java front end** (TODO: link once source repo is public) is implemented as a plugin for the Java compiler. It works by running a few initial compiler stages to simplify the program and then translating the resulting, simpler Java code into the Laurel dialect. This dialect is a memory-safe imperative language intended to capture patterns that are common between languages such as Java, JavaScript, and Python. This choice makes the translation from Java to Laurel relatively straightforward but still non-trivial. It also allows a developer familiar with Java (and Laurel) to implement the translation even if they are not familiar with Lean.

- **The Python front end** is implemented as a client of the Python AST library. A pre-processing phase, which needs to be performed only once per Python version, traverses the structure of the AST provided by that library and auto-generates a Strata dialect corresponding to that version of Python. The front end proper then traverses the AST of an input program and performs the trivial translation into the Python dialect and serializes the result to send to Strata. The core of this traversal is automatically generated from the mechanized description of the Python AST. The translation from the Python dialect into other Strata dialects (Laurel, in this case) occurs within Strata itself.

There is a tradeoff between these two approaches, so which one to choose depends on the specifics of an individual use case. However, in general, the approach of directly representing the source language in a dialect, as we do for Python, has several advantages:

- It makes it possible to define a semantics for the source language within Strata, which opens the possibility of proving that any further translations preserve the semantics of the original program.
- It makes it possible to implement the translation to further Strata dialects in Lean. Lean is a particularly nice language for writing translations, and a Lean implementation can share utility code with other translations.

However, it also has several disadvantages:

- It requires creating a dialect matching the source language, which can require substantial work if a machine-readable description for that language isn't readily available (as it is for Python).
- Writing further translations in Lean requires familiarity with Lean, which is likely a less widely known language than that used to implement some existing parser for the chosen source language.

### What are the existing Strata dialects? How should I choose which Strata dialect to target for my source language?

Strata currently includes the following key dialects (though more can be added at any time):

- **Python.** This dialect directly represents the Python language. It is automatically generated from the Python `ast` module, so variations of it can exist for any Python version.

- **Laurel.** This dialect is intended to capture the common semantic structures that exist across several memory-safe, imperative, object-oriented languages including Java, JavaScript, and Python. These structures include the ability to nest operations with side effects within expressions and built-in support for heap-allocated objects with fields.

- **Core.** This dialect is the heart of Strata, and most analyses are implemented by first translating into Strata Core and then to the representation naturally used by the analysis. It is slightly simpler than Laurel, as well as more general, being able to represent the semantics of artifacts written in a wider variety of languages using core constructs drawn from both functional and imperative programming. Unlike the first two dialects above, the Core dialect has formally specified semantics.

- **SMT.** This dialect directly represents the SMT-LIB language (v2.7) used to communicate with SMT solvers. It is used by the deductive verification implementation in Strata to represent verification conditions. By including it as an explicit dialect, we make it possible to prove that Strata's verification condition generator is correct. Including it as a dialect has additional benefits, because the DDM automatically generates a parser for it which can be used to parse the responses from an SMT solver (such as complex models for satisfiable queries, which are left unhandled by many existing tools).

---

## Core Translation Concepts

### How do I map source language constructs to Strata dialect constructs?

The first step is to choose a target dialect. It's typically best to choose the dialect that is most similar to your source language, to make the mapping as simple as possible. Next, many of the steps required to perform a semantics-preserving transformation from the constructs available in a typical source language into the fewer but more general constructs in a Strata dialect follow the same patterns used in compilers. A book like *Modern Compiler Implementation*, especially the chapter on translation to IRs, can be helpful background.

### What are the semantics preservation requirements when translating to Strata?

Strata is intended to allow multiple analyses to be implemented for multiple source languages without requiring excessive duplication of effort. For this to be effective, a front end must capture the semantics of the original source as accurately as possible, so that whatever details an analysis might need are guaranteed to be available. Although the exact details of "as accurately as possible" depend on what details of each language are included in a formal semantics, a general rule of thumb would be to treat a Strata front end more like you would when implementing a compiler than you might when, say, implementing a narrowly-targeted static analysis tool.

### How do I represent contracts, invariants, and verification objectives in Strata?

The dialects that support imperative programming constructs (such as Laurel and Core) include, at the very least, assumption and assertion statements. In principle, any verification objectives can be represented using these alone. However, Laurel and Core both also include built-in notions of contracts that can be directly targeted. Both languages allow preconditions and postconditions on procedures and invariants on loops.

If you're targeting a dialect that does not directly include such constructs, it's still possible to attach arbitrary expressions as metadata to Strata AST nodes, though backend analyses will typically need to be updated slightly to interpret this metadata.

---

## Implementation Guide

This section provides guidance for writing code that constructs and manipulates the AST for a Strata dialect. This includes the APIs for building types, expressions, and statements, managing scoping and variable binding, and implementing lowering passes between dialects. Throughout this section, we use the Python front-end as a running example. Its external tooling (parser, dialect generator, serializer) lives in [`Tools/Python/strata/`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/), and its Lean-side translators live in [`Strata/Languages/Python/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/) (with tests in [`StrataTest/Languages/Python/`](https://github.com/strata-org/Strata/blob/main/StrataTest/Languages/Python/)).

Note: AI coding agents (e.g. Amazon Kiro) can significantly accelerate front-end development. They are already proficient in Lean 4 and most common source languages, and can help with writing translation functions, generating boilerplate, and navigating the Strata codebase. Consider using one throughout the process.

### What are the prerequisites for building a Strata front-end (knowledge of Lean, understanding of IRs, etc.)?

Building a Strata front-end requires knowledge at several layers, though not all of it is needed upfront:

- **Understanding your target dialect** (e.g. Laurel). You need to understand its intermediate representation, its type system, its AST, and its procedure model.

- **Working knowledge of Lean 4 syntax.** Not deep theorem-proving expertise, but enough to write pattern-matching functions, work with monadic error handling (`Except`), and navigate inductive types. The Python front-end's [`PythonToLaurel.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/PythonToLaurel.lean) is a good example: it's essentially a large match over the source AST constructors, recursively building Laurel `StmtExprMd`.

- **Understanding the DDM pipeline.** How a dialect defines syntactic categories and operations, how those get serialized to Ion, and how `#load_dialect` / `#strata_gen` (in [`Strata/DDM/Integration/Lean/`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/Integration/Lean/)) auto-generate Lean types from dialect files. The Python front-end demonstrates this well: [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) introspects Python's `ast` module to programmatically generate a DDM dialect via calls like `PythonAST.add_syncat("expr")` and `PythonAST.add_op("IntPos", ...)`, then the `Parser` class walks the native AST and emits DDM `Operation` nodes.

- **Conceptual understanding of verification** (helpful but not strictly required, and only to the extent that you intend to verify programs in the language you're adding). Knowing that `Assert` nodes become proof obligations, that loops require invariants for an SMT solver to reason about them, and that procedures need contracts helps you make sound translation choices. You do not need to understand the SMT encoding or the Core VCG internals to get started.

### Where should my front-end code be hosted?

There are three ways to host a new front-end, each with different tradeoffs for developers and users. The right choice depends on your project's maturity, how tightly you want to coordinate with the Strata team, and how much autonomy you need.

#### Option 1: Inside the official Strata repository

Your front-end lives alongside the core Strata code in [strata-org/Strata](https://github.com/strata-org/Strata).

**Developer experience:**
- Direct access to all internal APIs with no dependency indirection.
- When Strata maintainers make breaking changes to internal APIs (e.g., renaming a Laurel constructor, changing a DDM type), they can fix your front-end in the same PR. You don't wake up to a broken build after a Strata update. Your front-end is built and tested on every Strata CI run. This catches regressions early, but also means your tests must pass for anyone's PR to merge. You need to coordinate with Strata maintainers on code review, style, and structure. There is more process overhead.

**User experience:** Users get your front-end automatically when they clone Strata and run `lake build`. Zero extra setup. Running `lake exe StrataVerify MyFile.yourlang.st` works out of the box. Your front-end appears in the same documentation, examples directory, and test suite. It feels like a first-class part of Strata.

**Requirements:** To have your front-end included in the official repository, it must meet a quality bar that ensures long-term maintainability:

- A clear translation pipeline with tests covering the supported language features.
- Consistent code structure following the patterns described in the [codebase structure](#how-should-i-structure-my-front-end-codebase) section.
- Documentation of design decisions and known limitations.

Front-ends that are officially maintained by AWS within the strata-org repository are held to a higher standard, including ongoing maintenance commitments and broader test coverage.

#### Option 2: Separate repository in the `strata-org` GitHub organization

Your front-end lives in its own repository (e.g., `strata-org/strata-yourlang`) under the Strata GitHub organization.

**Developer experience:**
- You have your own repository with your own CI, release cadence, and PR process.
- You depend on Strata as a Lake dependency (a `[[require]]` in your `lakefile.toml` pointing at `strata-org/Strata`), pinning to a specific Strata revision and updating on your own schedule.
- When Strata makes a breaking change, you are responsible for updating your code to match. There is a lag between Strata changes and your adaptation.
- Being in the `strata-org` organization signals that the project is recognized by the Strata community. Strata maintainers have direct visibility since they own the org, which makes it easier to coordinate on compatibility.
- Less coordination overhead than option 1, but you give up some autonomy (org admins control repository settings and permissions).

**User experience:**
- Users need to add your repository as a Lake dependency or clone it separately. It's an extra setup step.
- Users may hit version mismatches — your front-end might be pinned to a specific Strata revision while they are on main. They need to be aware of compatibility.
- Discoverability is good — users browsing the `strata-org` GitHub organization will find your front-end alongside Strata itself.

#### Option 3: Separate repository outside the `strata-org` organization

Your front-end lives in your own GitHub organization or personal account.

**Developer experience:**
- Maximum autonomy. Your repository, your organization, your rules. No coordination with Strata maintainers required.
- Same Lake dependency mechanism as option 2 — you pin to a Strata revision and update when you want.
- Same responsibility for tracking breaking changes as option 2.
- The downside is isolation: Strata maintainers have no visibility into your project. If they are considering a breaking change, they won't know to check whether it affects you.

**User experience:** Same setup burden as option 2 (add a Lake dependency, build separately). Discoverability is comparable to option 2: the Strata repository maintains a list of known external front-ends, so users browsing Strata will find your project. However, there is no organizational endorsement — the listing makes your front-end discoverable but does not imply that the Strata team vouches for its quality or maintenance status. Version compatibility is entirely on the user to figure out. The listing in Strata can include a note about which Strata version your front-end was last tested against, but there is no organizational mechanism to enforce that it stays up to date.

#### How to choose

| Dimension | In Strata repo | Separate repo in `strata-org` | Separate repo outside |
|---|---|---|---|
| Breaking change protection | Strata maintainers fix your code | You fix it yourself | You fix it yourself |
| User setup | Zero (comes with Strata) | One extra Lake dependency | One extra Lake dependency |
| Development velocity | Slower (shared CI, reviews) | Medium (own CI, some coordination) | Fastest (fully independent) |
| Discoverability | Automatic | Good (same org) | Good (listed in Strata repo) |
| Trust signal to users | Strongest (part of official project) | Good (endorsed by org) | Neutral (listed, not endorsed) |
| Maintenance commitment | Shared with Strata team | Yours, but visible to org | Entirely yours |

A natural progression is to start with option 3 (or option 2 if you can get org access) to iterate quickly with minimal coordination overhead, then move to option 1 once the front-end is mature and meets the quality bar. If your front-end doesn't yet meet the bar for option 1, that's fine — we can work with you to define a path to get there.

### How should I structure my front-end codebase?

Add each new dialect under [`Strata/Languages/YourDialect/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/). The existing dialects follow a consistent pattern, with the following categories of files:

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

### What is the API for constructing a dialect's AST programmatically?

The API has two layers: dialect definition and program construction. Both are provided by the `strata.base` Python module (see [`Tools/Python/strata/base.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/base.py)).

At the **dialect definition layer**, you create a `Dialect` object and populate it with syntactic categories (`SynCatDecl`) and operations (`OpDecl`). A syntactic category groups related AST nodes (e.g., one per Python AST base class). An operation defines a concrete AST node with typed arguments and a result category. The Python front-end's `gen_dialect()` in [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) shows this concretely: it calls `PythonAST.add_syncat("expr")` to create the expression category, then `PythonAST.add_op("IntPos", ArgDecl("v", Init.Num()), PythonAST.int())` to define a positive-integer node. Once defined, `OpDecl` objects are callable — e.g. `PythonAST.IntPos(NumLit(42))` constructs an `Operation` node. The dialect is serialized to Ion via `Dialect.to_ion()`.

At the **program construction layer**, you walk the source language's native AST and emit `Operation` nodes. The key value types are `NumLit`, `StrLit`, `Ident`, `OptionArg`, and `Seq`. Every node can carry a `SourceRange(offset, end_offset)` via the `ann=` keyword argument, which propagates byte offsets through to verification error messages. The Python parser's `ast_to_arg` method in [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) is the canonical example of this dispatch. The final result is a `Program` object to which you add the top-level `Operation` with `p.add(op)`, and then serialize with `p.write(output_path)`.

### How do I implement lowering passes between Strata dialects?

A lowering pass is a set of mutually recursive functions that pattern-match on the source AST and construct target AST nodes. There is no framework or base class to inherit from. The two canonical examples are:

- **Source-to-Laurel translators** (like [`PythonToLaurel.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/PythonToLaurel.lean)): a `translateExpr` for expressions, a `translateStmt` for statements, a `translateType` for types, and a top-level `translateProcedure` that assembles the pieces.

- **[`LaurelToCoreTranslator.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LaurelToCoreTranslator.lean)**: the more complex case where source and target have fundamentally different representations. Laurel uses a unified `StmtExpr` type, while Core separates expressions (`Core.Expression.Expr` with de Bruijn indices) from statements (`Core.Statement`). The translator has `translateExpr` and `translateStmt` entry points, handles the split between Core functions and procedures, and runs Laurel-to-Laurel passes ([`LiftImperativeExpressions`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LiftImperativeExpressions.lean), [`HeapParameterization`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/HeapParameterization.lean), [`ModifiesClauses`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/ModifiesClauses.lean)) before lowering.

A new lowering pass follows the same recipe: define your recursive translators, thread the environment, and wire them into the pipeline at the appropriate point.

### How do I ask for Strata features for my front-end and what support can I expect from Strata maintainers?

If a feature you need would benefit multiple source languages (e.g., a new Laurel construct, a Core transformation, or a DDM capability), it will be considered and prioritized by the Strata maintainers. Open an issue on the [strata-org/Strata](https://github.com/strata-org/Strata) repository describing the feature, the use case, and which languages would benefit.

For features that are specific to a single front-end, the Strata team can help by reviewing pull requests and providing guidance on how to integrate with existing infrastructure, but the implementation responsibility stays with the front-end team.

### What are performance considerations for the translation process?

Some considerations include:

- If your dialect has nested or recursive structures (e.g., nested pattern matching, comprehensions), flatten them early. Deeply nested translations produce deeply nested verification conditions that are harder for SMT solvers.

- Core uses a flat variable namespace. If your high-level dialect has lexical scoping, shadowing, or closures, you need a renaming strategy. Generating fresh names naively (e.g., appending counters) is fine for correctness but can produce huge variable sets that slow down SMT encoding.

- The biggest performance bottleneck is usually the SMT solver. Transformations that produce smaller, more modular verification conditions (VCs) win.

- Prefer generating multiple smaller procedures with tight contracts over one monolithic procedure. The [`CallElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/CallElim.lean) transformation replaces calls with `assert pre; havoc; assume post`, which is much cheaper than inlining entire bodies.

- If your dialect has features that map to quantifiers (e.g., `forall x in collection`), be careful — quantifiers are expensive for SMT solvers. Use triggers where possible (Lambda expressions support quantifiers with triggers) but also consider whether an encoding that does not use quantifiers is possible.

- The order you compose transformations matters. For example, if your dialect has both loops and procedure calls, translating to Core first and then running [`CallElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/CallElim.lean) → [`LoopElim`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/LoopElim.lean) is the standard pipeline. But if your high-level construct can be desugared to avoid loops entirely (e.g., bounded iteration → unrolling), doing that before hitting Core avoids the need for loop invariants.

- Core's `Map` type uses Select/Store axioms, which are well-supported by SMT but can be expensive with many updates. If your dialect has data structures that map to nested maps (e.g., objects with fields that are themselves maps), the encoding can explode. Consider flattening where possible.

- Core supports polymorphic types, but SMT-LIB has limited polymorphism support. The SMT encoder must monomorphize or use sort encodings. If your dialect introduces many generic types, the encoding overhead grows. Prefer concrete types where the high-level semantics allow it.

- Profile with actual examples early. A transformation that looks clean structurally can still produce VCs that time out on the solver.

## Validation & Testing

### How do I validate that my front-end preserves source language semantics?

To validate that your front-end preserves source language semantics, the recommended approach is differential testing with an executable intermediate representation. Build a testing framework that compiles the same program twice: once using the standard language compiler (like `javac` for Java or CPython for Python) and once through your Strata front-end. Execute both versions and compare their outputs for equivalence. If the outputs match, your translation correctly preserves the source language semantics. This approach provides independent validation of your front-end without requiring full end-to-end verification workflows, making debugging significantly easier when issues arise. Most Strata dialects have well-defined executable semantics. You can reuse the execution engine of your target dialect to build the differential testing infrastructure.

### What code coverage targets should I aim for?

When building a new Strata front-end, you should aim for at least 80% feature-level coverage of the language features you intend to support. This means tracking not just the percentage of tests that pass, but specifically which language constructs and features are validated by your passing tests. Feature-level coverage ensures you are systematically testing critical language capabilities like lambdas, generics, polymorphism, exception handling, and concurrency primitives rather than just accumulating test counts. Map each test case to the specific language features it exercises, allowing you to identify gaps where certain features remain untested and prioritize improvements accordingly.

Beyond feature coverage, track your test pass rate as a complementary metric that measures overall translation correctness. The framework should maintain both metrics over time, enabling you to monitor progress and detect regressions. For languages with comprehensive conformance test suites (like Python's CPython tests, or TypeScript's ECMAScript Test Suite), these official suites provide excellent baseline coverage targets since they're designed to validate complete language specification compliance. Start with these established test collections rather than building from scratch, as they represent the same standards used by the language maintainers themselves.

## Appendix – technical questions

### How do I debug translation issues?

Implement detailed logging throughout your translation pipeline to facilitate systematic debugging. Your framework should capture intermediate representations at key transformation points—the parsed abstract syntax tree from the source language, the generated Strata IR, and execution traces from both the reference compiler path and your Strata path. When a differential test fails, these logs allow you to pinpoint exactly where the translation diverged by comparing intermediate states. Additionally, maintain a coverage tracking system that maps test outcomes to specific language features over time, creating an audit trail that shows which features consistently pass, which fail, and which remain untested. Log execution metadata like timeout occurrences, crashes, or infinite loops when running on large real-world codebases, as these robustness issues often reveal edge cases that small unit tests miss.

### What utilities does Strata provide for AST manipulation and transformation?

Strata provides utilities at three levels:

**DDM level:** The [`strata.base`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/base.py) Python module provides `Dialect`, `OpDecl`, `SynCatDecl`, and `Operation` classes for programmatically defining and constructing ASTs. On the Lean side, `#load_dialect` and `#strata_gen` (in [`Strata/DDM/Integration/Lean/`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/Integration/Lean/)) auto-generate typed Lean inductive types from a dialect's Ion file. [`Strata/DDM/Ion.lean`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/Ion.lean) handles Ion serialization/deserialization, and [`Strata/DDM/AST.lean`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/AST.lean) provides the generic AST representation all dialects share. [`Strata/DDM/Util/`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/Util/) contains helpers for `SourceRange` tracking, and various `List`, `Array` utilities. [`Strata/DL/Util/`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Util/) provides [`StringGen`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Util/StringGen.lean) for fresh name generation, [`LabelGen`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Util/LabelGen.lean) for unique label creation, and [`Map`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Util/Map.lean)/[`ListMap`](https://github.com/strata-org/Strata/blob/main/Strata/DL/Util/ListMap.lean) utilities.

**Laurel level:** Several Laurel-to-Laurel transformation passes run before Core translation and serve as examples for AST manipulation:
- [`LaurelTypes.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LaurelTypes.lean) provides `computeExprType`, which computes the `HighType` of any `StmtExprMd` given a type environment — used for operator dispatch (e.g., deciding whether `+` means `Add` or `StrConcat`).
- [`LaurelFormat.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LaurelFormat.lean) provides pretty-printing (`formatStmtExpr`, `formatHighType`) for debugging.
- [`LiftImperativeExpressions.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LiftImperativeExpressions.lean) hoists assignments out of expression contexts into preceding statements.
- [`HeapParameterization.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/HeapParameterization.lean) analyzes which procedures read or write the heap and adds explicit heap parameters.
- These passes compose in a pipeline: the [`LaurelToCoreTranslator`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LaurelToCoreTranslator.lean) calls them before translating to Core, and they operate on the same `StmtExprMd` / `Program` types that the front-end translator produces.

**Core level:** [`Strata/Transform/`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/) provides program-to-program transformations on the Imperative dialect's `Stmt` type. [`LoopElim.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/LoopElim.lean) replaces loops with invariant checks, havocs, and guard assumptions. [`CallElim.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Transform/CallElim.lean) replaces procedure calls with their contracts. A front-end developer doesn't typically write new Core transforms, but understanding that they exist — and that the pipeline applies them automatically — is important for knowing what the front-end's output needs to look like (e.g., loops need invariants, procedures need contracts).

### How do I handle scoping and variable binding?

Scoping and variable binding are handled entirely at the translator level — neither the DDM dialect nor the Laurel IR has a built-in notion of scope. The key patterns are:

- **Thread a type environment** through the recursive AST walk. The translator's `translateStmt` returns an updated environment alongside the translated Laurel node. In the Python front-end ([`PythonToLaurel.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/PythonToLaurel.lean)), this is `TranslationContext` with a `variableTypes : List (String × String)` field — when an annotated assignment like `x: int = 5` is encountered, the translator appends `(varName, varType)` to the context and returns the new context alongside the `LocalVariable` node.

- **Laurel uses flat name-based binding.** `LocalVariable "x" TInt (some init)` introduces `x` into the enclosing block, and `Identifier "x"` references it by name. There are no de Bruijn indices or explicit scope markers at the Laurel level. Scoping is lexical-by-convention: a variable declared inside a block is visible to subsequent statements because the environment is threaded forward, but it doesn't leak out.

The front-end developer doesn't need to implement scope resolution machinery — just thread the environment correctly and emit `LocalVariable` / `Identifier` nodes with consistent names.
