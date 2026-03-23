# Best Practices for New Front-Ends Definition

## Executive Summary

This guide provides documentation for developers building new front ends to Strata. This document is intended for compiler engineers, programming language researchers, and verification tool developers who want to integrate their source languages with the Strata analysis ecosystem. Whether you're adding support for a new programming language, domain-specific language, or extending an existing front-end, this guide will walk you through good architectural decisions, implementation patterns, and development practices.

## Why This Matters

Building a correct front-end is challenging. It requires a deep understanding of both your source language's semantics and Strata's IR design. Poor translation choices can lead to unsound verification results or make certain properties impossible to verify. This guide distills lessons learned from existing implementations to help you avoid common pitfalls and build robust, maintainable front ends.

## Getting Started

The guide consists of answers to several key questions, organized to support both linear reading and targeted references. New developers should start with the architecture overview and core translation concepts before diving into implementation details. Experienced developers can jump directly to specific sections addressing their immediate needs.

---

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

- **The Python front end** is implemented as a client of the Python `ast` library. A pre-processing phase, which needs to be performed only once per Python version, traverses the structure of the AST provided by that library and auto-generates a Strata dialect corresponding to that version of Python. The front end proper then traverses the AST of an input program and performs the trivial translation into the Python dialect and serializes the result to send to Strata. The core of this traversal is automatically generated from the mechanized description of the Python AST. The translation from the Python dialect into other Strata dialects (Laurel, in this case) occurs within Strata itself.

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

This section provides guidance for writing code that constructs and manipulates the AST for a Strata dialect. This includes the APIs for building types, expressions, and statements, managing scoping and variable binding, and implementing lowering passes between dialects.

> TODO: add hyperlinks to the files and/or methods referenced in this section

> TODO: explain that Coding Agents can speed-up the work as they already know Lean and most of the existing languages

### What are the prerequisites for building a Strata front-end (knowledge of Lean, understanding of IRs, etc.)?

Building a Strata front-end requires knowledge at several layers, though not all of it is needed upfront. The most fundamental prerequisite is understanding the Strata dialect you will target (e.g. Laurel). You need to understand its intermediate representation, its type system, its AST and its procedure model (e.g. Procedure with inputs, outputs, preconditions, and a body). This is the target you're translating into, so fluency with it is non-negotiable. You also need a working understanding of Lean 4 syntax — not deep theorem-proving expertise, but enough to write pattern-matching functions, work with monadic error handling (`Except`), and navigate inductive types. The Python front-end's `PythonToLaurel.lean` is a good example: it's essentially a large match over the source AST constructors, recursively building Laurel `StmtExprMd` nodes, and you need to be comfortable reading and writing that style of code. For instance, every translation function follows the same pattern of matching a source construct and assembling Laurel nodes with metadata wrappers like `mkStmtExprMd (StmtExpr.PrimitiveOp Operation.Add [leftExpr, rightExpr])`.

Beyond the IR and Lean, you need to understand Strata's Dialect Definition Mechanism (DDM) — how a dialect defines syntactic categories and operations, how those get serialized to Ion, and how `#load_dialect` / `#strata_gen` auto-generates Lean types from the dialect file. The Python front-end demonstrates this well: `pythonast.py` introspects Python's `ast` module to programmatically generate a DDM dialect via calls like `PythonAST.add_syncat("expr")` and `PythonAST.add_op("Name", ...)`, then the `Parser` class walks the native AST and emits DDM `Operation` nodes. You need to understand this pipeline — source language AST → DDM operations → Ion serialization → Lean-side typed AST — because it determines how your parser and translator connect. Finally, a conceptual understanding of verification condition generation is helpful but not strictly required for building the front-end itself: knowing that `Assert` nodes become proof obligations, that procedures with local variables become Core procedures (not callable from assertion contexts), and that loops require invariants for the SMT solver to reason about them, helps you make sound translation choices. You do not need to understand the SMT encoding or the Core VCG internals to get started.

### What is the API for constructing a dialect's AST programmatically?

The API for constructing a dialect's AST programmatically has two layers: dialect definition and program construction. Both are provided by the `strata.base` module for the Python Front-End.

At the **dialect definition layer**, you create a `Dialect` object and populate it with syntactic categories and operations. A syntactic category (`SynCatDecl`) groups related AST nodes — for example, the Python front-end creates categories for each Python AST base class. An operation (`OpDecl`) defines a concrete AST node with typed arguments and a result category. Arguments are declared with `ArgDecl`, which pairs a name with a kind — either a reference to a syntactic category, or a built-in kind from `Init` (`Init.Str()`, `Init.Num()`, `Init.Seq(cat)`, `Init.Option(cat)`). The Python front-end's `gen_dialect()` shows this concretely: it calls `PythonAST.add_syncat("expr")` to create the expression category, then `PythonAST.add_op("ConPos", ArgDecl("v", Init.Num()), PythonAST.constant())` to define a positive-constant node with a numeric argument producing a constant. The last positional argument to `add_op` is always the result category. Once defined, `OpDecl` objects are callable — e.g. `PythonAST.ConPos(NumLit(42))` constructs an `Operation` node. The dialect is serialized to Ion via `Dialect.to_ion()` and can be round-tripped back with `Dialect.from_ion()`.

At the **program construction layer**, you walk the source language's native AST and emit `Operation` nodes by calling the `OpDecl` objects from the dialect. The key value types are `NumLit` (non-negative integers), `StrLit` (strings), `Ident` (identifiers), `OptionArg` (optional values — `OptionArg(None)` or `OptionArg(inner)`), and `Seq` (sequences — `Seq(tuple(...))`). Every node can carry a `SourceRange(offset, end_offset)` via the `ann=` keyword argument, which propagates byte offsets through to verification error messages. The Python parser's `ast_to_arg` method is the canonical example of this dispatch: it matches on the syntactic category's name and converts Python values to the appropriate DDM argument type — `int` becomes `IntPos`/`IntNeg`, `str` becomes `StrLit`, `bool` becomes `ConTrue`/`ConFalse`, `None` becomes `OptionArg(None)`, `list` becomes `Seq`, etc. The final result is a `Program` object (created via `strata.Program(dialect)`) to which you add the top-level `Operation` with `p.add(op)`, and then serialize with `p.write(output_path)`.

### How do I handle scoping and variable binding?

Scoping and variable binding in a Strata front-end are handled entirely at the translator level — neither the DDM dialect nor the Laurel IR has a built-in notion of scope. Instead, the translator threads a type environment through the recursive AST walk, and Laurel's `LocalVariable` construct implicitly introduces bindings that the downstream Core translator resolves. The key pattern is that `translateStmt` returns an updated environment alongside the translated Laurel node. In the Python front-end, this is `TranslationContext` with a `variableTypes : List (String × HighTypeMd)` field — when an annotated assignment like `x: int = 5` is encountered, the translator appends `(varName, varType)` to the context and returns the new context alongside the `LocalVariable` node.

The critical design choice is that Laurel itself uses flat name-based binding — `LocalVariable "x" TInt (some init)` introduces `x` into the enclosing block, and `Identifier "x"` references it by name. There are no de Bruijn indices or explicit scope markers at the Laurel level. This means scoping is lexical-by-convention: a variable declared inside a block is visible to subsequent statements in that block because the environment is threaded forward through the `foldl` over the block's statements, but it doesn't leak out. The front-end developer doesn't need to implement any scope resolution machinery — just thread the environment correctly and emit `LocalVariable` / `Identifier` nodes with consistent names.

### What utilities does Strata provide for AST manipulation and transformation?

Strata provides utilities at three distinct levels: the DDM layer for dialect-level AST construction and serialization, the Laurel layer for IR-level analysis and transformation, and the Core layer for verification-oriented program transformations.

**DDM level:** The main utility is the `base` module (see for example Python's `strata.base`), which provides the `Dialect`, `OpDecl`, `SynCatDecl`, and `Operation` classes for programmatically defining and constructing ASTs. On the Lean side, the `#load_dialect` and `#strata_gen` macros in `Strata/DDM/Elab/` auto-generate typed Lean inductive types from a dialect's Ion file — so for example once you define `WhileStmt(cond: expr, body: stmt)` in your dialect, you get a Lean constructor you can pattern-match on. The `Strata/DDM/Ion.lean` module handles Ion serialization and deserialization, and `Strata/DDM/AST.lean` provides the generic AST representation that all dialects share. The `Strata/DDM/Util/` directory contains low-level helpers: `SourceRange` for byte-offset tracking, `StringGen` for fresh name generation, `LabelGen` for unique label creation, and various `List`, `Array`, `Map` utilities.

**Laurel level:** Strata provides several Laurel-to-Laurel transformation passes that run before Core translation and can serve as examples for performing AST manipulation. `LaurelTypes.lean` provides `computeExprType`, which computes the `HighType` of any `StmtExprMd` given a type environment — this is used by both front-ends for operator dispatch (e.g., deciding whether `+` means `Add` or `StrConcat` based on operand types). `LaurelFormat.lean` provides pretty-printing (`formatStmtExpr`, `formatHighType`) for debugging. `LiftExpressionAssignments.lean` is a Laurel → Laurel pass that hoists assignments out of expression contexts into preceding statements — for example, transforming `var y := x + (x := 1)` into a sequence of snapshots and assignments. `HeapParameterization.lean` is another Laurel → Laurel pass that analyzes which procedures read or write the heap (via `FieldSelect`, `New`, field assignments) and adds explicit heap parameters. These passes compose in a pipeline: the `LaurelToCoreTranslator` calls them before translating to Core, and they operate on the same `StmtExprMd` / `Program` types that the front-end translator produces.

**Core level:** `Strata/Transform/` provides program-to-program transformations on the Imperative dialect's `Stmt` type. `LoopElim.lean` replaces loops with invariant checks, havocs, and guard assumptions — essential for SMT-based verification since the solver can't reason about unbounded iteration. `CallElim.lean` replaces procedure calls with their contracts (assert precondition, havoc outputs, assume postcondition), enabling modular verification. A front-end developer doesn't typically write new Core transforms, but understanding that they exist — and that the pipeline applies them automatically — is important for knowing what the front-end's output needs to look like (e.g., loops need invariants because `LoopElim` will consume them, and procedure calls need contracts because `CallElim` will inline them).

### How do I implement lowering passes between Strata dialects?

A lowering pass between Strata dialects is a recursive function that pattern-matches on the source AST and constructs target AST nodes. There is no framework or base class to inherit from — you write a set of mutually recursive functions, one per syntactic category (expressions, statements, types), that take a source node and return a target node. The two canonical examples are the source-to-Laurel translators (like `PythonToLaurel.lean`) and the `LaurelToCoreTranslator.lean`. Both follow the same structure: a `translateExpr` function that maps source expressions to target expressions, a `translateStmt` function that maps source statements to target statements, a `translateType` function for types, and a top-level `translateProcedure` / `translateFunction` that assembles the pieces into the target's procedure representation.

The Laurel-to-Core translator (`LaurelToCoreTranslator.lean`) demonstrates the more complex case where the source and target have fundamentally different representations. Laurel uses a unified `StmtExpr` type for both expressions and statements, while Core separates them into `Core.Expression.Expr` (a locally-nameless lambda calculus with de Bruijn indices) and `Core.Statement` (an imperative command language). So the translator has two entry points: `translateExpr` for expression contexts (producing `Core.Expression.Expr`) and `translateStmt` for statement contexts (producing `TypeEnv × List Core.Statement`). The expression translator must handle the de Bruijn encoding. The statement translator handles the split between Core functions and procedures: a `StaticCall` in expression position becomes nested `.app` applications, while in statement position it becomes `Core.Statement.call`. The translator also runs Laurel-to-Laurel passes before lowering — `LiftExpressionAssignments` hoists assignments out of expressions, `HeapParameterization` adds explicit heap threading, and `ModifiesClauses` generates frame conditions — by calling them on the Laurel `Program` before invoking `translateProcedure` on each procedure. This pipeline composition is done in the top-level `translateProgram` function, which collects union/tuple types to generate Core datatype declarations, runs the Laurel passes, classifies procedures as functions vs. procedures, and then translates each one. A new lowering pass follows the same recipe: define your recursive translators, thread the environment, and wire them into the pipeline at the appropriate point.

---

## Validation & Testing

### How do I validate that my front-end preserves source language semantics?

To validate that your front-end preserves source language semantics, the recommended approach is differential testing with an executable intermediate representation. Build a testing framework that compiles the same program twice: once using the standard language compiler (like `javac` for Java or CPython for Python) and once through your Strata front-end. Execute both versions and compare their outputs for equivalence. If the outputs match, your translation correctly preserves the source language semantics. This approach provides independent validation of your front-end without requiring full end-to-end verification workflows, making debugging significantly easier when issues arise. Most Strata dialects have well-defined executable semantics. You can reuse the execution engine of your target dialect to build the differential testing infrastructure.

### What code coverage targets should I aim for?

When building a new Strata front-end, you should aim for at least 80% feature-level coverage of the language features you intend to support. This means tracking not just the percentage of tests that pass, but specifically which language constructs and features are validated by your passing tests. Feature-level coverage ensures you are systematically testing critical language capabilities like lambdas, generics, polymorphism, exception handling, and concurrency primitives rather than just accumulating test counts. Map each test case to the specific language features it exercises, allowing you to identify gaps where certain features remain untested and prioritize improvements accordingly.

Beyond feature coverage, track your test pass rate as a complementary metric that measures overall translation correctness. The framework should maintain both metrics over time, enabling you to monitor progress and detect regressions. For languages with comprehensive conformance test suites (like Python's CPython tests, or TypeScript's ECMAScript Test Suite), these official suites provide excellent baseline coverage targets since they're designed to validate complete language specification compliance. Start with these established test collections rather than building from scratch, as they represent the same standards used by the language maintainers themselves.

### How do I debug translation issues?

Implement detailed logging throughout your translation pipeline to facilitate systematic debugging. Your framework should capture intermediate representations at key transformation points—the parsed abstract syntax tree from the source language, the generated Strata IR, and execution traces from both the reference compiler path and your Strata path. When a differential test fails, these logs allow you to pinpoint exactly where the translation diverged by comparing intermediate states. Additionally, maintain a coverage tracking system that maps test outcomes to specific language features over time, creating an audit trail that shows which features consistently pass, which fail, and which remain untested. Log execution metadata like timeout occurrences, crashes, or infinite loops when running on large real-world codebases, as these robustness issues often reveal edge cases that small unit tests miss.

---

## Best Practices

This section distills lessons learned from existing Strata front-end implementations into actionable guidance. It describes how to structure your codebase for maintainability, optimize translation performance, and contribute back to the Strata ecosystem.

### What are performance considerations for the translation process?

Some considerations include:

- If your dialect has nested or recursive structures (e.g., nested pattern matching, comprehensions), flatten them early. Deeply nested translations produce deeply nested verification conditions that are harder for SMT solvers.

- Core uses a flat variable namespace. If your high-level dialect has lexical scoping, shadowing, or closures, you need a renaming strategy. Generating fresh names naively (e.g., appending counters) is fine for correctness but can produce huge variable sets that slow down SMT encoding.

- The biggest performance bottleneck is usually the SMT solver. Transformations that produce smaller, more modular verification conditions (VCs) win.

- Prefer generating multiple smaller procedures with tight contracts over one monolithic procedure. The `CallElim` transformation replaces calls with `assert pre; havoc; assume post`, which is much cheaper than inlining entire bodies.

- If your dialect has features that map to quantifiers (e.g., `forall x in collection`), be careful — quantifiers are expensive for SMT solvers. Use triggers where possible (Lambda expressions support quantifiers with triggers) but also consider whether an encoding that does not use quantifiers is possible.

- The order you compose transformations matters. For example, if your dialect has both loops and procedure calls, translating to Core first and then running `CallElim` → `LoopElim` is the standard pipeline. But if your high-level construct can be desugared to avoid loops entirely (e.g., bounded iteration → unrolling), doing that before hitting Core avoids the need for loop invariants.

- Core's `Map` type uses Select/Store axioms, which are well-supported by SMT but can be expensive with many updates. If your dialect has data structures that map to nested maps (e.g., objects with fields that are themselves maps), the encoding can explode. Consider flattening where possible.

- Core supports polymorphic types, but SMT-LIB has limited polymorphism support. The SMT encoder must monomorphize or use sort encodings. If your dialect introduces many generic types, the encoding overhead grows. Prefer concrete types where the high-level semantics allow it.

- Profile with actual examples early. A transformation that looks clean structurally can still produce VCs that time out on the solver.

### How should I structure my front-end codebase?

Add each new dialect under `Strata/Languages/YourDialect/`. The existing dialects follow a consistent pattern, with the following categories of files:

1. **Root module file (`YourDialect.lean`)** — Re-exports everything. This is the entry point. Keep it minimal, just imports.

2. **Grammar / Parsing (`DDMTransform/`)** — Every dialect that parses `.st` files has this subdirectory:
   - `Grammar.lean` (preferred) or `Parse.lean` — DDM grammar definition (concrete syntax tree)
   - `Translate.lean` or `ASTtoCST.lean` — CST-to-AST translation
   - Optionally a `.st` grammar file (like Laurel's `LaurelGrammar.st`)

3. **AST and type definitions** — The core data structures of your dialect. Look at how C_Simp defines its expression/statement types by reusing the Lambda and Imperative expression and statement types:
   - Define type aliases for expressions using `Lambda.LExpr` or Core expressions
   - Define commands and statements using `Imperative.Stmt`/`Imperative.Cmd`
   - Add dialect-specific constructs (like Laurel's `Identifier`, `Operation`, `TypeHierarchy`)

4. **Translation to a lower dialect** — The key file. This could translate directly to Core, or go through an intermediate dialect such as Laurel.

5. **Dialect-specific passes** — You may want to do pre-translation transformations on your own AST. Laurel is the best example here with multiple passes:
   - `Resolution.lean` — Name resolution
   - `DesugarShortCircuit.lean` — Desugar complex expressions
   - `LiftImperativeExpressions.lean` — Normalize expressions
   - `HeapParameterization.lean` — Heap modeling
   - `EliminateHoles.lean`, `InferHoleTypes.lean` — Type inference

6. **Analysis entry point (such as verification)** — Orchestrates a full pipeline: parse → transform → translate → analyze.

Add a mirrored test structure under `StrataTest/Languages/YourDialect/`:
- Unit test `.lean` files at the top level
- `examples/` or `tests/` subdirectory for `.st` test programs
- `expected_*/` directories for golden-file testing if needed

Don't reinvent expression or statement representations. C_Simp shows an example of this. Your dialect should parameterize over these existing building blocks when possible and only add what's genuinely new.

### How do I contribute my front-end back to the Strata ecosystem?

> TODO: mention that dialects can be independent or part of the official Strata codebase

> TODO: mention that for a new FE to be within the strata.org repo, we need a quality bar and a path towards the quality bar for FE officially maintained by AWS.

### How do I ask for Strata features for my front-end and what support can I expect from Strata maintainers?

> TODO: if feature is interesting for multiple languages, it will be considered and prioritized. If not, we can help by reviewing PR...
