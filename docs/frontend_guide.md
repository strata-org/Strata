# Strata Front-End Guide

This is the technical reference for building front-ends that translate source languages into Strata dialects. For hosting and governance decisions, see [Hosting & Governance](frontend_hosting.md). For testing and validation, see [Testing & Validation](frontend_testing.md).

## Executive Summary

This guide provides documentation for developers building new front ends to Strata. This document is intended for compiler engineers, programming language researchers, and verification tool developers who want to integrate their source languages with the Strata analysis ecosystem. Whether you're adding support for a new language (either a general purpose programming language, domain-specific language, or other formal notation), or extending an existing front-end, this guide will walk you through good architectural decisions, implementation patterns, and development practices.

## Why This Matters

Building a correct front-end is challenging. It requires a deep understanding of both your source language's semantics and the Strata IR you are targeting. Poor translation choices can lead to unsound verification results or make certain properties impossible to verify. This guide distills lessons learned from existing implementations to help you avoid common pitfalls and build robust, maintainable front ends.

## Getting Started

The guide consists of answers to several key questions, organized to support both linear reading and targeted references. New developers should start with the architecture overview and core translation concepts before diving into implementation details. Experienced developers can jump directly to specific sections addressing their immediate needs.

## Architecture & Design

### What are the main components of a Strata front-end?

A Strata front end parses text written in a source language and translates it to a representation in a Strata dialect. To do this, it needs several components:

- **A parser or compiler front-end for the source language.** We typically recommend that this be the standard parser for the source language, perhaps the one used by a standard production compiler, interpreter, or analyzer for that language, to ensure that it accurately captures the structure of all source programs of interest and can be maintained as easily as possible as the language evolves. For complex languages, leveraging an existing compiler's early passes (name resolution, type inference, desugaring) is recommended, as it avoids reconstructing these in Lean. This will often be implemented in the source language itself, or at the very least in a language different than Lean, the language used to implement Strata.

- **Data structures to represent the target Strata dialect (either an existing one like Laurel, or a new one you define for your source language).** Although it would be possible to traverse the AST of the source language and directly generate the textual or binary representation of a Strata dialect, doing so would involve complex code that is difficult to understand and audit. So, we recommend an AST-to-AST translation from the source language to a Strata dialect. AST representations for Strata dialects are available in Java, Lean, and Python, generated from a high-level dialect description. If your source language toolchain uses a different language, contact the Strata team to discuss adding support for it, or use the Ion serialization format directly. See the [Implementation Guide](#what-is-the-api-for-constructing-a-dialects-ast-programmatically) for details on the Dialect Definition Mechanism (DDM) that generates these ASTs.

- **Code to translate between the source language and the Strata dialect.** Given ASTs for both the source language and a Strata dialect, one component of the front end will need to traverse an instance of the former to produce an instance of the latter. This component is specific to each source language, and its complexity will depend on how different the chosen Strata dialect is from the source language. See the section on [choosing a target dialect](#what-are-the-existing-strata-dialects-which-strata-dialect-should-i-target) for guidance on this decision. It's possible for a Strata dialect to exactly mirror the structure of a source language, in which case this translation will be straightforward and mechanical (and possibly even auto-generated, as in the Python dialect described below). This is the recommended approach when feasible, as it keeps the external translation simple and moves the complexity of lowering the Strata dialect into verification friendly dialects like Strata Core into Lean where it can be shared and potentially verified.

- **A serializer for the Strata dialect.** Given that the parser and translator are likely written in a different language than Strata itself, it will usually be necessary to serialize the AST produced by the previous component to send it to the Strata implementation. The DDM automatically generates serializers (and deserializers) alongside the AST, so this component typically requires no manual implementation.

### What are examples of existing front ends (Python, Java) and their design decisions? What is the recommended translation pipeline (e.g., source language → high-level Strata → Core)?

Two of the existing Strata front ends, Java and Python, illustrate our two recommended approaches to front end development and the tradeoffs between them.

- **The Java front end** (TODO: link once source repo is public) is implemented as a plugin for the Java compiler. It works by running a few initial compiler stages to simplify the program and then translating the resulting, simpler Java code into the Laurel dialect. This dialect is a memory-safe imperative language intended to capture patterns that are common between languages such as Java, JavaScript, and Python. This choice makes the translation from Java to Laurel relatively straightforward but still non-trivial. It also allows a developer familiar with Java (and Laurel) to implement the translation even if they are not familiar with Lean.

- **The Python front end** is implemented as a client of the Python [`ast`](https://docs.python.org/3/library/ast.html) standard library module, which provides programmatic access to Python's abstract syntax tree. A pre-processing phase, which needs to be performed only once per Python version, traverses the structure of the AST provided by that library and auto-generates a Strata dialect corresponding to that version of Python. The front end proper then traverses the AST of an input program and performs the translation into the Python dialect and serializes the result to send to Strata. The core of this traversal is automatically generated from the mechanized description of the Python AST. The translation from the Python dialect into other Strata dialects (Laurel, in this case) occurs within Strata itself.

There is a tradeoff between these two approaches, so which one to choose depends on the specifics of an individual use case. In particular, it depends on the architecture of the source language compiler you are using and at it which point in the standard pipeline it is cleanest to inject a Strata front-end. However, in general, the approach of directly representing the source language in a dialect, as we do for Python, has several advantages:

- It makes it possible to define a semantics for the source language within Strata, which opens the possibility of proving that any further translations preserve the semantics of the original program.
- It makes it possible to implement the translation to further Strata dialects in Lean. Lean is a particularly nice language for writing translations, and a Lean implementation can share utility code with other translations.

However, it also has several disadvantages:

- It requires creating a dialect matching the source language, which can require substantial work if a machine-readable description for that language isn't readily available (as it is for Python).
- Writing further translations in Lean requires familiarity with Lean, which is likely a less widely known language than that used to implement some existing parser for the chosen source language.

### What are the existing Strata dialects? Which Strata dialect should I target?

Strata currently includes the following key dialects (see [`Strata/Languages/`](https://github.com/strata-org/Strata/tree/main/Strata/Languages) for the full list, though more can be added at any time):

- **[Python](https://github.com/strata-org/Strata/tree/main/Strata/Languages/Python).** This dialect directly represents the Python language. It is automatically generated from the Python `ast` module, so variations of it can exist for any Python version.

- **[Laurel](https://github.com/strata-org/Strata/tree/main/Strata/Languages/Laurel).** This dialect is intended to capture the common semantic structures that exist across several memory-safe, imperative, object-oriented languages including Java, JavaScript, and Python. These structures include the ability to nest operations with side effects within expressions and built-in support for heap-allocated objects with fields. If your language is imperative and object-oriented, Laurel is likely the right target.

- **[Core](https://github.com/strata-org/Strata/tree/main/Strata/Languages/Core).** This dialect is the primary analysis target in Strata — a simple, possibly nondeterministic, imperative language with a functional, higher-order expression language. It does not include built-in objects or heap reasoning. Most analyses are implemented by first translating into Strata Core and then to the representation naturally used by the analysis. It is slightly simpler than Laurel, as well as more general, being able to represent the semantics of artifacts written in a wider variety of languages using core constructs drawn from both functional and imperative programming. Unlike the first two dialects above, the Core dialect has formally specified semantics. If your language doesn't fit Laurel's object-oriented model, target Core.

- **[SMT](https://github.com/strata-org/Strata/tree/main/Strata/DL/SMT).** This dialect directly represents the SMT-LIB language (v2.7) used to communicate with SMT solvers. It is used by the deductive verification implementation in Strata to represent verification conditions. By including it as an explicit dialect, we make it possible to prove that Strata's verification condition generator is correct. Including it as a dialect has additional benefits, because the DDM automatically generates a parser for it which can be used to parse the responses from an SMT solver (such as complex models for satisfiable queries, which are left unhandled by many existing tools).

---

## Core Translation Concepts

### How do I map source language constructs to Strata dialect constructs?

The first step is to choose a target dialect. It's typically best to choose the highest-level dialect that still offers sufficient precision for your intended analyses, to make the mapping as simple as possible. Most Strata dialects have executable semantics, which enables differential testing of translations — this is an important consideration when choosing a target dialect (see [Validation & Testing](frontend_testing.md#how-do-i-validate-that-my-front-end-preserves-source-language-semantics)). Next, many of the steps required to perform a semantics-preserving transformation from the constructs available in a typical source language into the fewer but more general constructs in a Strata dialect follow the same patterns used in compilers. A book like *Modern Compiler Implementation*, especially the chapter on translation to IRs, can be helpful background.

### What are the semantics preservation requirements when translating to Strata?

Strata is intended to allow multiple analyses to be implemented for multiple source languages without requiring excessive duplication of effort. For this to be effective, a front end must capture the semantics of the original source as accurately as possible, so that whatever details an analysis might need are guaranteed to be available. Although the exact details of "as accurately as possible" depend on what details of each language are included in a formal semantics, a general rule of thumb would be to treat a Strata front end more like you would when implementing a compiler than you might when, say, implementing a narrowly-targeted static analysis tool. Strata aims to make its intermediate representations executable, which means translations should preserve enough detail for both analysis and execution — more than a typical compiler optimization pass would retain, but with the same attention to semantic fidelity.

### How should I handle metadata propagation?

Preserving metadata — especially source code locations — across translations is critical for a good verification and analysis experience. When a verification condition fails or an analysis reports a finding, the user needs to trace it back to the original source code. Strata AST nodes can carry `SourceRange(offset, end_offset)` annotations that propagate byte offsets from the source file through to error messages. Every translation step should map source locations from the input AST to the output AST so that downstream tools can report meaningful diagnostics. Beyond source locations, metadata can also carry invariants, type information, or other annotations that backend analyses may need to interpret.

### How do I represent contracts, invariants, and verification objectives in Strata?

The dialects that support imperative programming constructs (such as Laurel and Core) include, at the very least, assumption and assertion statements. In principle, any verification objectives can be represented using these alone. However, Laurel and Core both also include built-in notions of contracts that can be directly targeted. Both languages allow preconditions and postconditions on procedures and invariants on loops. While assertion and assumption statements are sufficient for expressing verification objectives, using contracts is strongly recommended for modular verification and meaningful error reporting.

If you're targeting a dialect that does not directly include such constructs, it's still possible to attach arbitrary expressions as metadata to Strata AST nodes, though backend analyses will typically need to be updated slightly to interpret this metadata.

---

## Implementation Guide

This section provides guidance for writing code that constructs and manipulates the AST for a Strata dialect. This includes the APIs for building types, expressions, and statements, managing scoping and variable binding, and implementing lowering passes between dialects. Throughout this section, we use the Python front-end as a running example. Its external tooling (parser, dialect generator, serializer) lives in [`Tools/Python/strata/`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/), and its Lean-side translators live in [`Strata/Languages/Python/`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/) (with tests in [`StrataTest/Languages/Python/`](https://github.com/strata-org/Strata/blob/main/StrataTest/Languages/Python/)).

Note: AI coding agents (e.g. Amazon Kiro) can significantly accelerate front-end development. They are already proficient in Lean 4 and most common source languages, and can help with writing translation functions, generating boilerplate, and navigating the Strata codebase. Consider using one throughout the process.

### What are the prerequisites for building a Strata front-end (knowledge of Lean, understanding of IRs, etc.)?

Building a Strata front-end requires knowledge at several layers, though not all of it is needed upfront:

- **Understanding your target dialect** (e.g. Laurel). You need to understand its intermediate representation, its type system, its AST, and its procedure model.

- **Working knowledge of Lean 4 syntax.** Not deep theorem-proving expertise, but enough to write pattern-matching functions, work with monadic error handling (`Except`), and navigate inductive types. The Python front-end's [`PythonToLaurel.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/PythonToLaurel.lean) is a good example: it's essentially a large match over the source AST constructors, recursively building Laurel `StmtExprMd`.

- **Understanding the DDM pipeline.** How a dialect defines syntactic categories and operations, how those get serialized to Ion, and how `#load_dialect` / `#strata_gen` (in [`Strata/DDM/Integration/Lean/`](https://github.com/strata-org/Strata/blob/main/Strata/DDM/Integration/Lean/)) auto-generate Lean types from dialect files. You don't need to understand the DDM internals deeply — just enough to use the generated types in your translator. The Python front-end demonstrates this well: [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) introspects Python's `ast` module to programmatically generate a DDM dialect via calls like `PythonAST.add_syncat("expr")` and `PythonAST.add_op("IntPos", ...)`, then the `Parser` class walks the native AST and emits DDM `Operation` nodes.

- **Conceptual understanding of the analyses you intend to perform** (helpful but not strictly required, and only to the extent that you intend to verify or analyze programs in the language you're adding). Knowing that `Assert` nodes become proof obligations, that loops require invariants for an SMT solver to reason about them, and that procedures need contracts helps you make sound translation choices. You do not need to understand the SMT encoding or the Core VCG internals to get started.

### What is the API for constructing a dialect's AST programmatically?

The API has two layers: dialect definition and program construction. Both are provided by the `strata.base` Python module (see [`Tools/Python/strata/base.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/base.py)).

**Step 1: Define a dialect.** Create a `Dialect` object and populate it with syntactic categories (`SynCatDecl`) and operations (`OpDecl`). A syntactic category groups related AST nodes (e.g., one per Python AST base class). An operation defines a concrete AST node with typed arguments and a result category.

**Step 2: Define syntactic categories and operations.** The Python front-end's `gen_dialect()` in [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) shows this concretely: it calls `PythonAST.add_syncat("expr")` to create the expression category, then `PythonAST.add_op("IntPos", ArgDecl("v", Init.Num()), PythonAST.int())` to define a positive-integer node. Once defined, `OpDecl` objects are callable — e.g. `PythonAST.IntPos(NumLit(42))` constructs an `Operation` node. The dialect is serialized to Ion via `Dialect.to_ion()`.

**Step 3: Construct program AST nodes.** Walk the source language's native AST and emit `Operation` nodes. The key value types are `NumLit`, `StrLit`, `Ident`, `OptionArg`, and `Seq`. Every node can carry a `SourceRange(offset, end_offset)` via the `ann=` keyword argument, which propagates byte offsets through to verification error messages. The Python parser's `ast_to_arg` method in [`pythonast.py`](https://github.com/strata-org/Strata/blob/main/Tools/Python/strata/pythonast.py) is the canonical example of this dispatch.

**Step 4: Serialize.** The final result is a `Program` object to which you add the top-level `Operation` with `p.add(op)`, and then serialize with `p.write(output_path)`.

### How do I implement lowering passes between Strata dialects?

A lowering pass is a set of mutually recursive functions that pattern-match on the source AST and construct target AST nodes. There is no framework or base class to inherit from. The two canonical examples are:

- **Source-to-Laurel translators** (like [`PythonToLaurel.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Python/PythonToLaurel.lean)): a `translateExpr` for expressions, a `translateStmt` for statements, a `translateType` for types, and a top-level `translateProcedure` that assembles the pieces.

- **[`LaurelToCoreTranslator.lean`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LaurelToCoreTranslator.lean)**: the more complex case where source and target have fundamentally different representations. Laurel uses a unified `StmtExpr` type, while Core separates expressions (`Core.Expression.Expr` with de Bruijn indices) from statements (`Core.Statement`). The translator has `translateExpr` and `translateStmt` entry points, handles the split between Core functions and procedures, and runs Laurel-to-Laurel passes ([`LiftImperativeExpressions`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/LiftImperativeExpressions.lean), [`HeapParameterization`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/HeapParameterization.lean), [`ModifiesClauses`](https://github.com/strata-org/Strata/blob/main/Strata/Languages/Laurel/ModifiesClauses.lean)) before lowering.

A new lowering pass follows the same recipe: define your recursive translators, thread the environment, and wire them into the pipeline at the appropriate point.

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
