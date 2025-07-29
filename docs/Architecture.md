# Strata Architecture

## Overview

Strata is an extensible language and analysis definition environment intended to describe the semantics of programs, specifications, protocols, architectures, and other aspects of large-scale distributed systems and their components.

Strata achieves this broad scope by defining an extensible set of orthogonal *dialects* (inspired by the [same concept in MLIR](https://mlir.llvm.org/docs/DefiningDialects/)) and allowing them to be extended and combined to achieve the purposes of specific use cases. The core dialects included in Strata are intended to be small, simple building blocks that, when appropriately combined and extended, can allow most existing languages to be modeled with high fidelity and without substantial loss of abstraction.

Strata is implemented in Lean to enable both verification of its own implementation as well as, in the long term, to enable the use of Lean to reason about programs written in Strata itself. However, we aim for the general structure of the various Strata dialects and languages, as well as the majority of its implementations, to be such that replicating them in other languages is straightforward. To accelerate the development of tools in a variety of languages, Strata can  automatically generate dialect-specific ASTs, serializers, and deserializers.

In the short term, Strata intends to support deductive verification with largely the same capabilities as the Boogie Intermediate Verification Language. In the longer term, we aim for Strata to be useful for most, if not all, program and specification analysis use cases.

## Dialect Definition Mechanism

Dialects are intended to be the building blocks for complete languages. As such, each typically contains a small number of constructs, and sometimes as little as a single construct.

Each dialect has a concrete syntax and a simple type system. The Dialect Definition Manager (DDM), in the [`Strata.DDM`](../Strata/DDM/) namespace, provides an embedded DSL within Lean to define the syntax and typing rules, which then produces a parser and preliminary type checker that can be used for processing either snippets embedded in a Lean source file or text read from external files.

The result of processing text written in a specific dialect is a generic and very flexible AST that captures all of the constructs possible in Strata. This representation allows flexibility, but is not particularly well-suited to concise traversals and transformations. Therefore, each dialect may have either an auto-generated or a hand-written Lean AST, as well, and a transformation from the generic syntax into dialect-specialized syntax.

## Dialect Composition and Transformation

In the current implementation of Strata, composition of dialects can occur in two places:

* In the definition of the syntax of a dialect in the DDM, one dialect can be imported into another, using the `open` directive at the top of a dialect definition, and the syntactic categories of the imported dialect can then be used in the dialect being defined.
* In the context of analysis, the hand-written ASTs for the current dialects have been implemented with an eye toward generality. Each of them is highly parameterized, allowing a variety of combinations. Expressions are parametric in the type of identifiers and the set of built-in functions. Commands and statements are parameterized by the type of expressions, and statements are parameterized by the type of commands.

Transformations (located in [`Strata.Transform`](../Strata/Transform/)) are a central part of the Strata infrastructure. The semantics of some dialects are canonically defined in terms of reduction into other dialects. For other dialects, transformation of constructs from one form to another can make certain analyses more straightforward. For example, some analyses work better on structured programs and some are easier to implement on unstructured programs. Or some analyses might work best with imperative assignments preserved, while some forms of verification condition generation work better on “passive” programs consisting of only assertions and assumptions.

## Dialect Library

Strata includes several generic dialects that allow it to represent the semantics of a variety of common programming languages. These dialects are currently sufficient to represent the constructs available in Boogie, and allow some flexibility beyond what Boogie provides, as well. These dialects are located in the [`Strata.DL`](../Strata/DL/) namespace.

### Lambda

The `Lambda` dialect ([`Strata.DL.Lambda`](../Strata/DL/Lambda/)) is intended to represent pure expressions of the sort that appear in essentially every programming or specification language. This dialect is parameterized by a set of built-in functions, allowing many first-order and higher-order expression languages as specific instantiations.

### Imperative

The `Imperative` dialect ([`Strata.DL.Imperative`](../Strata/DL/Imperative/)) is intended to represent imperative statements of the sort that appear in most programming languages. It is built of commands, which execute atomically, and currently has two mechanisms for combining commands:

* deterministic structured statements (if and while statements with explicit conditions), 
* non-deterministic structured statements (choice and repetition, with conditions encoded using assumptions), 

### Loopy

The `Loopy` dialect ([`Strata.DL.Imperative.Loopy`](../Strata/DL/Imperative/Loopy.lean)) extends the `Imperative` dialect with non-nested loops. It introduces introduces `LoopOrStmt`:

```
inductive LoopOrStmt : Type where
  | loop (guard: DefaultPureExpr.Expr) (body: Block DefaultPureExpr Command) (measure: Option DefaultPureExpr.Expr) (invariant: Option DefaultPureExpr.Expr)
  | stmt (s : Stmt DefaultPureExpr Command)
```

Both the measure and the invariant are currently optional to allow you to implement automatic measure/invariant generation.

### Boogie

The Boogie dialect ([`Strata.Languages.Boogie`](../Strata/Languages/Boogie/)) is intended to roughly mirror the capabilities of the [Boogie Intermediate Verification Language](https://github.com/boogie-org/boogie). As its foundation, it uses the `Imperative` dialect parameterized by the `Lambda` dialect. It specializes these dialects in several ways:

* It defines a type of identifiers that include scoping information, which is a parameter to `Lambda`.
* It introduces data types to represent procedures with contracts.
* It extends the language of commands from the `Imperative` dialect to include procedure calls, and uses this extended set of commands as a parameter to the various statement types.

It currently provides the following features:

* Declaration of abstract types and type synonyms.
* Declaration of axioms.
* Declaration of global constants and variables.
* Built-in types for Booleans, unbounded integers, and maps.
* Built-in operators and functions roughly mirroring what is available in SMT-Lib for the supported types.
* Declaration and optionally definition of pure functions
* Declaration and optionally definition of procedures with local variables, multiple outputs, preconditions, postconditions, and frame conditions.

The `Imperative` dialect also includes a verification condition generator (VCG) based on partial evaluation that produces a proof obligation for each assertion that appears in a statement or list of statements. It currently produces expressions in the `Lambda` dialect, but could be generalized as it depends only on the `.ite` expression constructor, which could equivalently be Boolean negation.

### CSimp

The CSimp dialect ([`Strata.Languages.C_Simp`](../Strata//Languages/C_Simp/) is a vaguely C-like language intended to show how to model common programming language constructs in Strata. There are many examples in `C_Simp/Examples`. CSimp builds on the `Loopy` dialect parameterized by the `Lambda` dialect.

`C_Simp/Verify.lean` demonstrates verification via transformation to Boogie. A loop elimination pass is first run to transform loops into the appropriate `assume` and `assert` commands, and then Boogie’s VCG, described above, is used to verify the program.

## Analysis

Our intent is that analysis implementations in Strata become highly reusable by building on two factors: the parametric and orthogonal nature of the core dialects, and the central focus on transformation. This allows two forms of reuse:

* An analysis can be defined over, for instance, imperative control flow graphs, while being generic over the types of commands and expressions that may appear in them, other than requiring that certain operations exist on them. This allows it to straightforwardly be applied to various instantiations of that type.
* An analysis can be defined on one dialect, and transformations can move from other dialects into that one. This allows a single analysis implementation to be applied to multiple languages.

The current Strata implementation includes only one analysis: the Boogie dialect VCG. However, you can add your own analyses on top of the existing dialects. The Imperative dialect includes an inductively-defined small-step operational semantics that can be used as a basis for verifying the correctness of analyses.

## External Reasoning Tools

Strata was designed to be used with external reasoning tools such as SMT solvers, CHC solvers, abstract interpretation engines, model checkers, and others. Currently, the VCG for the Boogie language based on partial evaluation along with an interface to SMT solvers (in [`Strata.DL.SMT`](../Strata/DL/SMT/)).

## Third-Party Dialects and Analyses

We encourage you to create your own dialects to smoothly support specific use cases. In some cases, new dialects may be of general interest. In others, they may be only of interest to those within a specific organization, or include information that is internal to an organization. To support dialects of both types, Strata makes it possible to construct a new dialect entirely as a client of the core Strata libraries, without changes to the core library code. This structure is transitive, so a client that creates a new dialect can subsequently become a dependency of a second client that uses that dialect to create a larger language.
