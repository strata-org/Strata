# Building Front-Ends for Strata

This guide provides documentation for developers building new front ends to Strata. It is intended for compiler engineers, programming language researchers, and verification tool developers who want to integrate their source languages with the Strata analysis ecosystem. Whether you're adding support for a new language (either a general purpose programming language, domain-specific language, or other formal notation), or extending an existing front-end, these documents will walk you through good architectural decisions, implementation patterns, and development practices.

## Documents

- **[Quick Start Tutorial](frontend_quickstart.md)** — Build your first front-end in 30 minutes: define a toy language, translate it to Laurel, and verify contracts end-to-end.

- **[Front-End Guide](frontend_guide.md)** — Architecture, dialect selection, core translation concepts (semantics preservation, metadata propagation, contracts), and implementation reference (prerequisites, DDM API, lowering passes, AST utilities, scoping).

- **[Hosting & Governance](frontend_hosting.md)** — Where to host your front-end code (inside the Strata repo, in the `strata-org` org, or independently), codebase structure conventions, and how to request features from the Strata team.

- **[Testing & Validation](frontend_testing.md)** — Differential testing for semantic correctness, feature-level coverage targets, debugging translation issues, and how translation choices affect downstream verification performance.

## Quick orientation

A Strata front-end parses a source language and translates it into a Strata dialect. The key decisions are:

1. **Which dialect to target** — Laurel for imperative/OO languages, Core for everything else. See [dialect selection](frontend_guide.md#what-are-the-existing-strata-dialects-which-strata-dialect-should-i-target).
2. **How to structure the translation** — Reuse the source language's reference compiler where possible, mirror the source AST in a Strata dialect, and let Lean handle the lowering. See [architecture](frontend_guide.md#what-are-the-main-components-of-a-strata-front-end).
3. **Where to host the code** — Start in your own repo, move to the official repo when mature. See [hosting options](frontend_hosting.md#where-should-my-front-end-code-be-hosted).
4. **How to validate correctness** — Differential testing against the source language's reference implementation. See [validation](frontend_testing.md#how-do-i-validate-that-my-front-end-preserves-source-language-semantics).
