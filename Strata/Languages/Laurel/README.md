# Laurel

Laurel is an intermediate verification language that provides features common to
Java, Python, and JavaScript. This folder implements Laurel and its lowering to
Strata Core.

## Documentation

Laurel is documented by three guides. Each is a
[Verso](../../../docs/verso/README.md) document under
[`docs/verso/`](../../../docs/verso); the published HTML is linked below.

- **[User Guide](../../../docs/verso/LaurelUserGuide.lean)**
  ([published](https://strata-org.github.io/Strata/laurelguide/html-multi/)) — a
  task-oriented guide to writing Laurel specifications: assertions, loop
  invariants, pre- and postconditions, quantifiers, objects, modifies clauses,
  and `old`.

- **[Designer Guide](../../../docs/verso/LaurelDesignGuide.lean)**
  ([published](https://strata-org.github.io/Strata/laureldesign/html-multi/)) —
  how the Laurel language is defined: its types, unified expression/statement
  model, procedures, programs, and type checking.

- **[Implementor Guide](../../../docs/verso/LaurelImplementationGuide.lean)**
  ([published](https://strata-org.github.io/Strata/laurelimpl/html-multi/)) —
  how a checked Laurel program is lowered to Strata Core: the translation
  pipeline, its passes and their ordering, and the differences between Laurel and
  Core.

To build and preview the guides locally, see
[`docs/verso/README.md`](../../../docs/verso/README.md) (or run `make laurelguide`,
`make laureldesign`, `make laurelimpl` from `docs/verso/`).

The full pass list and exact ordering live in
[`LaurelCompilationPipeline.lean`](LaurelCompilationPipeline.lean)
(`laurelPipeline`); end-to-end tests are under
[`StrataTest/Languages/Laurel/EndToEndTests/`](../../../StrataTest/Languages/Laurel).
