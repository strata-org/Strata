# BoogieToStrata Status

Snapshot of what works and what's open in the Boogie → Strata Core
translator. For ongoing work, the GitHub issue tracker is authoritative.

## Shipped

- **CFG emission for procedures with gotos.** Procedures containing any
  `goto` are emitted using Strata Core's native `cfg` syntax (entry block
  + labeled blocks + transfers). 1-target gotos become `goto L;`,
  2-target gotos become `goto L1, L2;` (nondet), 3+ targets are chained
  through synthetic `__nondet_N` blocks. Procedures without gotos continue
  to use the structured path unchanged.
- **CFG procedure locals.** Local variables for CFG procedures are emitted
  in a `locals` block bound by the `command_cfg_procedure` grammar rule,
  visible across all CFG blocks via `@[scope(locals)]`.
- **Name-collision fixes.** A global name set keyed by entity-type prefix
  prevents Boogie symbols from sharing the same Strata identifier after
  sanitization. Covers global vars, function names, and procedure names.
- **Type-synonym chain resolution.** The DDM translator now resolves
  transitive type synonyms (e.g. `ref := i64 := int`), so comparison
  operators no longer panic.
- **SMACK `assert_` handling.** SMACK's `assert(...)` lowers to a call to
  `assert_.iN()`. BoogieToStrata recognizes this pattern and emits a
  Strata `assert` statement so the verifier generates VCs for it.
- **InferModifies.** When a Boogie procedure has no `modifies` clause,
  BoogieToStrata infers one from the procedure body. Required for SMACK
  output, which omits `modifies` everywhere.
- **`old(...)` expression rename consistency.** `old(x)` references use
  the same renamed identifier as the un-old version of `x`.
- **`--smack` CLI flag.** Gates SMACK-specific translation behavior:
  enables `InferModifies` and injects a `Requires` clause on calls to
  `assert_.<type>` so SMACK's `assert(...)` lowers verify against the
  asserted predicate. Off by default for non-SMACK Boogie.
- **`__VERIFIER_assume` `free ensures` synthesis.** Under `--smack`, a
  `free ensures (_i0 != 0)` is synthesized on `__VERIFIER_assume`
  declarations so callers of `assume(...)` carry the assumption through
  procedure-call elimination. Mirrors the `assert_` pattern with dual
  polarity.

## Test fixtures

- `Tools/BoogieToStrata/Tests/*.bpl` — small per-feature regression
  inputs, each paired with a `.expect` golden file.
- `Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`
  runs the translator against every `.bpl` in `Tests/` and diffs the
  output against `.expect`.

## Known issues

- [#1162](https://github.com/strata-org/Strata/issues/1162) — Type checker
  errored on nondet goto with undeclared `$__nondet_N`. Resolved on
  `htd/smack` by emitting an `init` command for the synthetic variable
  in `translateTransfer`; tracked here for cross-reference.
- [#1184](https://github.com/strata-org/Strata/issues/1184) — Multi
  out-parameter support for the CBMC backend.
- [#1185](https://github.com/strata-org/Strata/issues/1185) — Cross-
  procedure PE error contamination silently drops obligations.
  `--split-procs` in `run_pipeline.py` is the current workaround.

## Pipeline status

End-to-end results for the 25-program SMACK benchmark (12 original +
13 simplified AWS C Common functions, in
`Examples/smack-docker/programs/*.c`) are summarized in
`Examples/smack-docker/README.md`.
