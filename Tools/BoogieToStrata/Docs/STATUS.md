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

## Test fixtures

- `Tools/BoogieToStrata/Tests/*.bpl` — small per-feature regression
  inputs, each paired with a `.expect` golden file.
- `Tools/BoogieToStrata/IntegrationTests/BoogieToStrataIntegrationTests.cs`
  runs the translator against every `.bpl` in `Tests/` and diffs the
  output against `.expect`.

## Known issues

- [#1148](https://github.com/strata-org/Strata/issues/1148) — Umbrella
  issue tracking remaining blockers preventing end-to-end verification of
  SMACK-generated Boogie.
- [#1152](https://github.com/strata-org/Strata/issues/1152) — Sanitization
  can still map distinct Boogie names to the same Strata identifier in
  edge cases not covered by the entity-prefix fix.
- [#1162](https://github.com/strata-org/Strata/issues/1162) — Type checker
  errored on nondet goto with undeclared `$__nondet_N`. Resolved on
  `htd/smack` by emitting an `init` command for the synthetic variable
  in `translateTransfer`; tracked here for cross-reference.
- **`FormatCore.lean` not updated for new `command_cfg_procedure`
  signature.** CI build fails on `Strata/Languages/Core/DDMTransform/FormatCore.lean:991`:
  the call to `Command.command_cfg_procedure` still passes 5 args but
  the grammar now expects 6 (added `locals : Block`). Symptom:
  `Application type mismatch: cfgBody has type CFGBody M but is expected
  to have type CoreDDM.Block M`, plus a downstream `noncomputable`
  failure on `Core.formatProcedure`. Fix path: update the CST builder
  in `FormatCore.lean` to thread the locals block through. Address
  after the branch cleanup is merged.

## Pipeline status

End-to-end results for the 12-program SMACK benchmark
(`Examples/smack-docker/programs/*.c`) are summarized in
`Examples/smack-docker/README.md`.
