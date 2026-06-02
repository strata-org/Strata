# Reports index

Triage writeups, draft upstream issues, and post-mortems. Each entry: status (RESOLVED / PARTIAL / OPEN / SUPERSEDED-BY) + one-sentence next-action pointer.

## Verifier hang / overflow cluster

| Report | Status | Next action |
|---|---|---|
| [stack-and-hang-conjectures-report.md](stack-and-hang-conjectures-report.md) | **truth-of-record** | Update issue 1 section once next downstream walker for sce1 is identified (see follow-up §4) |
| [strata-verify-stack-overflow-deeply-nested-expr.md](strata-verify-stack-overflow-deeply-nested-expr.md) | OPEN (issue 2 — diagnosis corrected 2026-06-02; no fix landed) | Combine with `elabexpr-paren-strip-experiment.md` into a self-contained upstream filing; rewrite the `elabExpr` mutual cycle as worklist + combiner stack (8-12h) |
| [elabexpr-paren-strip-experiment.md](elabexpr-paren-strip-experiment.md) | discarded micro-fix | Consume as triage evidence in the issue 2 upstream filing; not a standalone report |
| [v5-pass-question-mark-analysis.md](v5-pass-question-mark-analysis.md) | informational | None (records the qualitative analysis behind v5/v6 PASS-? matrix surfacing; closed when fuel-bump experiment confirmed loop-havoc as cause) |

The cluster's umbrella issue, "non-TCO walker family across the verify pipeline," was originally tracked as Conjecture A. Empirical bisection has now disambiguated three issues:

- **Issue 1** (flat-list overflow) — partially resolved on `htd/smack-tco-experiment` (`PrecondElim.transformDecls`, `TermCheck.transformDecls`, `translateCoreDecls`, `typeCheckIter`, `runProgram`-O(N) iterativized). Threshold advanced from N≈30K to ≥50K. At N≥100K a different downstream walker still SIGABRTs.
- **Issue 2** (deeply-nested-expr overflow) — diagnosis corrected; original `translateExpr` location was wrong. Actual culprit: `elabExpr` cycle in `StrataDDM/StrataDDM/Elab/Core.lean:1694`. No fix landed.
- **Issue 3** (large-`.bpl` hang) — RESOLVED on `htd/smack` via commit `277c468cb`. `Env.deferred` dedup on CFG `condGoto` false branch. Width-O(2^K) array growth, not a non-TCO walker.

## CBMC backend triage

| Report | Status | Next action |
|---|---|---|
| [cbmc-inout-rename-collision.md](cbmc-inout-rename-collision.md) | RESOLVED on `htd/smack` (commit `f265cda63`); upstream issue [#1198](https://github.com/strata-org/Strata/issues/1198) | Track #1198 to merge |
| [cbmc-timeouts-and-stale-expects-report.md](cbmc-timeouts-and-stale-expects-report.md) | RESOLVED on `htd/smack` (RPO emission fix `520f3f573`) | None — fix landed; report kept as motivation for the patch |

## BoogieToStrata translator

| Report | Status | Next action |
|---|---|---|
| [verifier-assume-synthesis-report.md](verifier-assume-synthesis-report.md) | RESOLVED on `htd/smack` (commit `1b2231f99`, cherry-picked from PR 1149) | Track upstream PR 1149 |

## Filing & follow-up tracking

For the `htd/smack` branch's bug ledger (per-fix landing status, upstream issue numbers, etc.), see [`Examples/smack-docker/BRANCH_FEATURES.md`](../Examples/smack-docker/BRANCH_FEATURES.md) §9.

For the verification matrix history (v1 → v6) and per-program verdicts, see [`Examples/smack-docker/README.md`](../Examples/smack-docker/README.md) "Run history" and "v6 per-program detail" sections.
