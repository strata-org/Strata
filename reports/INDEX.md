# Reports index

Triage writeups, draft upstream issues, and post-mortems. Each entry: status (RESOLVED / PARTIAL / OPEN / SUPERSEDED-BY) + one-sentence next-action pointer.

For open feature work (not tied to a specific bug report), see [`BACKLOG.md`](BACKLOG.md).

## Verifier hang / overflow cluster

| Report | Status | Next action |
|---|---|---|
| [stack-and-hang-conjectures-report.md](stack-and-hang-conjectures-report.md) | **truth-of-record** | None — diagnoses for issues 1, 2, 3 are now stable. |
| [issue-1-unblocking-2026-06-02.md](issue-1-unblocking-2026-06-02.md) | RESOLVED on `htd/smack` — sce1 reaches verdict at N=100K (38s), N=200K (144s); N=500K is CPU-bound (performance, not stack). 4-commit cherry-pick `95abbe567`/`7b1018e81`/`73c17b1bd`/`fab1575f8`. | None — sce1 fully unblocked. |
| [issue-2-elabexpr-overflow-upstream-filing.md](issue-2-elabexpr-overflow-upstream-filing.md) | OPEN — self-contained upstream-filing artifact ready | File standalone issue against strata-org/Strata. Fix is 8-12h on the `elabExpr`/`runSyntaxElaborator`/`elabSyntaxArg` cycle in `StrataDDM`. |
| [issue-3-deferred-doubling-upstream-filing.md](issue-3-deferred-doubling-upstream-filing.md) | RESOLVED on `htd/smack` (commit `8f019818f`); filed upstream as [#1316](https://github.com/strata-org/Strata/issues/1316) + PR [#1317](https://github.com/strata-org/Strata/pull/1317) | Track #1317 review/merge. |
| [issue-3-mwe-15procs.core.st](issue-3-mwe-15procs.core.st) | reference artifact | Linked from the upstream filing; reproduces the doubling on `htd/smack` pre-fix. |
| [strata-verify-stack-overflow-deeply-nested-expr.md](strata-verify-stack-overflow-deeply-nested-expr.md) | OPEN (issue 2 — superseded as the upstream-filing target by `issue-2-elabexpr-overflow-upstream-filing.md`) | Use `issue-2-elabexpr-overflow-upstream-filing.md` for the actual filing; this older draft retained for triage history. |
| [elabexpr-paren-strip-experiment.md](elabexpr-paren-strip-experiment.md) | discarded micro-fix | Already consumed as triage evidence in `issue-2-elabexpr-overflow-upstream-filing.md`. Not a standalone report. |
| [v5-pass-question-mark-analysis.md](v5-pass-question-mark-analysis.md) | informational | None (records the qualitative analysis behind v5/v6 PASS-? matrix surfacing; closed when fuel-bump experiment confirmed loop-havoc as cause). |

The cluster's umbrella issue, "non-TCO walker family across the verify pipeline," was originally tracked as Conjecture A. Empirical bisection has now disambiguated three issues:

- **Issue 1** (flat-list overflow) — RESOLVED on `htd/smack` via 4-commit cherry-pick (`95abbe567`, `7b1018e81`, `73c17b1bd`, `fab1575f8`) iterativizing `PrecondElim.transformDecls`, `TermCheck.transformDecls`, `translateCoreDecls`, `Program.typeCheck`, plus an O(N²)→O(N) `runProgram` walker. sce1 reaches a verdict at N=100K (38s), N=200K (144s); at N=500K CPU-bound (performance ceiling, not a stack bug).
- **Issue 2** (deeply-nested-expr overflow) — OPEN. Diagnosis corrected; actual culprit is `elabExpr` cycle in `StrataDDM/StrataDDM/Elab/Core.lean:1694`. Self-contained upstream filing ready ([`issue-2-elabexpr-overflow-upstream-filing.md`](issue-2-elabexpr-overflow-upstream-filing.md)); not yet posted. Fix scope: 8-12h on a critical mutual block.
- **Issue 3** (large-`.bpl` hang) — RESOLVED on `htd/smack` via commit `277c468cb` (cherry-picked as `8f019818f`). `Env.deferred` dedup on CFG `condGoto` false branch. Width-O(2^K) array growth, not a non-TCO walker. Filed upstream as [#1316](https://github.com/strata-org/Strata/issues/1316) + PR [#1317](https://github.com/strata-org/Strata/pull/1317) targeting `htd/unstructured-procedure`.

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
