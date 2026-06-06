# EQ Post-Fix Rerun Plan (2026-06-05)

Two re-test plans queued behind upstream/local fixes. No live runs here — recipes only.

## Track A: Post-#1331 Java-SMACK re-test (28 files)

**Trigger**: lean4 PR #1331 merges to `main2` AND reaches `htd/smack` via toolchain bump.

**Background**: Tier-1 sweep over the 28-file Java-SMACK roster showed 21.4% (6/28) elab-fail
with `Cannot find this fvar in the context! old <var>`. All 6 trip the same #1331 root cause
(see `/Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-anomalies-audit-2026-06-05.md`).

**Expected outcome**: the elab-fail bucket clears (6 → 0). Remaining 22 files unchanged.

**Reproduction recipe** (per file):
```bash
cd /Users/htd/Documents/Strata-smack
gtimeout 60s lake exe strata verify <path-to-eq-file>.st 2>&1 | tee /tmp/rerun-$(basename <file> .st).log
```

**Pass criteria**: zero `Cannot find this fvar in the context! old` occurrences across all 28 logs.

## Track B: Post-e15 Probe-2 re-test (10 files)

**Trigger**: ALREADY MET — e-15 fix landed on `htd/smack` at merge `c1b1ce5ee`. Ready to run.

**Roster** (10 files from Probe 2):
- EQ_032wuerhmvw
- EQ_0agwqtm2bcg
- EQ_0c53ogei0g4
- EQ_0exak45poxy
- EQ_0fmj2meb0oj
- EQ_0gsuem3slyl
- EQ_0q0oga15aij
- EQ_0rvvwfsfv2r
- EQ_0stx52y505t
- EQ_0z42qdmejd0

**Pre-fix bucket distribution**:
| Bucket | Count | Files |
|---|---|---|
| PARTIAL with e-15 errors | 1 | (one of the 10) |
| Silent TIMEOUT with `e-` evidence in stderr | 4 | |
| FAIL-elab (#1331) | 1 | |
| Silent TIMEOUT without `e-` evidence | 4 | |

**Expected post-fix outcomes**:
- 5+ files flip to PASS (the 1 PARTIAL + 4 e-15 silent timeouts).
- 1 file unchanged — typecheck-blocked (#1331), waits on Track A.
- 4 files (silent TIMEOUT without `e-` evidence) MAY OR MAY NOT shift; treat as exploratory signal.

**Reproduction recipe** (per file):
```bash
cd /Users/htd/Documents/Strata-smack
gtimeout 60s lake exe strata verify Examples/aaron-eq-portfolio/<EQ_NAME>.st \
  2>&1 | tee /tmp/probe2-rerun-<EQ_NAME>.log
echo "exit=$?"
```

**Pass criteria**:
- ≥5/10 logs end in PASS.
- The 1 #1331 file still elab-fails with `old <var>` (expected; clears under Track A).
- Re-bucket the 4 unknowns and append to the portfolio anomalies audit.

## Outputs

After each track runs, append a results section to:
`/Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-anomalies-audit-2026-06-05.md`
with the new bucket counts and any net-new failure modes surfaced.
