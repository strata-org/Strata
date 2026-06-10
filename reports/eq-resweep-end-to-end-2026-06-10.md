# EQ end-to-end re-sweep of the #1331-cleared files (post-fix SMT verdicts)

Date: 2026-06-10
Branch: htd/smack
Binary: `strata` rebuilt 2026-06-10 02:28 (force-relinked; carries the Jun-9 fixes
flushCmds `437d38683` + effective-modifies widening #1331 `188255668`)
Corpus: the **16 "cleared" (oldfvar→ok) files** from
`reports/verify-1331-fix-corpus-2026-06-10.md` — the EQ files whose #1331 ELAB
error the fix eliminated and which then reach a clean type-check.

> **Status: COMPLETE.** All 16 files, all 1,253 procedures verified per-procedure.
> (This supersedes an earlier partial draft; the prior `/tmp`-based run was wiped
> three times, so this rerun writes all artifacts durably under
> `Examples/smack-docker/eq-resweep/` in the repo tree. Driver: `run.sh`,
> resumable; raw per-proc logs: `proc-out/*.out`; taxonomy:
> `analysis/failure-taxonomy.txt`.)

## 1. Headline

This run pushes the #1331-cleared EQ files **past type-check into SMT** — the layer
the prior corpus report (`verify-1331-fix-corpus-2026-06-10.md`) explicitly did not
exercise. Three findings, all from the complete 1,253-procedure dataset:

1. **The #1331 fix holds end-to-end. Zero old-fvar regressions** — across all 1,253
   per-procedure outputs, **0** emit `Cannot find this fvar in the context! old`
   (hard-verified by grep). The fix is not merely a type-check patch; the widened
   effective-modifies set survives all the way through VC generation and SMT.

2. **The #1331-cleared files verify at the procedure level.** Under the
   pilot-equivalent `--split-procs` configuration, the per-procedure outcomes across
   all 1,253 procs are:

   | outcome | count | % |
   |---|---:|---:|
   | **PASS** (real proofs) | 927 | 74.0% |
   | PASS_0 (vacuous — 0 goals) | 158 | 12.6% |
   | PASS-? (vacuous — path unreachable) | 81 | 6.5% |
   | TIMEOUT (60 s cap) | 73 | 5.8% |
   | ERR_FNAME (errno 63) | 13 | 1.0% |
   | ERR_SOLVERCRASH (heap-type) | 1 | 0.1% |

   **Non-failing: 1,166 / 1,253 = 93.1%** (PASS + vacuous). **Real proofs: 927 /
   1,253 = 74.0%.** Only **14 (1.1%) are hard errors**; the rest of the non-PASS
   tail is timeouts. Every one of the 16 files lands `PARTIAL` at the program level —
   but that label reflects a small per-proc failure minority, not a broad failure.

3. **No soundness holes, and the errors are EQ-corpus-specific, not #1331.** All 14
   error procs return rc=3 **and print zero `goals passed` lines** — they fail
   *loudly*; none masks a spurious pass. The two error buckets are a strata
   temp-file-naming bug and a Java-heap SMT-lowering type mismatch (§4), both
   orthogonal to the `old()`-modifies widening.

**Honest one-liner:** *≥74% real proofs, ≤93% non-failing; 73 timeouts unresolved
(a genuine mix — see §3.1); 14 loud tooling errors; 0 soundness holes; 0 #1331
regressions.*

## 2. Methodology catch (load-bearing)

A first pass ran **whole-program** SMT on each translated `.core.st` and produced
**0 PASS / 15 TIMEOUT / 1 ERROR**. That number is a **harness artifact, not a
verifier limit**, and must not be reported as the result:

- These EQ files carry **36–172 procedures each** (they are Java→Boogie "equalizer"
  outputs with a heavy `$heap` model, not SMACK pilot programs).
- The SMACK pilot — and `run_pipeline.py` — verify with **`--split-procs`**, which
  prunes the program to ~1/N before each SMT query
  (`filterProceduresPipelinePhase`). Whole-program SMT over 44–172 procedures at
  once predictably stalls in VC generation: the sampled TIMEOUT outputs showed
  **0 obligations even attempted** — the verifier never reached the solver.
- A spot-check confirmed the fix: the first procedure of the smallest file
  (`EQ_4yipg2qisfn`, the one that ERRORed whole-program) verifies in **1 second**
  and **PASSes** (`All 3 goals passed`) when run with `--procedures`.

So the fair, pilot-equivalent measure is **per-procedure** (`--split-procs`), and
that is what Section 1's numbers report. The whole-program "0 PASS" is recorded here
only to document the methodology trap.

## 3. Per-procedure results (split-procs, the fair measure)

Complete — all 16 files. Columns: pass = real PASS; p? = PASS-? (vacuous);
p0 = PASS_0 (0 goals); err = ERR_FNAME + ERR_SOLVERCRASH; to = TIMEOUT.

| file | procs | pass | p? | p0 | err | to |
|------|------:|-----:|---:|---:|----:|---:|
| EQ_4yipg2qisfn_out | 44 | 39 | 0 | … | 5 | 0 |
| EQ_ofggc1dth0s_out | 36 | 35 | 0 | … | 0 | 1 |
| EQ_putl12axces_out | 47 | 46 | 0 | … | 0 | 1 |
| EQ_52uajzr2i5s_out | 49 | 44 | 0 | … | 4 | 1 |
| EQ_bsowhr2fu12_out | 70 | 63 | 4 | … | 0 | 3 |
| EQ_htqg3z5agdx_out | 54 | 48 | 5 | … | 0 | 1 |
| EQ_knmfqqxigdy_out | 47 | 40 | 6 | … | 1 | 0 |
| EQ_qacza51n1bc_out | 70 | 63 | 4 | … | 0 | 3 |
| EQ_tjkakpi04ae_out | 69 | 62 | 2 | … | 0 | 5 |
| EQ_xcnu42auqk5_out | 49 | 44 | 0 | … | 4 | 1 |
| EQ_yo1ortq3kh2_out | 56 | 55 | 0 | … | 0 | 1 |
| EQ_dbwnbib1y0q_out | 75 | 60 | 8 | … | 0 | 7 |
| EQ_bnxhlpcselv_out | 172 | 143 | 12 | … | 0 | 17 |
| EQ_elbns5m3uk4_out | 96 | 86 | 9 | … | 0 | 1 |
| EQ_jqp2kinnr5j_out | 172 | 137 | 21 | … | 0 | 14 |
| EQ_sz1wo0jj0sg_out | 147 | 120 | 10 | … | 0 | 17 |
| **TOTAL** | **1253** | **927** | **81** | **158** | **14** | **73** |

(`p0`/PASS_0 counts are folded into the TOTAL row; the `pass`+`p?` columns are the
goal-bearing verdicts. Per-file PASS_0 is the remainder; see
`Examples/smack-docker/eq-resweep/program-results.tsv` for the exact split.)

Flags per proc: `verify <st> --procedures <p> --check-mode deductive
--check-level full --call-policy bodyOrContract --inline-fuel 100
--solver-timeout 10`, `gtimeout 60`, single-thread Z3, 2 parallel workers
(memory-bounded; 4-way risked the documented 28.5 GB thrash and was throttled down).

### 3.1 The TIMEOUT bucket is genuinely mixed (not would-be-PASS)

The 73 timeouts split, by output emitted within the 60 s cap:

- **70 / 73 produced *zero* solver output** — strata never reached Z3, stuck in VC
  generation / parsing of the large multi-proc `.core.st`. This is a **scaling
  problem in VC-gen**, the analogue of the whole-program stall (§2) at one tier down.
- **3 / 73 reached the solver** within 60 s (`EQ_htqg3z5agdx`, `EQ_qacza51n1bc`,
  `EQ_jqp2kinnr5j`) but couldn't close.

A **budget re-probe** (re-running 4 of the 0-output procs at `gtimeout 300 /
--solver-timeout 90`) proved "0-output-at-60 s" does **not** mean "would PASS":
- `EQ_yo1ortq3kh2 <clinit>`: got past the stall and finished in 69 s — **807 goals
  passed, 1 FAILED**. The 60 s cap was *masking a real PARTIAL*.
- `EQ_htqg3z5agdx`: still timed out at 300 s after 239 solver-activity lines —
  **genuinely hard SMT**.
- `EQ_ofggc1dth0s`, `EQ_putl12axces`: still 0 output at 300 s — **deep pre-solver
  stall**.

**Consequence:** TIMEOUT mixes deep-stall + hard-SMT + ≥1 masked real failure, so it
cannot be assumed would-be-PASS. The 93.1% non-failing rate is an **upper bound** on
real soundness; the 74.0% real-proof rate is the firm lower bound.

## 4. The two error buckets (NOT #1331, no soundness risk)

The 14 hard-error procedures fail on EQ-corpus-specific issues that #1331 unmasks but
does not cause. Both fail **loudly** (rc=3, zero `goals passed` lines) — neither can
mask an unsound pass.

1. **Filename too long (errno 63) — 13 procs**, all in `EQ_4yipg2qisfn_out` (5),
   `EQ_52uajzr2i5s_out` (4), `EQ_xcnu42auqk5_out` (4). **Deterministic and
   name-length-driven**: every failing proc name is **265–278 chars** (deeply-mangled
   Java signatures). strata writes per-obligation temp `.smt2` files named after the
   *unhashed* obligation name, so name + `_ensures_0_2.smt2` exceeds the OS 255-byte
   path-component limit:
   ```
   <unknown>(1, (0-0)) invalid argument (error code: 63, file name too long)
     file: /var/.../reffile_com_alibaba_excel_..._ensures_0_2.smt2
   ```
   A strata temp-file-naming bug (fix: hash/truncate long obligation names in the
   temp-file path). *(Note: my harness already hashes its **own** output filenames —
   this errno-63 is strata's **internal** `.smt2` emission, a real strata bug.)*

2. **SMT heap-type mismatch — 1 proc** (`EQ_knmfqqxigdy_out`). The Java
   `$heap`/float-array model mislowers to SMT:
   ```
   SMT Solver Crash! ... (error "Parse Error: ...Subexpressions must have the same type:
     Equation: (= Output_of_..._floatArrHeap@44 otherfile__null)
     Type 1: (Map StrataRef (Map (_ BitVec 32) Real))
     Type 2: StrataRef")
   ```
   A real encoding defect in the float-array heap lowering — an `otherfile__null`
   (`StrataRef`) is equated with a `floatArrHeap` (`Map StrataRef (Map BV32 Real)`).

Both are corpus-specific (Java-heap model + name mangling) and orthogonal to the
`old(<unmodified-global>)` widening. They are the *next* blockers for end-to-end EQ
verification, distinct from both #1331 and the modifies-completeness blocker that
the 8 `next_blocker` files hit at type-check.

## 5. Honest scope

- **Sample = the 16 cleared files only**, not the full 3,529-file corpus. These are
  the files #1331 demonstrably unblocked at type-check; this run asks "do they then
  verify?" The answer (per-procedure): 74% real proofs, 93% non-failing, modulo the
  buckets above.
- **Per-procedure, not whole-program.** Program-level verdicts are all PARTIAL because
  every file has *some* non-PASS proc; the meaningful number is the per-proc rate,
  matching how the SMACK pilot is scored. Whole-program SMT (§2) is intractable here.
- **74% is the firm floor, 93% the ceiling.** The 73 timeouts are unresolved and
  genuinely mixed (§3.1) — at least one is a masked real failure — so the true
  real-proof rate sits between 74% and 93%, not at either end. A higher-budget re-run
  (≥300 s/proc, ≥90 s solver) would split the timeouts into real-PASS / real-FAIL, but
  that is a separate, expensive measurement.
- **Zero regressions is exact**, not sampled: grep of `Cannot find this fvar ... old`
  over all 1,253 per-proc outputs returns 0.

## 6. Files referenced (all DURABLE, in the repo tree)

After three `/tmp` wipes destroyed prior runs, everything now lives under
`/Users/htd/Documents/Strata-smack/Examples/smack-docker/eq-resweep/`:

- `run.sh` — resumable driver (translate → enumerate → verify split-procs → tally);
  `bash run.sh tally` recomputes from existing outputs.
- `files.txt` (16 names), `proc-worklist.tsv` (1,253 file⇆proc rows).
- `core-st/*.core.st` — the 16 post-fix translations (input to verify).
- `proc-out/*.out` — all 1,253 raw per-proc strata outputs (each has `### PROC` /
  `### FILE` / body / `### RC`).
- `proc-results.tsv` (file⇆proc⇆class), `program-results.tsv` (per-file tally),
  `failures.tsv` (the 87 non-PASS), `timeouts.tsv` / `err_fname.tsv` / `err_crash.tsv`.
- `reprobe/*.out` — the budget re-probe outputs (§3.1).
- `analysis/failure-taxonomy.txt`, `analysis/reprobe-finding.txt` — the §3.1/§4 source.
- Prior type-check-layer report: `reports/verify-1331-fix-corpus-2026-06-10.md`
- Fix commit: 188255668
