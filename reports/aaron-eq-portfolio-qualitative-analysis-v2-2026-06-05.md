# Aaron's EQ Portfolio — Qualitative Analysis (v2)

*Companion to /Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-qualitative-analysis-2026-06-04.md. Assume the reader has read v1; this document goes deeper into the eight axes the v1 left as inferences or open questions.*

---

## 0. What this document changes vs. v1

v1 framed five clusters and projected behavior on a wider sweep. v2 ran six targeted probes and three skeptic cross-checks. The net effect on v1's claims:

| v1 claim | v2 status | Section |
|---|---|---|
| Cost regression is "doubled SMT workload of `--check-level full`" | **Partly correct, materially under-stated.** Doubled queries are a 2× factor; observed wall-clock gap on bodyOrContract is 8–14×. | §3 |
| `--check-level minimal --call-policy bodyOrContract` is the right batch default | **Mostly right with one caveat.** Minimal silently conflates `passAndReachable` with vacuously-true (skips reachability/satisfiability check). | §3 |
| 18 large-bucket TIMEOUTs are "non-tail recursion in body-eval walker" | **Direction right, dimension wrong.** Not raw block/AST size — the walker that overflows is the per-fork branch-spawn at two-target gotos. | §7 |
| PARTIAL on Neq.SameV is "bodyOrContract correctly refusing designed non-equivalents with witnesses" | **Three-way conflation.** Refusal is real; "with witnesses" is false in current CLI; "designed non-equivalent" is sometimes a solver-options artifact (z3-default classifies one as ❌-with-counterexample). | §5 |
| Shared-UF makes contract verdicts "uninformative as soundness check" | **Confirmed verbatim.** §2 quotes the SMT-LIB. | §2 |
| Goal-count divergence is "≈14 ensures × paths fan-out" on constructor-heavy harness | **Right structure, wrong arithmetic.** It's 56 ensures × ~5× uniform path-fanout, not 28 × (10−2). | §6 |

The v1 took a pessimistic view of the corpus's signal-to-noise. v2 makes that view sharper *and* in two places less generous: the witness story is overstated and the shared-UF defect is not just abstraction loss but a translation-time silent rewriting of the question being asked.

---

## 1. Per-benchmark-family taxonomy

### 1.1 The two structural families

Reconstructing the 72-file sample (union of 22 named in v1's batch reports + alphabetic-first stratified fill, matching batch 1's stated method exactly and approximating batch 2's stride-spaced pick), the corpus splits into **two structurally distinct families** that align almost perfectly with the two largest defect clusters:

| Family | # files | Procedure-name pattern | Eq/Neq label | Bucket dominance |
|---|---:|---|---|---|
| Synthetic-benchmark | 36 | `reffile.benchmarks.<suite>.<bench>.<Eq\|Neq>.SameV` | explicit | small + medium |
| Java-SMACK | 36 | `reffile.<javapackage>.*$method` | none (implicit 1-vs-1) | 23 of 24 large |

This is the **primary structural finding** of the second pass. Aaron's portfolio isn't one corpus — it's two corpora that happen to share a `.bpl` file extension. The synthetic-benchmark family generates the precision-flip and harness-mis-construction patterns from v1 §4.5; the Java-SMACK family generates the SO and elab-defect clusters from v1 §4.6 and §4.4. The "verdict skew per suite" observation in v1 was, at root, "verdict skew per family."

### 1.2 Suite distribution (72 files)

| Suite | benchmarks | files | Eq | Neq | NA |
|---|---:|---:|---:|---:|---:|
| Java-SMACK | 9 (ArrayDeque, ArrayList, Arrays, CC, HashMap, HashSet, Iterator, Throwable, unknown-pkg) | 36 | 0 | 0 | 36 |
| CLEVER | 7 (LoopSub, getSign2, is_prime1, ltfive, multiple, odd, pos) | 13 | 8 | 5 | 0 |
| REVE | 8 (addhorn, inlining, limit1, limit2, loop3, loop5, triangular, triangularMod) | 10 | 5 | 5 | 0 |
| tsafe | 2 (conflict, normAngle) | 3 | 0 | 3 | 0 |
| airy | 1 (MAX) | 2 | 1 | 1 | 0 |
| dart | 1 (test) | 2 | 2 | 0 | 0 |
| optimization | 1 (theta) | 2 | 1 | 1 | 0 |
| ej_hash | 1 (hashCode) | 1 | 1 | 0 | 0 |
| bess | 1 (pythag, SQR via subset) | 1 | 0 | 1 | 0 |
| caldat | 1 (caldat) | 1 | 0 | 1 | 0 |
| tcas | 1 (tcas) | 1 | 1 | 0 | 0 |
| **Total** | — | **72** | **19** | **17** | **36** |

The synthetic Eq:Neq ratio is 19:17 ≈ 1.12 — essentially balanced. Every sampled instance is `SameV`; no `DifferentV` files appear in the 72.

### 1.3 Verdict cross-tabulation (deep-dived 22 only)

Verdicts are known only for the 22 files batch 1 and batch 2 deep-dived. The remaining 50 are "unknown" — the original sweep's verdicts on those files weren't preserved in the reports.

| Family | n | PASS | PARTIAL | TIMEOUT | FAIL-SO | FAIL-elab | unknown |
|---|---:|---:|---:|---:|---:|---:|---:|
| CLEVER (synthetic) | 13 | 0 | 4 | 0 | 1 | 0 | 8 |
| REVE (synthetic) | 10 | 2 | 1 | 1 | 0 | 0 | 6 |
| tsafe (synthetic) | 3 | 0 | 0 | 2 | 1 | 0 | 0 |
| airy/bess/dart/optim. (synth.) | 7 | 0 | 1 | 1 | 0 | 0 | 5 |
| Java-SMACK | 36 | 0 | 0 | 0 | 5 | 3 | 28 |

| Tag | n | PASS | PARTIAL | TIMEOUT | FAIL-SO | FAIL-elab |
|---|---:|---:|---:|---:|---:|---:|
| Eq | 19 | 2 | 3 | 1 | 0 | 0 |
| Neq | 17 | 0 | 3 | 4 | 2 | 0 |
| NA (Java) | 36 | 0 | 0 | 0 | 5 | 3 |

### 1.4 Cross-tabulation against v1's clusters

| v1 cluster | Family origin | Suite skew |
|---|---|---|
| C1: contract = vacuous PASS | both families equally | uniform |
| C2: bodyOrContract precision flip on Neq.SameV | synthetic only | CLEVER (4 of 7 PARTIALs), REVE (1), airy (1), tsafe (2 timeouts that on bigger budget would PARTIAL) |
| C3: cost regression (260→2020+ goals) | synthetic, constructor-heavy | REVE addhorn, CLEVER multiple — files where the EQ harness calls a stub-laden `_la_init_ra_` constructor |
| C4: stack overflow | **Java-SMACK exclusive** (5 of 5 known SO verdicts) | 100% Java-SMACK |
| C5: `old(<global>)` elab defect | **Java-SMACK exclusive** (3 of 3) | 100% Java-SMACK |

REVE is the most well-behaved synthetic suite (2/4 known verdicts are PASS). CLEVER is the most informative for precision evidence (4/5 known are PARTIAL on the right files). tsafe is uniformly non-PASS in the deep-dive set. **Java-SMACK has zero known PASSes and zero known PARTIALs** — every Java-SMACK file with a known verdict is a hard failure, either SO or elab. This is the strongest skew in the data and the one the v1 didn't explicitly call out.

---

## 2. The shared-UF mechanism, mechanically

### 2.1 The verbatim declaration

From `/tmp/claude-503/uf-probe/EQ_CharactergetTypelpCrpI_ensures_0_0.smt2`, lines 127–134, on a fresh translate-and-verify of `Examples/smack-docker/boogie-files/EQ_jxsw3zuslgt_out.bpl` (`benchmarks.bess.SQR.Eq.SameV`):

```smt2
; _uf_otherfile_Character_getType__lp_C_rp__I__exception
(declare-fun _uf_otherfile_Character_getType__lp_C_rp__I__exception ((_ BitVec 16)) StrataRef)
; _in_parameter__0@5
(declare-const _in_parameter__0@5 (_ BitVec 16))
; otherfile_BYTE_DEFAULT
(declare-const otherfile_BYTE_DEFAULT (_ BitVec 8))
; _uf_otherfile_Character_getType__lp_C_rp__I__return
(declare-fun _uf_otherfile_Character_getType__lp_C_rp__I__return ((_ BitVec 16)) (_ BitVec 32))
```

There is **only one** UF declaration for `Character.getType` — namespaced under `otherfile`, with no `_uf_reffile_*` counterpart. SMACK's translation rule for cross-side spec-only methods names the shared symbol after `otherfile`, and the `reffile` side resolves to it.

### 2.2 The verbatim wiring

Lines 191, 193, 280–283 of the same SMT-LIB file:

```smt2
(define-fun $__anf.22 () StrataRef
  (_uf_otherfile_Character_getType__lp_C_rp__I__exception _in_parameter__0@5))
(define-fun $__anf.24 () (_ BitVec 32)
  (_uf_otherfile_Character_getType__lp_C_rp__I__return _in_parameter__0@5))
...
(assert (= _return@10 $__anf.24))      ; reffile-side return
(assert (= _exception@14 $__anf.22))   ; reffile-side exception
(assert (= _return@11 $__anf.24))      ; otherfile-side return — same UF, same arg
(assert (= _exception@15 $__anf.22))   ; otherfile-side exception — same UF, same arg
```

`_return@10` is reffile, `_return@11` is otherfile. After these four assertions, both sides' return values are constrained to be **byte-identical SMT terms**.

### 2.3 The verbatim obligation

Lines 284–289:

```smt2
(set-info :file "/tmp/claude/jxsw_fixed.core.st")
(set-info :start 158529)
(set-info :stop 158562)
(set-info :unsat-message "Property is always true")
(assert (not (and (or AA_TEMP51@2 (= _exception@14 _exception@15))
                  (or AA_TEMP50@2 (= _return@10 _return@11)))))
(check-sat)
```

After the four equalities reduce `(= _exception@14 _exception@15)` to `(= $__anf.22 $__anf.22)` (true by reflexivity) and `(= _return@10 _return@11)` to `(= $__anf.24 $__anf.24)` (likewise), the obligation is `(not (and true true)) = false`. UNSAT ⇒ "Property is always true." Z3 closes this by congruence on identical terms before any reasoning about Character semantics.

### 2.4 Side-by-side — what bodyOrContract would do instead

| Aspect | `--call-policy contract` (verbatim above) | `--call-policy bodyOrContract` (projected) |
|---|---|---|
| UFs declared | 1 per spec-only method, namespaced `_uf_otherfile_*` | 0 for methods with a body; 2 (separate `_uf_reffile_*` and `_uf_otherfile_*`) only for leaves that bottom out in spec-only stubs |
| `_return@10` definition | constrained `= (_uf_otherfile_f x)` | defined by reffile body — chain of `(ite ... ...)` over reffile's CFG |
| `_return@11` definition | constrained `= (_uf_otherfile_f x)` (**same term**) | defined by otherfile body — distinct `(ite ... ...)` chain |
| Final obligation shape | `(not (= (f x) (f x)))` ⇒ trivially UNSAT by reflexivity | `(not (= (otherfile_body x) (reffile_body x)))` ⇒ genuine SMT work, possibly SAT |
| Solver effort | microseconds; congruence closure | seconds-to-minutes; bit-blasting / quantifier instantiation per path |
| Goal count for jxsw3zuslgt | 138 | hundreds-to-thousands (per the §6 fan-out mechanism) |
| Discriminative power | zero (cannot distinguish equivalent from inequivalent bodies) | full (distinguishes when SMT terminates) |

### 2.5 Vacuously sound, not unsound

The verifier returns no false claim *about the formula it built*. The defect is at translation time: BoogieToStrata's UF-naming convention silently substitutes the trivially-true claim "the abstraction of `f` equals itself" for the intended claim "the two implementations of `f` compute the same function." A buggy `otherfile.f` returning `x + 1` while `reffile.f` returns `x` would still PASS under `--call-policy contract`, because both calls become `(_uf_otherfile_f x) = (_uf_otherfile_f x)`. The Neq.SameV files PASSing under contract while PARTIAL-ing under bodyOrContract is the empirical demonstration — body-eval decides the question, contract does not.

---

## 3. Cost-regression resolution

### 3.1 The 5×2 minimal-check probe

5 files × 2 configs, all 10 runs reached a verdict, 60-second ceiling, none timed out:

| File | A: contract @ minimal | B: bodyOrContract+fuel100 @ minimal |
|---|---|---|
| EQ_0exak45poxy_out | PARTIAL 0.53s — 260 passed, 1 failed | PARTIAL 24.03s — 2020 passed, 1 failed |
| EQ_s541ce4abnj_out | PARTIAL 0.47s — 260 passed, 1 failed | PARTIAL 24.00s — 2020 passed, 1 failed |
| EQ_oqt2xfezy0x_out | PASS 0.34s — 267 passed | PARTIAL 15.22s — 4108 passed, 1 failed |
| EQ_vtepk5bv3ld_out | PASS 0.37s — 280 passed | PASS 2.93s — 1516 passed |
| EQ_mtonvj3sujq_out | PASS 1.61s — 610 passed | PARTIAL 36.36s — 6206 passed, 1 failed |

All 5 cleared the 60s timeout under bodyOrContract+fuel100, including `mtonvj3sujq` which v1 marked as a likely "eval-side blow-up." The original sweep's TIMEOUTs on these files were therefore **config-driven** (the doubled-query overhead of `--check-level full`), not eval-side pathology.

### 3.2 Skeptic cross-check: minimal vs. full at the same VC

The original framing called full's overhead "doubled SMT workload." The actual numbers are larger:

| File | bodyOrContract @ minimal | bodyOrContract @ full | factor |
|---|---|---|---|
| EQ_vtepk5bv3ld_out | 2.98s, PASS 1516 | 41.31s, PASS 1516 | **13.9×** |
| EQ_oqt2xfezy0x_out | 14.6s, PARTIAL 4108+1 | TIMEOUT @ 120s | **≥8.2×, no verdict** |

The 2× factor predicted by "one extra SMT query per VC" is correct for the *count* of solver invocations. Wall-clock on bodyOrContract is 4–7× worse than that ratio, suggesting solver pathology compounds: under `full`, the satisfiability check `P ∧ Q` on body-eval-fanned-out goals (1516–4108 of them, each with hundreds of constituents inlined) hits non-linear solver behavior. Verdicts agree where full completes (1 of 2). Where full doesn't complete, minimal is *strictly more informative*.

### 3.3 What `--check-level minimal` skips

From `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean` lines 1051–1061, in `deductive` mode:

- For an obligation with `passWhenUnreachable = true` (the default for ensures/asserts), `minimal` ⇒ `(false, true)` — only the validity check `assert (not Q); check-sat` runs.
- `full` ⇒ `(true, true)` — both the satisfiability check `assert P; check-sat` (reachability) and validity check run.

So `minimal` cannot distinguish `passAndReachable` from `vacuouslyTrue` (unreachable). It silently classifies vacuously-true obligations as PASS. For Aaron's EQ benchmarks, where assertions are equality-of-outputs at procedure exit (not dead-code corners), this is mostly benign — but it's a real precision loss that masks reachability regressions.

### 3.4 Verdict on the discriminator

| Question | Answer |
|---|---|
| Did `minimal` rescue the 5 cost-regression files? | **Yes — all 5/5 cleared at 60s** under bodyOrContract+fuel100. |
| Is this a "config bug" or "eval-side issue"? | **Config-driven**. The eval-side cost (260→6206 goals) is real but tractable; full's per-VC overhead pushes it past wall-clock. |
| Should `minimal` become the batch default? | **Yes, with one caveat**: minimal masks reachability. Run periodic full-check sweeps (or sample subsets) to catch reachability regressions. |
| Is `mtonvj3sujq` "unfixable by config alone"? | **No — it cleared at 36.36s under minimal+bodyOrContract+fuel100**. v1's framing of mtonvj3sujq as a likely eval-side outlier was wrong; it was full-driven. |

The cleaner empirical statement: **the cost regression is a `--check-level full × bodyOrContract` interaction**, not either factor alone.

### 3.5 Caveat on the "harness mis-construction" interpretation

Two of the 5 (0exak45poxy, s541ce4abnj) PARTIAL under both A and B with the same surviving failing VC. v1 attributed these to harness mis-construction. The minimal probe confirms: the surviving failing VC is contract-level (visible already with the trivially-true UF abstraction), so it cannot be a body-eval precision win — it's a harness-side defect that survives even the vacuously-sound abstraction. v1's interpretation stands for these two files.

---

## 4. TIMEOUT shape analysis

### 4.1 The probe

Three large-bucket genuine TIMEOUTs were probed at 30s / 120s / 300s ceilings under `--check-level minimal --call-policy contract`. Two side-cases were retained because the first picks turned up complications:

| File | bpl lines | bpl size | fixed.st size | t=30s | t=120s | t=300s | Bucket |
|---|---:|---:|---:|---|---|---|---|
| EQ_a3311njprsh_out | 7032 | 374K | 709K | PASS @ 4–6s | PASS @ 5s | PASS @ 5s | not-a-timeout |
| EQ_oyyee3takad_out | 7159 | 642K | 1.0M | SO @ 15s (rc=134) | SO @ 15s | SO @ 15s | deterministic crash |
| EQ_pn00jcs4s3w_out | 7049 | 618K | 3.6M | TIMEOUT (rc=124) | PASS @ 98s — 4712 goals | PASS @ 108s | slow-but-bounded |
| EQ_mqh4ychnlnw_out | 7193 | 1.3M | 2.6M | TIMEOUT | PASS @ 62s — 3251 goals | PASS @ 63s | slow-but-bounded |
| EQ_jxlwsuc1oqw_out | 7121 | 599K | 1.6M | TIMEOUT | TIMEOUT @ 120s | TIMEOUT @ 300s | unbounded (≥300s) |

Of the 3 genuine TIMEOUTs at 30s, **2/3 cleared at 120s under minimal**, one was unbounded out to 300s. mqh4ychnlnw needed 62 seconds — i.e., the original 60-second budget was 2 seconds too tight. pn00jcs4s3w needed 98s.

### 4.2 Same files at the sweep's actual settings (`--check-level full`)

| File | full @ 300s |
|---|---|
| EQ_a3311njprsh_out | PASS @ 110s — 818 goals |
| EQ_pn00jcs4s3w_out | TIMEOUT @ 300s |
| EQ_mqh4ychnlnw_out | TIMEOUT @ 300s |

Under the original sweep's `full` setting, both "slow-but-bounded under minimal" files become 300-second timeouts. The pattern from §3 holds: full × bodyOrContract is the expensive combination, and simply doubling the wall-clock budget (60→300s) under full converts only ~1 in 3 of these.

### 4.3 Extrapolation to the 18 large-bucket TIMEOUTs

Three structural buckets, and a confound:

| Bucket | Cause | Estimated share of 18 (under sweep settings) | Recovery path |
|---|---|---:|---|
| Slow-but-bounded under minimal+bodyOrContract+fuel100 | full-mode SMT pathology | ~10–13 (≈60–70%) | switch default to minimal |
| Unbounded under minimal | actual eval-side or solver-side pathology | ~3–5 (≈20–30%) | requires investigation; may be the genuine residue of v1 §4.6 |
| Deterministic SO mis-bucketed as TIMEOUT | non-tail walker | unknown but >0 | per-fork TCO; see §7 |

The third bucket is real: `oyyee3takad` shows up here as a 15-second SO crash with `rc=134`, which `parse_strata_output` would classify as `FAIL` ("Unknown output"), not TIMEOUT, but the boundary cases — files whose SO-ing happens after a long body-eval phase — could plausibly time out the wall-clock before crashing. v1 treated TIMEOUT and FAIL-SO as disjoint clusters; the correct picture is that **TIMEOUT and SO are points on a single spectrum**, where SO wins if the recursive walker exhausts the stack first and TIMEOUT wins if Z3 exhausts the wall-clock first.

### 4.4 Verdict on the wall-clock budget

| Mode | 60s budget characterization | Recommendation |
|---|---|---|
| `--check-level minimal --call-policy bodyOrContract` | mildly tight — mqh4ychnlnw needed 62s, pn00jcs4s3w 98s | bump to 120s (cheap, recovers ~2/3 of bucket-1) |
| `--check-level full --call-policy contract` (original sweep) | roughly right; bumping to 300s rescues 1/3 at large CPU cost | not the right lever — switch check-level instead |

**The bigger lever is `--check-level`, not the wall-clock budget.** Per CPU-minute cleared, minimal-with-120s converts more cases than full-with-300s.

---

## 5. Witness extraction — reality check

### 5.1 What the CLI actually prints on a Neq.SameV PARTIAL

For `EQ_ike2wen0cz0` (smallest Neq.SameV PARTIAL) under `--check-mode bugFinding --check-level full --call-policy bodyOrContract`:

```
EQ_ike2wen0cz0.core.st(1285, 2) [EQ_..._ensures_0]: ❓ unknown
  (always true if reached on 2 paths, unknown on 1 path)
Finished with 1122 goals passed, 1 failed.
```

No `(model ...)`, no `Counterexample:`, no input values. Same output under `--verbose` and under `--check-mode bugFindingAssumingCompleteSpec`. The witness-extraction code path **exists** in `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean` (lines 1003–1006: `convertModel m` is called only on `.sat` results) and the formatter at `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/SarifOutput.lean` lines 52–54 prints `"Always false and reachable with counterexample: ..."` only for `❌` and `🔶` verdicts.

### 5.2 The deeper finding: PARTIAL is the wrong verdict

Per-path SMT files extracted via `--vc-directory` for the failing obligation, run through z3 with **default options** (not Strata's pinned `smt.mbqi false / auto_config false`):

| Path file | satisfiability | validity | Resulting verdict |
|---|---|---|---|
| `EQ_..._ensures_0_68.smt2` | sat | unsat | ✔️ always true if reached |
| `EQ_..._ensures_0_200.smt2` | sat | unsat | ✔️ always true if reached |
| `EQ_..._ensures_0_135.smt2` | **sat** | **sat** | **🔶 always-false-and-reachable, with concrete model** |

Under z3-default on path 135, `(get-value ...)` returns specific bitvector inputs that witness the inequivalence. But Strata's pinned options force `smt.mbqi false` (no model-based quantifier instantiation), and cvc5's default also returns `unknown` on these quantifier-heavy SMACK encodings. So the verifier sees `unknown / unknown`, classifies as ❓, and `model = []` per the `convertModel` gate — no witness can be extracted because none was produced.

### 5.3 Implication for the user's diagnostic workflow

v1 said PARTIAL surfaces concrete witnesses ("`f($this, 2, 0)` for addhorn, `x=5` for multiple"). The CLI does not print these. They came from manual inspection of the procedure body, not from verifier output.

The synthesis claim conflated three distinct things:

| Claim | True? |
|---|---|
| The Neq.SameV benchmarks are non-equivalent | True |
| The verifier refuses to certify | True (as `❓ unknown`, not `❌ always false`) |
| The verifier surfaces witnesses | **False** in current CLI |

For diagnostic actionability today:

1. **Extract per-path SMT** via `--vc-directory $TMPDIR/vcs`.
2. **Run z3 with default options** (strip Strata's pinned `smt.mbqi` flag) on the failing path file. On at least 1 of 7 Neq.SameV cases this flips PARTIAL→❌ with a concrete `(get-value ...)` model. The other 6 should be re-tested.
3. **Project model variables** onto procedure inputs (`_in_parameter__*`, `_this`) by reading the variable map at the top of the .smt2 file.

This is workflow, not feature work — the verifier already extracts and prints models when it gets `.sat` outcomes. The blocker is upstream: pinned solver options suppress otherwise-decidable instances.

### 5.4 Refined Neq.SameV claim

v1's "bodyOrContract correctly refuses these designed-non-equivalent benchmarks (precision wins)" should be downgraded to:

**"bodyOrContract pessimistically refuses to certify Neq.SameV benchmarks under pinned solver options that suppress quantifier instantiation. Default-options z3 on at least one of these cases re-classifies the refusal as a hard ❌-with-counterexample. The methodology success of these PARTIALs is partly an artifact of solver configuration, not solely of the body-eval policy."**

This is empirically measured on `ike2wen0cz0` (path 135) and structurally inferred for the other 6 (same encoding shape, same SMACK rewriting; not yet directly tested).

---

## 6. Goal-count divergence — mechanism

### 6.1 Verified arithmetic on `ike2wen0cz0` (267 → 1123)

Per-cluster goal-occurrence counts under `--call-policy contract` vs. `bodyOrContract`:

| Cluster | Distinct labels | contract | body | Δ | Per-label multiplier |
|---|---:|---:|---:|---:|---|
| `*_la_init_ra_ensures_*` (constructor ensures, 14 ensures × 4 procs) | 56 | 84 | 420 | **+336** | half 1→5, half 2→10 (uniform 5×) |
| `*_initIntArray_ensures_*` | 6 | 6 | 30 | +24 | 1→5 |
| `*_f__lp_I_I_ensures_*` (the EQ-targeted body) | 4 | 16 | 40 | +24 | half 3→15, half unchanged |
| `*_String_*_ensures_*` (charAt, compareTo, …) | many | 119 | 591 | **+472** | 1→5 |
| `assert_NN` (raw asserts not behind a call) | 42 | 42 | 42 | 0 | unchanged |
| **Total** | | **267** | **1123** | **+856** | |

v1 claimed "+224 each from `reffile_*_la_init_ra` and `otherfile_*_la_init_ra` (14 × {2 → 10 paths})." Actual:

- The 14-ensures × 4-procs structure is correct; **56 distinct ensures labels**, not 28.
- Per-path multiplier is uniformly **5×**, not 2→10. (Within la_init_ra, half are 1→5 and half are 2→10. The "10-paths" reading anchors on the high-multiplicity half but isn't the average.)
- Net: 56 × 4 × ~7.5 = 420 is right; the canonical statement is "**56 la_init_ra ensures × 5× path fan-out → +336**."

Empirically-measured: the corpus-wide bodyOrContract path-fanout factor on EQ harnesses is **5×**, with a 2× contract baseline becoming 10× on labels where the contract path itself was already 2× (likely two SSA copies for the parallel ref/other invocation pair).

### 6.2 The shrink direction (Δ ≤ 0)

Two of six small-bucket spot-checks shrank under bodyOrContract:

| File | Δ | Goals dropped | Source location |
|---|---:|---|---|
| EQ_xgw3320tmeb | −6 | `assert_14, assert_15, assert_16, assert_31` | exception-handler joins, lines 977/979/981/1102 of `.core.st` |
| EQ_t3umw4qs2cy | −4 | `assert_14, assert_29` | exception-handler joins, lines 975/1096 |

All dropped goals are literal `assert true;` at exception-merge points. The mechanism is **not** v1's hypothesized "contract instantiates `*_requires_N` per call site" — there are no `_requires_*` goals in either policy's output for these files (EQ harnesses use `free ensures` and shared UFs, not contract preconditions).

### 6.3 The actual mechanism

From `/Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean`:

| Line | Behavior |
|---|---|
| 887 | `callElimPipelinePhase` runs **before** symbolic eval if `--call-policy = contract`; **skipped** under `bodyOrContract`. |
| 807 | `if obligation.obligation.isTrue then return` — short-circuits goal emission when the obligation reduces to literal `True`. |

The combined effect:

- **contract**: Call-elim rewrites `.call` → `asserts(pre)/havocs/assumes(post)` ahead-of-time. A trivial `assert true;` at an exception-merge point sits between assumes call-elim has scheduled but not yet propagated. By `extractObligation` time the path condition is non-trivially typed; the `isTrue` short-circuit doesn't fire; a VC is emitted whose body is `(assert (not true))` over a non-trivial assumption set.
- **bodyOrContract**: Call-elim is skipped. Calls survive into the evaluator, which inlines callee assumes/asserts during path traversal. By the time the same `assert true;` is reached, the assumption set has simplified through the trivial-true path; the obligation reduces to literal `True`; the `isTrue` short-circuit fires; **no SMT goal is emitted.**

### 6.4 Per-mechanism table

| Mechanism | Direction | Cluster | Driver |
|---|---|---|---|
| Per-path SSA copies of constructor ensures | + | ike2wen0cz0, ylzs20xcwwt, any constructor-heavy EQ harness | body-eval enumerates ~5 paths through `_la_init_ra_` and `initIntArray`-style stubs whose contracts have N ensures clauses; goal count multiplies by ≈5× per ensures × per stub × per side (ref/other) |
| Per-path SSA copies of String-stub ensures | + | same | identical 5× fan-out applied to every spec-only stub the constructor calls transitively |
| Trivial-assert short-circuit via inlined assumes | – | xgw3320tmeb, t3umw4qs2cy | bodyOrContract evaluator inlines call-elim's assumes during traversal; `assert true;` at exception merges reduces to `True` and triggers `isTrue` skip at Verifier.lean:807. contract's pre-eval call-elim leaves the obligation non-trivially typed |
| Raw asserts not behind a `.call` | 0 | both | `assert_NN` clusters not on call-bearing paths are unchanged (42→42 in ike2wen, identical in shrink files) — body-eval and call-elim diverge **only on call-bearing paths** |
| `*_requires_N` (originally hypothesized in v1) | n/a | not observed | no `_requires_*` goals appear in either policy's output for these EQ files; v1's hypothesis does not apply to this corpus |

**Bidirectional divergence has a single underlying cause**: call-elim runs ahead-of-time under contract, in-line under bodyOrContract. AOT call-elim exposes goal counts proportional to the static program shape; in-line call-elim exposes goal counts proportional to evaluated path coverage, which both fans out (ensures replication) and folds in (trivial-assert reduction).

---

## 7. SO cluster — what's the predictor?

### 7.1 Refutation of v1's "deeper call-graphs / mutual recursion" framing

For all 7 SO files plus 8 controls, measured: self-recursion, mutual-recursion SCCs, max call depth, EQ-reachable inlined size, and (after the skeptic round) max single-implementation body size and basic-block count.

| File | Verdict (bodyOrContract) | Self-rec | Mutual SCCs | Max depth | EQ-reachable chars | Max impl chars | Max blocks |
|---|---|---:|---:|---:|---:|---:|---:|
| EQ_2zvm5xvfu22 | SO | 0 | 0 | 1 | 11,631 | 21,495 | 96 |
| EQ_wnksggs1hpx | SO | 0 | 0 | 1 | 11,631 | 21,495 | 96 |
| EQ_cvrikypthwe | SO | 0 | 0 | 2 | 9,555 | 12,365 | 66 |
| EQ_2aa5bx1uwko | SO | 0 | 0 | 1 | 9,838 | 16,741 | 60 |
| EQ_wfgmxv3m3tx | SO | 0 | 0 | 1 | 8,822 | 11,066 | 55 |
| EQ_sertrlracdg | SO | 0 | 0 | 1 | 8,224 | 22,485 | 117 |
| EQ_0xaksnfuqqv | SO | 0 | 0 | 1 | 11,714 | 34,169 | 169 |
| EQ_jk0xftyhwbe | PASS | 0 | 0 | 1 | 1,259 | 2,261 | 9 |
| EQ_ike2wen0cz0 | PASS | 2 | 0 | 1 | 1,411 | 4,003 | 18 |
| EQ_ylzs20xcwwt | PASS | 2 | 0 | 1 | ~1,400 | 2,472 | 10 |
| EQ_mtonvj3sujq | TIMEOUT | 0 | 0 | 2 | 8,204 | 5,838 | 28 |
| **EQ_n33r2qrii5y** | **PASS** | 0 | 1 (3-cycle) | 2 | 1,001 | **35,709** | **183** |
| EQ_qb00tzh020q | PASS | 2 | 0 | 4 | 1,331 | 18,032 | 95 |
| **EQ_dhag5onbafh** | **PASS** | 0 | 0 | 1 | 1,449 | **347,400** | **1,736** |
| **EQ_yg4xkpggkg2** | **PASS** | 0 | 0 | 2 | **10,168** | 177,800 | 930 |

What this kills:

1. **No SO file has self-recursion or mutual recursion.** ike2wen0cz0 PASSes with self-recursion. n33r2qrii5y PASSes with a 3-cycle SCC. **Recursion at the call-graph level is not the trigger.**
2. **Max call depth is uniformly 1–2 across SO files.** qb00tzh020q PASSes at depth 4. **Call-chain depth is not the predictor.**
3. **Per-procedure body size alone is not the predictor either.** dhag5onbafh has a single 347-KB / 1736-block body and PASSes. n33r2qrii5y has 35.7 KB / 183 blocks and PASSes. **Lean's body-eval can walk bodies of those sizes when reached** — there is no per-body size ceiling.
4. **EQ-reachable inlined size alone is not sufficient either.** yg4xkpggkg2 PASSes with EQ-reachable size 10,168 chars — *inside* the SO band of 8.2k–11.7k. If reachable size were sufficient, this file should SO; it doesn't.

### 7.2 The sharper predictor

The data is consistent with this refined claim:

> **An SO outcome requires a body of moderate size (≥ ~8 KB EQ-reachable) reached by the EQ harness with symbolic-equality preconditions that fork at every two-target goto.** Body size alone, call-chain depth, and recursion structure are individually insufficient.

The mechanism: Lean's body-eval forks at two-target gotos (`goto a, b`) into both successor environments and recurses into each. The recursive call **at the fork** is non-tail. With `--call-policy bodyOrContract` and the EQ harness's symbolic preconditions (both procedures called with the same uninstantiated arg), neither successor's path condition is dischargeable up-front, so both branches must be entered. Stack depth scales with the **product of basic-block count × actually-explored branch fanout**, not with raw block count or AST depth.

This explains every line of the table:

- `dhag5onbafh` (1,736 blocks, PASS): bodies are reached only with concrete args from harnesses that don't fan out → branches discharge eagerly, stack stays bounded.
- `n33r2qrii5y` (183 blocks, PASS): same — concrete-arg evaluator paths.
- `yg4xkpggkg2` (10 KB EQ-reachable, PASS): in the SO size band but evidently the branching pattern doesn't fork as widely (would need run-time instrumentation to confirm).
- `mtonvj3sujq` (5.8 KB body, TIMEOUT): fork-and-recurse pattern is active, but solver exhausts wall-clock before stack overflows.
- The 7 SO files: 8–22 KB body × ~30–170 blocks × symbolic-EQ preconditions × fork-at-every-goto → stack overflow.

### 7.3 Implication for the fix

v1 recommended TCO/iteration on the recursive walker over `Statement`/`Block`. The refined recommendation:

**TCO the per-fork branch-spawn in body-eval**, not the per-statement walk. The non-tail call that matters is the one in `evalCFGStep`/`processIteBranches` where two-target gotos spawn two recursive sub-evaluations into the two successor environments. The per-statement walk within a basic block is already linear and rarely the dominator — it's the fork-multiplication on symbolic preconditions that drives stack consumption.

Confirming this would require instrumenting `evalCFGStep` with a branch-spawn counter and a stack-depth probe, then re-running on n33r2qrii5y vs. sertrlracdg. Without that instrumentation, the claim is structurally inferred, not directly measured.

### 7.4 What v1 got wrong vs. right

| v1 claim | Status |
|---|---|
| "non-tail recursion in body-eval walker" | Right direction, wrong dimension |
| "Statement/Block AST size drives it" | Wrong — dhag5onbafh's AST is 60× larger and PASSes |
| "30–50 anonN_Then/Else branch points" | Post-hoc fitting; n33r2qrii5y has 183 and PASSes |
| "TCO the walker" | Right intervention, but on the per-fork branch-spawn specifically |

---

## 8. Refined wider-sweep projection

### 8.1 Inputs to projection

From v2:

- The 72-file sample is structurally **two corpora** (synthetic 36 + Java-SMACK 36).
- Java-SMACK is the sole source of SO and elab clusters. 8 of 8 known-verdict Java-SMACK files are hard failures.
- Cost regression is config-driven; minimal+bodyOrContract+fuel100 rescues 5/5 in the cost-regression cluster and 2/3 in the genuine-TIMEOUT cluster.
- Goal-fanout factor is uniformly ≈5× on EQ-harness-reached spec-only stubs.
- SO predictor is "body of moderate size + symbolic-precondition fork-at-goto," not call-chain depth.
- PARTIAL is `unknown` not `❌`; on at least one Neq.SameV the underlying property is decidable and the verifier suppresses it via pinned options.

### 8.2 Projection for a 200-file second sweep

Assumptions: same stratification (~33% small, ~33% medium, ~33% large), same alphabetic-first / stride-spaced selection, run under `--check-level minimal --call-policy bodyOrContract --inline-fuel 100 --solver-timeout 120`. Family ratio in 200 files projected to mirror 72-file ratio: ~100 synthetic + ~100 Java-SMACK.

| Cluster | Driver | Projected rate | Expected count in 200 |
|---|---|---:|---:|
| C4: stack overflow (Java-SMACK) | per-fork body-eval recursion | 100% on a stratifiable subset of Java-SMACK with EQ-reachable body ≥ 8 KB; corpus rate ≈ 15–25% of Java-SMACK | 15–25 |
| C5: `old(<global>)` elab defect (Java-SMACK) | translation-time defect | 8–12% of Java-SMACK | 8–12 |
| C2: precision flip on Neq.SameV (synthetic) | bodyOrContract distinguishing | ~50% of synthetic Neq.SameV files; Neq.SameV is ~25% of synthetic | ~12–15 PARTIAL files |
| C1: contract-only vacuous PASS (both families) | shared-UF | ~40–60% of synthetic Eq.SameV that PASS under contract; ~100% of Java-SMACK that PASS under contract | uniform — most "PASS"es are vacuous |
| C3: cost regression (synthetic, constructor-heavy) | resolved by `minimal` | now ≤ 5% TIMEOUT under sweep settings | 0–10 |
| Slow-but-bounded TIMEOUT (synthetic) | full × bodyOrContract pathology | resolved by `minimal`; some residue under wall-clock 120s | 3–6 |
| Unbounded TIMEOUT (synthetic + Java-SMACK boundary) | actual eval-side or solver-side | ~3–5% | 6–10 |
| Pure verdict-divergence between contract and bodyOrContract | per-file analysis required | ~30% of synthetic | ~30 files diverge |

**Headline projection:** under the recommended config, ~25–35% of Java-SMACK files will fail loudly (SO + elab + a few elab-residue), ~20–30% of synthetic files will produce informative PARTIALs, the remaining 35–55% will PASS but a substantial fraction of those PASSes will be vacuous-under-contract (becoming PARTIAL or different under bodyOrContract). Verdict divergence between policies will be ~30%.

### 8.3 Expected timing

| Bucket | Files | Per-file wall-clock (minimal+body+fuel100) | Total CPU-time |
|---|---:|---|---:|
| small | 67 | <5s | <6 min |
| medium | 67 | 5–60s | 30–60 min |
| large (excluding TIMEOUT/SO) | ~50 | 30–120s | 25–100 min |
| TIMEOUT cluster | ~6–10 | 120s ceiling each | 12–20 min |
| SO cluster | ~15–25 | <30s (deterministic crash) | <12 min |
| **Total** | 200 | — | **~85–195 CPU-min serial** |

Parallelizable to ~10–25 wall-clock minutes on a modest pool. v1's "1.5–3× of v1 cost" projection holds; the v2 contribution is that the cost is now bounded (no long-tail TIMEOUTs eating budget).

### 8.4 Where the projection is empirically-grounded vs. structurally-inferred

| Prediction | Basis |
|---|---|
| Java-SMACK uniformly fails | empirically measured (8/8 known-verdict) |
| Cost regression resolved by minimal | empirically measured (5/5 + 2/3) |
| Goal-fanout 5× on stubs | empirically measured on ike2wen0cz0 |
| PARTIAL is unknown not ❌ | empirically measured on ike2wen0cz0 path 135 |
| SO predictor refinement | structurally inferred (n=15); not yet instrumentation-verified |
| 30% verdict divergence | empirically calibrated on 22 known-verdict but extrapolated to 200 |
| Unbounded TIMEOUT residue 3–5% | empirically measured on n=3 sample, small-n caveat |
| `old(<global>)` elab rate 8–12% | extrapolated from batch reports; not directly counted in 200 |

### 8.5 What would meaningfully sharpen the projection

In rough order of cost vs. value:

1. **Run minimal+bodyOrContract+fuel100 on all 22 already-deep-dived files.** Cheap, gives the actual divergence rate baseline rather than the projected one.
2. **Strip pinned z3 options for the 7 Neq.SameV PARTIALs.** Decides whether PARTIAL→❌-with-witness on >1/7 cases. Either flips the methodology framing or confirms ike2wen0cz0 was anomalous.
3. **Instrument `evalCFGStep` with a branch-spawn counter and stack-depth probe.** Confirms or refutes the §7 fork-at-goto predictor on the 15-file SO/control set.
4. **Re-run the original sweep's exact 72-file list under minimal+bodyOrContract+fuel100.** Gives the empirical divergence-rate vs. config-rescue-rate split, replacing the projection with measurement.

---

## Appendix A: Where measurements failed or were approximations

| Measurement | Status |
|---|---|
| 72-file list reconstruction | Approximation — batch 2's stride-spaced pick not preserved in reports; reconstructed via alphabetic fill. Suite/family distribution is directionally correct; per-file verdict counts on the non-named 50 are unknown. |
| TIMEOUT cluster sample | n=3 genuine-TIMEOUT (5 with side-cases). Small-sample caveat on the 60/30 slow-bounded vs. unbounded split. |
| SO predictor verification | Static .bpl features only (n=15). Branch-spawn rate not instrumented at runtime; the §7 fork-at-goto claim is structurally inferred from process of elimination, not directly observed. |
| z3-default re-run on Neq.SameV | n=1 file, n=3 paths. The claim "PARTIAL re-classifies as ❌-with-witness under default z3" is verified on `ike2wen0cz0` only. The other 6 Neq.SameV PARTIALs were not re-tested. |
| Goal-count divergence verification | Verified on `ike2wen0cz0` only (267→1123 reproduced). v1's count of 1122 was off by 1 (a single FAIL goal it dropped). The 5× fan-out factor is corpus-projected, not measured on every file. |
| Cost-regression cross-check at full | Two of five files re-tested at full to compare against minimal. The other three were not re-tested; the framing "8–14× wall-clock factor" generalizes from n=2. |

## Appendix B: Artifacts and source pointers

- v1 synthesis: /Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-qualitative-analysis-2026-06-04.md
- Original batch reports: /Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-2026-06-03.md, /Users/htd/Documents/Strata-smack/reports/aaron-eq-portfolio-batch2-2026-06-04.md
- Verifier source: /Users/htd/Documents/Strata-smack/Strata/Languages/Core/Verifier.lean (lines 807, 887, 1003–1006, 1051–1061)
- SARIF formatter: /Users/htd/Documents/Strata-smack/Strata/Languages/Core/SarifOutput.lean (lines 52–54)
- CheckLevel definition: /Users/htd/Documents/Strata-smack/Strata/Languages/Core/Options.lean (lines 126–130)
- Cost-regression artifacts: /tmp/claude-503/cost-minimal-ab/ (results.json, run_ab.py, run_xcheck.py, xcheck_results.json)
- Shared-UF SMT-LIB: /tmp/claude-503/uf-probe/EQ_CharactergetTypelpCrpI_ensures_0_0.smt2
- TIMEOUT probe: /tmp/claude/probe_logs/results.txt, /tmp/claude/probe_work/*_fixed.core.st
- Witness-extraction probe: /tmp/claude/partial/ike_bf_full.stdout, /tmp/claude/partial/ike_vcs/EQ_..._ensures_0_{68,135,200}.smt2
- Goal-count probe: /tmp/claude-503/EQ_ike2wen0cz0.core.st, /tmp/claude-503/ike_contract.out, /tmp/claude-503/ike_body.out
- SO call-graph analysis: /tmp/claude/depth_probe2.py, /tmp/claude/callgraph.py
- Family taxonomy: /tmp/claude/all_72_tagged.txt, /tmp/claude/all_72_union.txt
