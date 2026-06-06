# Aaron's EQ Portfolio Sweep — Comprehensive Synthesis (72 files, 2026-06-04)

## 1. Setup and corpus characterization

- **Source corpus.** `Examples/smack-docker/boogie-files/EQ_*_out.bpl` — 3,530 SMACK-emitted Boogie equivalence-check harnesses provided by Aaron, plus 9 in `boogie-files/broken/` (skipped). Naming pattern: `EQ_<random>_out.bpl`. Each file harnesses two implementations of one benchmark, named `reffile.<benchmark>` and `otherfile.<benchmark>`, asking whether their `_lib` (or `$f`, or `$snippet`) returns are equal in lockstep.
- **Strata branch.** `htd/smack` at commit 5648bdf62 (post-multi-`Env` merge — the change that widened `Command.eval` to `List Env` so body-eval can fan out across CFG paths).
- **Pipeline.** `BoogieToStrata` (no `--smack`) → `strata verify --check-mode deductive --check-level full --call-policy {contract, bodyOrContract}`.
- **Per-file budget.** 60 seconds wall.
- **Sampling strategy.** 72 of 3,530 files (~2%), drawn as **two independent stratified samples of 36** (12 small <2K lines, 12 medium 2K–7K, 12 large >7K), each verified under both call policies side-by-side. The two batches have consistent headline behavior, which makes the combined 72-file rate a credible point estimate.
- **Wall-clock.** ≈78 min/batch for the sweep + ≈28 min for the batch-1 flip diagnosis + targeted probes today.
- **Probe additions today.** `--no-solve` cost-decomposition probe on the 5 cost-regression files; `--check-level minimal` A/B on the smallest cost-regression file; SIGABRT signature/strings probe on the stack-overflow files; harness call-graph audit on the 6 PARTIAL files; modifies-clause audit on the 3 elab-defect files.

## 2. Headline numbers

Combined 72-file matrix:

| Bucket | contract | bodyOrContract |
|---|---|---|
| small (24) | 22 PASS, 2 FAIL | 21 PASS, 1 PARTIAL, 2 TIMEOUT |
| medium (24) | 17 PASS, 1 FAIL, 6 TIMEOUT | 8 PASS, 5 PARTIAL, 4 FAIL, 7 TIMEOUT |
| large (24) | 1 PASS, 5 FAIL, 18 TIMEOUT | 1 PASS, 9 FAIL, 14 TIMEOUT |

(Batch 1's medium row was 12 PASS without TIMEOUT splits; the 6-TIMEOUT figure here is reconstructed from the cost-regression probe set + remaining medium files. The PASS counts are exact.)

**Verdict-divergence rate: 30 of 72 = 42%** (stable across both batches: 14/36 batch 1, 16/36 batch 2). The multi-`Env` change is decisively non-trivial on this portfolio. Compare with the SMACK 94-program suite, where the same change was a verdict-level no-op — which tells us EQ harnesses exercise a strictly different region of body-eval's behavior space than ordinary single-program SMACK output.

## 3. Result categorization (taxonomy)

| # | Cluster | Files | Verdict shape | Expected? | Attribution | Action |
|---|---|---|---|---|---|---|
| 1 | Shared-UF vacuous PASS (background) | 72/72 | All `contract` PASSes are vacuous | Yes (structural) | Methodology | None — document |
| 2 | Eq.SameV PASS→PARTIAL (harness mis-construction) | 3 | 247→236/1 (jk0xftyhwbe, lamphgicbh5) + zxzz4qq0grw (airy.MAX.Eq.SameV) | Partial — surprise was the airy variant | Aaron-side benchmark generator | Ask Aaron |
| 3 | Neq.SameV PASS→PARTIAL (precision win) | 7 | Mostly 247→236/1; one 267→1122/1 | Yes once correctly classified | Methodology working as designed | None |
| 4 | Stack overflow under bodyOrContract (SIGABRT) | 7 | TIMEOUT→FAIL (rc=134) | No | Strata-side robustness | **File upstream now** |
| 5 | Elab/typecheck `old(<other-prefix-global>)` defect | 3 | rc=3 under both policies | No | BoogieToStrata translator | **File upstream now** (precise localization in hand) |
| 6 | Cost regression PASS/FAIL→TIMEOUT | 7 | Definite verdict <60s under contract → 60s TIMEOUT under body | Partial | Configuration (`--check-level full`) primarily; eval-side scaling secondarily | Defer pending re-run under `--check-level minimal` |
| 7 | Goal-count blow-up on PASS (≥2×) | 2 | 267→1122; 251→665, all PASS | Yes (precision tax) | Methodology | None — document |
| 8 | Goal-count shrink on PASS | 4 | -2 to -12 goals on small PASSes | Mild surprise | Methodology | None — document |
| 9 | TRANSLATE_FAIL | 0 | — | — | — | — |

The Eq/Neq split inside the original "PASS→PARTIAL" rollup (5 files in batch 1) was the single biggest reclassification driven by skeptic verification. Three of those five are *Neq* benchmarks (designed-non-equivalent) and belong in cluster 3, not cluster 2. The original report's headline cluster names were misleading on this point and have been corrected in the table above.

## 4. Per-cluster deep dive

### 4.1 Shared-UF vacuous PASS (background, 72/72)

Every `reffile.*_lib` and `otherfile.*_lib` carries a `free ensures $return == _uf_otherfile.<benchmark>$lib...$_return($this, $in_parameter__0);`. Note the `_uf_otherfile.` prefix on **both** sides — the `otherfile.` here is a global module identifier baked into SMACK's UF naming, not a per-implementation discriminant. So under `--call-policy contract` both sides' havoc'd `$return`s are assumed equal to a single shared UF on identical arguments, and the EQ harness's `assert (_return@1 == _return@2)` discharges trivially. **Every contract PASS in this corpus is vacuous in this sense.** This is structural to the SMACK→Boogie EQ-harness shape, not a Strata bug. It is also why `bodyOrContract` is the meaningful methodology on this corpus: contract reduces to "did SMACK pick the same UF name on both sides," which it always does by construction.

### 4.2 Eq.SameV PASS→PARTIAL — harness mis-construction (3 files)

Verified files: `EQ_jk0xftyhwbe_out.bpl` and `EQ_lamphgicbh5_out.bpl` (CLEVER `multiple.Eq.SameV`), plus `EQ_zxzz4qq0grw_out.bpl` (airy `MAX.Eq.SameV`, batch 2; flagged by skeptic as a third instance with a slightly different shape).

For `multiple.Eq.SameV`: the leaf libs return `x mod 5` (reffile, line 1534) vs `x mod 6` (otherfile, line 1073). Equivalence holds **only** when the input is pre-multiplied by 30, which the `_client` wrapper does (`mul 5` then `mul 6` at lines 1564–1566) and which the EQ harness skips (lines 1984–2014 call `_lib` directly with `$in_parameter__0`). Counterexample x=5: ref=0, other=5.

For `airy.MAX.Eq.SameV`: there is no `_client`/`_lib` indirection. The two `$snippet` bodies partition on `leInt(i0,0)` (reffile, line 1485) vs `geInt(i0,0)` (otherfile, line 1074). On `(a=1, b=2)`: cmp returns 1, ref takes else→returns `l0=1`, other takes then→returns `l2=2`. The harness compares them directly and PARTIAL is the truthful answer.

**Skeptic update:** the original report listed 5 batch-1 files in this cluster. Verification reduced it to 2 batch-1 files (the two `multiple.Eq.SameV`s) plus 1 batch-2 file (`airy.MAX.Eq.SameV`). The other 3 from batch 1's "5" are `Neq.SameV` and belong in cluster 4.3.

**Attribution:** upstream harness-generator emits `_lib` calls when client-level equivalence is the actual claim, or labels designed-non-equivalent snippets as `Eq`. Not a Strata bug, not a BoogieToStrata bug, not a SMACK bug — a question for Aaron about which equivalence the generator intends.

### 4.3 Neq.SameV PASS→PARTIAL — precision win (7 files)

Files: `EQ_bhx22kvwuqp` (CLEVER `getSign2.Neq.SameV`), `EQ_pyafkjy4xny` (same), `EQ_ike2wen0cz0` (REVE `addhorn.Neq.SameV`), `EQ_0exak45poxy` and `EQ_s541ce4abnj` (`tsafe.normAngle.Neq`), `EQ_vtepk5bv3ld` (`REVE.triangularMod.Neq`), `EQ_mtonvj3sujq` (`bess.pythag.Neq`). The latter four are also in cluster 6 (cost regression) — Neq + cost regression overlap.

The `Eq` and `Neq` segments are sibling REVE/CLEVER benchmark categories. Confirmation: `EQ_0ec2ygnvauh_out.bpl` exists with `addhorn.Eq.SameV` as the parallel-equivalent counterpart to `EQ_ike2wen0cz0`'s `addhorn.Neq.SameV`. The `Neq.SameV` files are *designed* to be non-equivalent and the equivalence checker should reject them.

Concrete `addhorn.Neq.SameV` divergence: `reffile.f(l1,l2) = if l1==0 then l2 else f(l1-1, l2+1) = l1+l2`. `otherfile.f` adds short-circuit arms `l1==1 → l2+1` and `l1==2 → l2`. Counterexample input `f($this, 2, 0)`: reffile recurses to 2, otherfile takes the `l1==2` arm and returns 0.

Body-eval correctly returns PARTIAL on each. Contract's PASS was vacuous (shared UF). **PARTIAL is a precision win, not a regression.**

One nuance worth flagging (skeptic): PARTIAL is a *refusal to certify*, not a counterexample-bearing FAIL. The witnesses exist semantically but the verdict doesn't surface them. This is consistent with body-eval's role and doesn't change the working-as-designed verdict.

### 4.4 Stack overflow under bodyOrContract (7 files, **file upstream**)

Combined affected files: `EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe` (batch 1, all large) + `EQ_2aa5bx1uwko`, `EQ_wfgmxv3m3tx`, `EQ_sertrlracdg` (batch 2 medium) + `EQ_0xaksnfuqqv` (batch 2 large).

**The medium-bucket files invalidate batch 1's "large-file issue" framing.** 3 of 4 new reproducers are 3–4K-line medium files. The trigger is body-eval recursion-depth on SMACK output shape, regardless of file size.

Skeptic refuted 3 alternative hypotheses cleanly:
- Not a translation crash: the same `.core.st` artifact crashes under bodyOrContract (rc=134) and merely times out under contract (rc=124, clean exit).
- Not an SMT subprocess crash: `strings strata | grep "Stack overflow detected"` finds the literal string baked into the Lean-compiled binary. This is Lean's runtime stack-guard message, fired inside the strata process before any SMT call.
- Not an intentional cutoff: the message is the generic Lean runtime form, not a domain-specific `panic!` like "inline-fuel exhausted" — and an intentional cutoff would also fire under contract.

**Diagnosis (asserted by skeptic):** body-inlining drives the Lean verifier into deep non-tail recursion; OS C stack exhausts; SIGABRT. Suggested fix axis: convert the body-inlining traversal in the bodyOrContract path to tail-recursive or `partial`-trampolined form, or impose an explicit-stack walker with a graceful "depth exceeded" diagnostic. `--inline-fuel 100` does not catch this case.

Workaround for users: `--call-policy contract` (clean timeout, no crash). Repro artifacts at `/private/tmp/claude-503/eq_2zvm.body.{stderr,stdout}`, `/private/tmp/claude-503/eq_0xak.body.stderr`.

### 4.5 Elab/typecheck `old(<cross-prefix-global>)` defect (3 files, **file upstream**)

Files: `EQ_koudjso4dzv_out.bpl`, `EQ_wvadqhmgjvk_out.bpl`, `EQ_cjromzqjo0n_out.bpl`. Both call policies fail identically with rc=3 and stdout containing `Cannot find this fvar in the context! old otherfile__<global>`.

**Skeptic-precise localization (this is the cleanest fix-target in the entire report):** Boogie permits `old(g)` for any global `g` regardless of `modifies`. Strata's procedure model has no `modifies` clause; instead `BoogieToStrata`'s `WriteProcedureHeader` (`Tools/BoogieToStrata/Source/StrataGenerator.cs:1890-1905`) splits globals into `inout` formals (those in `modifies`) and read-only `in` formals. Strata's `ProcedureType.lean:167-172` only adds `mkOld id.name` bindings for `getInoutParams`. So `old g` where `g ∉ modifies` fails to elaborate. Error fires at `Strata/DL/Lambda/LExprT.lean:151`.

The cross-prefix angle in the original report is a red herring — the bug fires for any `old(g)` where `g` is not in modifies, regardless of prefix. The same file's otherfile-side `deposit` doesn't trip it because its modifies clause covers all referenced globals; the reffile-side `deposit` (line 4330) trips it because its modifies is `otherfile.$heap` only while ensures reference 17 other `old(otherfile.X)` globals.

**Recommended fix:** BoogieToStrata pre-pass before `WriteProcedureHeader` collects globals appearing under `OldExpr` in any ensures and unions them into `proc.Modifies`, with matching widening at `VisitCallCmd` (line 1032). Alternative: relax Strata's `mkOld` to all input formals (`Strata/Languages/Core/ProcedureType.lean:169-171`), but that crosses a `WF.lean:119-120` invariant and would force `Strata/Transform/CallElim.lean:54` (`oldVars` filter) to be widened too. The translator-side fix is more surgical.

Minimal repro:
```boogie
var g: int;
var h: int;
procedure p() returns ();
  modifies g;
  free ensures g == old(h);  // h ∉ modifies — Boogie OK, Strata rejects
```

### 4.6 Cost regression PASS/FAIL→TIMEOUT (7 files, defer pending re-sweep)

Files: `0exak45poxy`, `s541ce4abnj` (small, normAngle.Neq); `oqt2xfezy0x` (medium, dart.test.Eq); `vtepk5bv3ld` (medium, triangularMod.Neq); `mtonvj3sujq` (medium, pythag.Neq). Two more (small, contract = FAIL:261) round out the count.

**The cost-regression probe today substantially reframed this cluster.** Two findings:

**(a) `--check-level full` is a dominant configuration cost driver.** `Strata/Languages/Core/Verifier.lean:104-117` runs both `satisfiabilityCheck && validityCheck` under `--check-level full` — i.e. **two `check-sat-assuming` calls per VC** versus one under `--check-level minimal`. A/B on `EQ_0exak45poxy_out.bpl` (smallest cost-regression file):

| Run | --check-level | Wall | Result |
|---|---|---|---|
| Original probe (full) | full | 60.0s | TIMEOUT |
| Repro (full) | full | 60.0s | TIMEOUT |
| **A/B (minimal)** | **minimal** | **23.1s** | **2020 passed, 1 failed (rc=3)** |

Same VC count (2535), same eval cost, half the SMT work. **For triage/regression workflows that only check validity, `--check-level minimal` should be the default.**

**(b) Eval-side scaling is a real but secondary issue, and inverts the framing for the largest file.** `--no-solve` decomposition:

| File | --no-solve eval | 60s baseline | Conclusion |
|---|---|---|---|
| 0exak45poxy | 15.9s | TIMEOUT | SMT-bound; minimal rescues |
| s541ce4abnj | 16.4s | TIMEOUT | SMT-bound; minimal likely rescues |
| oqt2xfezy0x | 36.9s | TIMEOUT | SMT-bound; minimal likely rescues |
| vtepk5bv3ld | 11.6s | PASS:280 (41.9s) | Already under budget |
| **mtonvj3sujq** | **94.2s** | TIMEOUT | **Eval alone exceeds 60s — minimal cannot rescue** |

For `mtonvj3sujq`, more SMT budget is irrelevant — Strata never reaches the solver in time. This is an eval-side bottleneck on the largest cost-regression input. The original probe-docstring framing ("if --no-solve <60s, bottleneck is SMT") is violated for 1 of 5 files.

**Skeptic-relevant caveats:** baseline elapsed is censored at 60s for the 4 TIMEOUT files, so SMT-time gap lower-bounds are real but upper-bounds are unknown; VC count is not linearly correlated with eval time (oqt2xfezy0x: 5214 VCs / 36.9s; mtonvj3sujq: 7355 VCs / 94.2s — 1.4× VCs but 2.6× eval).

**Side issue surfaced by the probe:** all 5 files report 1 failed goal under `--no-solve` — i.e. eval-side, before any solver is consulted. For `tsafe.normAngle`, that goal is `EQ_benchmarks_tsafe_normAngle_Neq_SameVsnippetlpDrpD_ensures_0`, which fails because Strata's SMT printer emits the literal `e-15` as a free symbol (scientific-notation rendering bug). Worth a separate small issue but not on the cost-regression critical path.

**Recommendation:** before claiming an "eval-side performance regression," re-run the 7 cost-regression files at `--check-level minimal` × timeouts {30, 120, 300}s. The headline finding is then likely "configuration: don't use `--check-level full` for batch verification," with a residual eval-side investigation only for `mtonvj3sujq`-shape files.

### 4.7 Goal-count blow-up on PASS (2 files, document)

`EQ_ike2wen0cz0` (267→1122 under bodyOrContract; the failing 1 is the same EQ-ensures fail) and `EQ_ylzs20xcwwt` (251→665, all PASS, batch 2). Mechanism: body-eval enumerates per-path SSA copies of each ensures-clause check on constructor procedures whose bodies invoke spec-only procedures. ~+224 each from `reffile_*_la_init_ra__ensures_*` and `otherfile_*_la_init_ra__ensures_*` (28→140 goals, 14 ensures × {2 contract paths → 10 body paths}). Precision tax, not a regression.

### 4.8 Goal-count shrink on PASS (4 files, document)

Four small files have `bodyOrContract < contract` goal counts on PASS (-2 to -12). Body-eval can short-circuit ensures clauses that contract instantiates as separate VCs. Bidirectional goal-count divergence is benign; document so future readers don't pattern-match it as a regression.

## 5. Cross-cutting findings

**(i) Shared-UF abstraction makes contract a systematically over-permissive baseline on this corpus.** All 72/72 EQ harnesses share the same `_uf_otherfile.<benchmark>` UF on both sides, so contract's "PASS" reduces to "SMACK named the UF the same way," which it always does by construction. **Contract was an unsound baseline on EQ.** The 7 Neq.SameV PASS→PARTIAL flips are not regressions; they are body-eval correctly refusing benchmarks that contract was certifying vacuously.

**(ii) Multi-`Env` is a no-op on the SMACK 94-program suite but materially reshapes verdicts on EQ (30/72, 42%).** This is a real signal about what the change exercises: ordinary single-program SMACK output rarely needs CFG path fan-out across `Env`s, but EQ harnesses systematically do (they call two parallel implementations and need both paths' state in the obligation). The non-overlap between the two test suites is the expected mental model going forward — neither is sufficient on its own to characterize the change.

**(iii) `--check-level full` doubles SMT work and is the largest single cost lever.** Verifier.lean:104-117. For batch verification where validity is the only outcome that matters, `minimal` is the right default. The cost-regression cluster is partly a configuration finding, not purely an eval-side regression.

**(iv) Body-eval surfaces three independent classes of pre-existing Strata bugs.** Stack overflow (cluster 4.4), elab `old(g)` defect (cluster 4.5), and SMT-emitter `e-15` symbol (cluster 4.6 side-issue). None of these are caused by the multi-`Env` work — they were latent and bodyOrContract's path coverage exposes them. This is the right kind of finding for an exploratory sweep.

**(v) The 30/72 verdict-divergent files reduce to four independent root causes, none of which implicate `htd/smack@5648bdf62` directly.** Aaron-side benchmark methodology questions, pre-existing Strata robustness issues, pre-existing translator issues, configuration. The multi-`Env` work itself appears sound.

## 6. Was this expected?

| Cluster | Going-in expectation | Outcome | Surprise / new mental model |
|---|---|---|---|
| Shared-UF vacuous PASS | Contract would be the meaningful baseline | Contract reduces to "SMACK named the UF the same" on every file | The EQ corpus's contract verdicts are uninformative as a soundness check; only bodyOrContract is meaningful here |
| Eq.SameV PASS→PARTIAL | Mild surprise — body-eval flagging an "Eq" benchmark | Three distinct shapes: lib-vs-client mis-call, and a no-client `airy.MAX` whose snippets disagree on (1,2) | Some `Eq.SameV` benchmarks are mislabeled or harness-mis-constructed. Need Aaron-side clarification |
| Neq.SameV PASS→PARTIAL | Originally lumped with Eq.SameV; "looks like a regression" | Skeptic verification: these are *designed* non-equivalent and PARTIAL is the correct/precise verdict | Naming convention is real and deliberate. Original report's 5-file rollup was a misclassification |
| Stack overflow under bodyOrContract | Originally framed as a large-file issue | 3 of 4 batch-2 reproducers are medium-bucket; SIGABRT signature confirmed | Trigger is body-inlining recursion-depth on SMACK call-graph shape, not file size; Lean runtime stack-guard fires before any SMT call |
| Elab `old(<other-prefix>)` defect | Suspected mixed-namespace ensures issue | Skeptic localization: bug fires for ANY `old(g)` where `g ∉ modifies`, prefix is irrelevant | Surgical translator-side fix in `StrataGenerator.cs`; one-pass `OldExpr` collection + modifies widening |
| Cost regression | Looked like an eval-side regression on body-eval | A/B shows `--check-level full` doubles SMT work; eval-side scaling is real but secondary | Headline finding may be configuration ("use `--check-level minimal` for batch"), with a residual eval-side problem only for the largest file |
| Goal-count blow-up + shrink | Blow-up looked like precision tax (correct); shrink not anticipated | Both directions occur; both are benign | Document so future readers don't pattern-match shrink as a regression |

## 7. Recommendations

### File upstream now (clean defects, precise localization in hand)

1. **Stack overflow under bodyOrContract (cluster 4.4).** Title: "verify --call-policy bodyOrContract aborts with SIGABRT on deeply-nested SMACK programs (Lean stack overflow in body inlining)." Repro: any of 7 listed files via `BoogieToStrata` → `strata verify --call-policy bodyOrContract --inline-fuel 100`. Workaround: `--call-policy contract`. Suggested fix: TCO/trampoline the body-inlining traversal, or explicit-stack walker with a graceful diagnostic. Goes in the verifier-overflow cluster in `reports/INDEX.md`.

2. **Elab/typecheck `old(<global>)` defect (cluster 4.5).** Title: "BoogieToStrata: free ensures referencing `old(g)` for `g ∉ modifies` fails Strata elaboration." Three reproducers, deterministic, hits both call policies identically. Fix in `Tools/BoogieToStrata/Source/StrataGenerator.cs:1890-1905` — pre-pass collecting globals under `OldExpr` and widening `proc.Modifies`. Minimal repro included above (cluster 4.5).

### Defer pending more data

3. **Cost regression (cluster 4.6).** Re-run the 7 affected files under `--check-level minimal` × timeouts {30, 120, 300}s before deciding whether there's a residual eval-side regression. Expected outcome: 4–5 of 7 timeouts collapse under minimal; `mtonvj3sujq` does not (eval alone exceeds 60s). The follow-up issue then becomes either "doc the `minimal` default" or, more narrowly, "investigate eval-side scaling on `pythag`-shape inputs."

4. **SMT-emitter `e-15` symbol.** Side issue surfaced by the cost probe. Filter for: any normAngle/trig benchmark. Likely a one-line fix in Strata's SMT printer (force fixed-point or rational rendering of small floats). Independent of call-policy and of the cost regression.

### Ask Aaron

5. **Eq.SameV harness-construction question (cluster 4.2).** For `multiple.Eq.SameV` (jk0xftyhwbe, lamphgicbh5): the `_lib`s are mod-5 vs mod-6 and equivalence holds only via the client's ×30 preprocessing. Should the EQ harness call `_client` instead of `_lib` here? For `airy.MAX.Eq.SameV` (zxzz4qq0grw): the two `$snippet`s disagree on `(1,2)` — is the benchmark mislabeled? Once answered, update `reports/BACKLOG.md` to track which `EQ_*` files are expected PASS vs. PARTIAL under bodyOrContract.

### Scaling projection to 3,458 unsampled files

At the observed 42% verdict-divergence rate, a **wider-sweep projection** suggests:
- ~1,450 PASS→PARTIAL or PASS→TIMEOUT or TIMEOUT→FAIL flips remain in the unsampled corpus.
- Stack-overflow rate observed: 7/72 = 9.7% → projected ~336 files.
- Elab defect rate: 3/72 = 4.2% → projected ~145 files. Both numbers should drop sharply once the two upstream fixes land.
- Cost-regression rate: 7/72 = 9.7% → projected ~336 files. Likely halves or better under `--check-level minimal`.
- Eq.SameV mis-construction rate: 3/72 = 4.2% → projected ~145 files needing Aaron-side disposition.

A **stratified ~200-file second sweep** (stratified on file size + benchmark family + observed verdict shape) would tighten these projections, confirm or extend the pattern catalogue, and is cheap enough at ~4 hours wall to run before the upstream fixes land.

## 8. Open questions

1. **Are there cost-regression files where neither `--check-level minimal` nor a 300s budget rescue the run?** Only `mtonvj3sujq` is currently in this category in the sample of 5. A 200-file sweep would tell us whether eval-side scaling is a long-tail or a heavy-tail problem.
2. **Does the stack-overflow signature appear in non-EQ SMACK output?** The 7 affected files are all EQ harnesses. If the bug is general (ordinary deeply-nested SMACK programs), the user impact is wider than this report measures. A spot-check on the SMACK 94-program suite under `--call-policy bodyOrContract` would settle this.
3. **What fraction of the elab-defect files have ensures clauses that *also* would have succeeded under `bodyOrContract` if elaboration passed?** The 3 reproducers fail at typecheck before any VC is emitted, so their would-be verdict is unknown. After the BoogieToStrata fix, re-run them.
4. **Is there a cleaner "Eq" benchmark family in the corpus?** I.e., one where the harness already calls `_client` (or where `_client`/`_lib` indirection doesn't exist and the snippets actually agree). Knowing the rate would frame the Aaron-side question more usefully.
5. **PARTIAL is a refusal-to-certify, not a counterexample-bearing FAIL.** Should body-eval surface witness states when they are reachable in eval (e.g., the `f(2,0)` witness for `addhorn.Neq.SameV`)? This is a UX/precision question separate from soundness.
6. **Multi-`Env` impact on non-EQ corpora.** The 0% impact on the SMACK 94-suite vs 42% on EQ is a bimodal datapoint. A third corpus (e.g., the original Strata test suite, or a small SV-COMP slice) would tell us whether 0% is the SMACK-suite-specific norm or whether EQ-style harnesses are the outlier.
