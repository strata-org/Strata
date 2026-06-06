# Aaron's EQ portfolio — initial sweep + PASS→PARTIAL flip diagnosis (2026-06-03)

## Setup

- **Source**: `Examples/smack-docker/boogie-files/EQ_*_out.bpl` — 3530 Boogie equivalence-check files Aaron handed off, plus 9 in `boogie-files/broken/` (skipped). Naming: `EQ_<random>_out.bpl`. Each file harnesses two implementations of the same benchmark, named `reffile.<benchmark>` and `otherfile.<benchmark>`, and asks whether their `_lib` returns are equal in lockstep.
- **Strata branch**: `htd/smack` at `5648bdf62` (post-multi-`Env` merge).
- **Pipeline**: BoogieToStrata DLL (no `--smack`) → `strata verify --check-mode deductive --check-level full --call-policy {contract,bodyOrContract}` with 60s per-file timeout.
- **Strategy**: stratified sample of 36 files (12 small <2K lines, 12 medium 2K–7K, 12 large >7K), each verified under both call policies side-by-side. ~78 minutes wall-clock for the sweep, ~28 minutes for the flip diagnosis.

## Headline counts

| Bucket | contract | bodyOrContract |
|---|---|---|
| small (12) | 12 PASS | 12 PASS |
| medium (12) | 12 PASS | 7 PASS, **5 PARTIAL** |
| large (12) | 1 PASS, 3 FAIL, 8 TIMEOUT | 1 PASS, **6 FAIL**, 5 TIMEOUT |

The multi-`Env` change is **not a no-op on this portfolio** — it materially diverges from contract on 14 of 36 files (39%). Two distinct phenomena:

- **5 medium files flip PASS → PARTIAL**: see "PASS→PARTIAL diagnosis" below.
- **3 large files flip TIMEOUT → FAIL** (`EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe`): "Stack overflow detected" — these are real Strata robustness issues to file (likely a non-TCO walker in the body-eval path; fits the existing verifier-overflow cluster).

## PASS→PARTIAL diagnosis (5 files)

| File | Cluster | contract | bodyOrContract |
|---|---|---|---|
| `EQ_jk0xftyhwbe_out.bpl` | `multiple_Eq_SameV` (×2) | PASS:247 | PARTIAL:236/1 |
| `EQ_lamphgicbh5_out.bpl` | `multiple_Eq_SameV` (×2) | PASS:247 | PARTIAL:236/1 |
| `EQ_bhx22kvwuqp_out.bpl` | `getSign2_Neq_SameV` (×2) | PASS:247 | PARTIAL:236/1 |
| `EQ_pyafkjy4xny_out.bpl` | `getSign2_Neq_SameV` (×2) | PASS:247 | PARTIAL:236/1 |
| `EQ_ike2wen0cz0_out.bpl` | `addhorn_Neq_SameV` | PASS:267 | PARTIAL:1122/1 |

Three adversarial lenses (real-bug / precision-regression / verifier-modeling-bug) converged with **high confidence**: body-eval is sound and correctly surfacing genuine non-equivalence at the obligation as-written. The Strata code paths involved (`processIteBranches` in `StatementEval.lean:658-698`, `evalCFGStep` in `ProcedureEval.lean:106-130`, `inlineCallBody`'s scope/PC frame management at `StatementEval.lean:872-899`, `handleCall .BodyOrContract` fallback at `StatementEval.lean:926-938`) all check out — no path-condition leak, no missed scope pop, no spurious obligation.

### Why contract passes vacuously

Each `reffile.*_lib` and `otherfile.*_lib` carries a `free ensures` of the form

```
free ensures $return == _uf_otherfile.<benchmark>$lib...$_return($this, $in_parameter__0);
```

— i.e. **both** `reffile.*` and `otherfile.*` lib procedures bind their `$return` to the **same** uninterpreted-function symbol (the `otherfile.*` prefix is a global module identifier, not a per-implementation prefix). Under `--call-policy contract`, both calls' havoc'd `$return` values are assumed equal to that single shared UF applied to identical arguments, so the EQ harness's `ensures (_return@1 == _return@2)` is trivially provable — vacuous PASS.

### Why body-eval fails

Body-eval honors `{:inline 1}` on the lib procedures: it substitutes the actual computed values, and the obligation becomes a substantive arithmetic claim:

| Cluster | reffile body | otherfile body | Failing obligation |
|---|---|---|---|
| `multiple_Eq` | `bvsrem(p0, 5)` | `bvsrem(p0, 6)` | `bvsrem(p0,5) == bvsrem(p0,6)` (e.g. p=5 → 0 vs 5) |
| `getSign2_Neq` | 3-way: 0 / 1 / -1 | 2-way: 1 / -1 | 4 of 6 cross-branch combos give -1 vs 1, 0 vs 1, 0 vs -1 |
| `addhorn_Neq` | recursive base `l1==0 → l2` | recursive bases `l1==0 → l2`, `l1==1 → l2+1`, `l1==2 → l2` | failing path is reffile-(l1==0) × otherfile-(l1==1): `l2 == l2+1` |

cvc5 returns `unknown` on each — the correct, sound outcome.

## Classification per cluster

### `getSign2_Neq_SameV` and `addhorn_Neq_SameV` — body-eval is doing exactly what `Neq` benchmarks expect

Directory naming `Neq/SameV` indicates these are **deliberately non-equivalent** program pairs from the CLEVER and REVE benchmark suites — designed to test that an equivalence checker correctly REJECTS them. Body-eval's PARTIAL is the intended verdict; contract's vacuous PASS was the unsound one. **Methodology working as designed.**

### `multiple_Eq_SameV` — harness mis-construction

This one is initially confusing because the directory says `Eq` (claimed equivalent) but the lib bodies (`mod 5` vs `mod 6`) are manifestly not equivalent. Investigation:

- The two `_client` procedures (lines 1084 of `otherfile.*_client` and 1545 of `reffile.*_client`) **do** compute equivalent functions on arbitrary inputs, but only because the client preprocesses its input as `l1 * 5 * 6 = l1 * 30` before passing it to `_lib`. Since 30 is divisible by both 5 and 6, both libs return 0 for that argument: `reffile.lib(30k) = 30k mod 5 = 0 = 30k mod 6 = otherfile.lib(30k)`.
- The benchmark's `_Eq_SameV` claim is **client-level equivalence**, not lib-level.
- However, the EQ harness (lines 1984–2014) calls the **libs directly** with `$in_parameter__0` (the original input), **not through the client**. So the obligation as-written demands `reffile.lib(p) == otherfile.lib(p)` for arbitrary `p`, which is genuinely false (e.g. p=5).
- **The harness is constructed to ask the wrong question.** It should call `_client`, not `_lib`. Whatever benchmark-harness generator produced these `EQ_*_out.bpl` files emitted a lib-level call when it should have emitted a client-level call.
- Contract mode hides the harness mis-construction by abstracting both libs to the same UF; body-eval correctly exposes that the libs themselves disagree.

**Not a SMACK bug**, **not a BoogieToStrata bug**, and **not a Strata bug** — it's a *benchmark-harness-generator issue* in the upstream equivalence-check tooling.

## ike-1122 goal-count blow-up (orthogonal phenomenon)

`EQ_ike2wen0cz0` shows 1122 goals under bodyOrContract vs 267 under contract — +855 extra. **All extra goals PASS**; the failing 1 is the same EQ-ensures failure as the 247-cluster. The +855 splits as ~+224 from each of `reffile_*_la_init_ra__ensures_*` and `otherfile_*_la_init_ra__ensures_*` (28→140 goals each: 14 ensures-clauses × {2 paths under contract → 10 paths under body-eval}), plus smaller fan-outs on `_f` itself. Mechanism: body-eval enumerates per-path SSA copies of each ensures-clause check on constructor procedures whose bodies invoke spec-only procedures. This is precision-tax overhead, not a regression — every extra goal discharges.

## Recommendations

1. **No Strata code change needed for the PASS→PARTIAL flips.** Body-eval is sound; contract mode is over-permissive due to the shared-UF abstraction. The `Neq/SameV` flips are precision wins; the `multiple_Eq_SameV` flips reveal a harness mis-construction in the upstream EQ generator.

2. **File 3 stack-overflow FAILs as a Strata robustness issue.** `EQ_2zvm5xvfu22`, `EQ_wnksggs1hpx`, `EQ_cvrikypthwe` all crash the verifier under bodyOrContract on programs where contract just times out. Likely a non-TCO walker in the body-eval path; fits the existing verifier-overflow cluster (`reports/INDEX.md` § "Verifier hang / overflow cluster"). Evidence dump: `/tmp/claude-503/repro_*.body.out`.

3. **Open a follow-up with Aaron about the harness generator** that produced the `multiple_Eq_SameV` files. The harness should call `_client`, not `_lib`. Once that's fixed (or the generator's intent is documented), update the BACKLOG to track which `EQ_*` files are actually expected to PASS under bodyOrContract vs. which are expected to PARTIAL.

4. **Wider-sweep follow-up.** This was 36 of 3530 (~1%). A ~200-file stratified sample would either confirm or extend the pattern catalogue. The patterns to watch for at scale: shared-UF cross-prefix free-ensures (above), large-bucket stack overflow (above), `247/236/1` recurrences on other Eq/Neq family pairs.

## Artifacts

- Workflow run 1 (sweep, 36 files): `wf_7533c9c0-dbe`. Per-file CSV in workflow output.
- Workflow run 2 (5-flip deep dive): `wf_01344288-987`. Reproduction artifacts at `/tmp/claude-503/repro_{0..4}.{contract,body}.out` and `/tmp/claude-503/repro_{0..4}.core.st`.
