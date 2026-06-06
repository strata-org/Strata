# Methodology note: what we've found running your EQ_*_out corpus

Hi Aaron — short note on what we've learned running your equivalence-checking
corpus through Strata's verifier, and a few things that would help us interpret
the results going forward.

## 1. Why contract-only was the wrong baseline on this corpus

The first batch of runs we sent you were under `--call-policy contract`, where
each procedure call is summarized by its declared `requires/ensures` pair and
the body is never inlined. On EQ benchmarks specifically that policy is almost
always vacuous: the equivalence harness calls a `_lib` (or `_client`) procedure
on each side, and contract-only abstracts both calls by *the same* uninterpreted
function. The harness's "do these two implementations agree" question then
collapses to "does this UF agree with itself," which trivially passes.

We measured the vacuous-PASS rate on a 22-file deep-dive sample (your CLEVER /
REVE / dart / bess / Java-SMACK families, two runs per file with policy in
`{contract, bodyOrContract}`):

- Strict verified flips (contract-PASS becomes non-PASS once bodies are
  expanded): **13 of 16 = 81%**, Wilson 95% CI [57%, 93%].
- Including a confirmed compound-vacuous case (Δ=0 body-eval, both policies
  generated the identical 138 UF goals): 14/16 = 87.5%.

The skew is also family-dependent: 6 of 6 Java-SMACK contract-PASSes flipped
under bodyOrContract (100%), 6 of 7 CLEVER+REVE+dart+bess synthetic
contract-PASSes flipped, and only 2 REVE files yielded substantive both-PASS
verdicts that look like real proofs.

Going forward, we will report `--call-policy bodyOrContract` as the meaningful
verdict and treat contract-only as a translation-shadowing baseline. Apologies
for any confusion the earlier numbers caused — they over-counted PASSes by
roughly 4-5x on this corpus.

## 2. Three things we'd appreciate clarification on

These are benchmark-design questions where a one-line answer from you would
unblock our interpretation.

### (a) `multiple_Eq_SameV` (jk0xftyhwbe, lamphgicbh5): is the harness calling the right side?

In both files the EQ harness calls `_lib` on each side, not `_client`. Under
bodyOrContract the verifier reports a counterexample on the `_lib` body. We
cannot tell from the Boogie alone whether the intended check is "the two
`_lib` implementations agree" (in which case the counterexample is a real find)
or "the two `_client` implementations agree, mediated by `_lib`" (in which case
the harness is mis-wired and we should be calling `_client`). Which is it?

### (b) `airy.MAX.Eq.SameV`: is this benchmark really equivalent?

The two `_lib` bodies disagree on the input pair (1, 2): one returns 2, the
other returns 1. Either the labeling (`Eq.SameV`) is wrong, or one of the two
bodies has been transformed in a way that wasn't intended to be
behavior-preserving. Worth a sanity check on your generator.

### (c) `Neq.SameV` benchmarks: designed non-equivalent at which level?

For files like `addhorn.Neq.SameV`, `pythag.Neq.SameV`,
`triangularMod.Neq.SameV`, `normAngle.Neq.SameV`, we find SAT witnesses on every
ensures_0 path under default-options Z3 (3/3 on ike, 9/9 on mtonvj, 6/6 on bhx,
5/5 on each of the two normAngle files). In other words, Z3 readily produces
concrete inputs at which the two sides differ. Are these benchmarks designed to
be non-equivalent at the `_lib` body level (so finding a witness is the correct
verdict), or only at the `_client` / harness level (so a `_lib`-level witness
means the harness is exposing internal divergence rather than the intended
property)? Same question as (a) but for the negative cases.

## 3. What our pipeline now reports on your corpus

Two recent fixes are worth noting because they substantially changed our
results compared to what we sent earlier:

- A stack-overflow fix (Strata-side, commit 277c468cb) for deeply-nested
  expressions surfaced by `--smack` translation. With this in place, no Java-
  SMACK file in our 28-file stratified sample stack-overflows.
- A non-standard scientific-notation literal (`3141592653589793e-15`) emitted
  by the Strata SMT-LIB writer was being rejected by both default Z3 and
  default cvc5 as a parse error. We've patched it locally; the upstream bug
  is what was masquerading as `❓ unknown` on the two `tsafe.normAngle.Neq.SameV`
  files.

On a 28-file size-stratified Java-SMACK sample (134 KB → 12 MB Boogie, post-
fix, 90 s verify wall): 25% real PASS (133 → 2,133 VCs each, no
`path unreachable`), 3.6% PARTIAL (one Z3-undecidable goal out of 21,784), 50%
TIMEOUT (almost monotone in file size), 21% type-elaboration failure with a
single shared root cause (`old`-of-fvar on a non-modifies state variable
referenced by an `_ensures_0` clause — distinct from previously-reported issue
#1162). No SO regressions, no panics. Java-SMACK is therefore not the uniform
hard-failure cohort we'd previously characterized it as; it has a real PASS
fraction once you control for file size and the `old`-of-fvar elab issue.

## 4. Suggested action on the harness side

If your generator is re-runnable, the single change that would most clarify
our results is to thread `_client` calls (not `_lib` calls) through the EQ
harness on both sides. As it stands, we cannot distinguish between

- a real `_lib`-level non-equivalence in your benchmark, and
- a precision-tax artifact where bodyOrContract exposes intermediate state
  the contract was designed to abstract away,

because both manifest as "bodyOrContract finds a counterexample on `_lib`."
With the harness routed through `_client`, a counterexample at the `_client`
level is unambiguously a real find against the intended specification, and a
PASS at the `_client` level is unambiguously a real proof.

If regeneration isn't practical, an alternative would be a tag in the
benchmark metadata indicating, per-file, whether the equivalence claim is at
the `_lib` or `_client` granularity. That would let us classify our verdicts
correctly without changing the `.bpl` output.

Happy to share the per-file artifacts (SMT-LIB witnesses, verifier logs)
for any of the cases above.
