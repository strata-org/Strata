# W3: PcInversion.lean local-reduction audit

## Plan

`Strata/Backends/CBMC/GOTO/PcInversion.lean` is 1,580 LoC. L2's design audit
classified its `BodyPcCovered` step as Class E (5+ auxiliary hypotheses per
step) and recommended skipping the `BlocksFoldClosed` combinator port. This
audit looks for **local** reductions that don't require the combinator:
near-duplicate step lemmas, dead `private theorem`s, verbose tactic chains,
repeated hypothesis bundles, and `Option.some.inj/subst` patterns that
`inj_subst` (from `Strata.Backends.CBMC.GOTO.Tactics`) could compress.

Threshold: only apply opportunities saving ≥10 LoC each. If the running total
is <30 LoC by the halfway mark, declare Tier 3 (file already lean) and stop.

## Findings

(stub — to be filled in)
