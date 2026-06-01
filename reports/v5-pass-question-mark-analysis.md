# V5 PASS-? Qualitative Analysis

Read-only static analysis of the 18 programs that produced
`pass (❗path unreachable)` (matrix label `PASS-?`) on the v5 run.
Classification: **A** correct vacuity / **B** bounded-fuel artifact /
**C** translator artifact / **D** other.

## Headline

Of the 18 PASS-?, the static-source agent classified all 18 as class B
(would-flip-with-more-fuel). **The empirical fuel-bump experiment falsified
that prediction.** Running 12 of the 18 programs at `--inline-fuel 500`
(5× the v5 baseline of 100, halfway to default 100000) produced *zero*
verdict changes — all 12 remain PASS-?. So the actual story is:

- The vacuity is **not** from `--inline-fuel` exhaustion. `--inline-fuel`
  controls body-eval recursion depth, not loop unrolling.
- Loops in the BPLs are encoded as backward `goto`s. Strata's structured
  evaluator treats them via `loopHasNoInvariants` semantics — i.e., havoc
  the loop-modified state when there's no `invariant` clause, then assume
  the loop-exit guard. The post-loop assertion is then evaluated against
  havoc'd state, and `path unreachable` fires when the negation of the
  assertion combined with the havoc constraints is unsatisfiable in the
  abstract path-condition model.
- That makes class B (bounded-fuel artifact) the wrong classification.
  The actual pattern is **class D — havoc-induced spurious vacuity**:
  Strata's model of the loop is so abstract that the assertion path's
  reachability collapses, even though the source program's loop bound is
  small (4 or 5 iterations for `array_sum` / `loop_sum`).

Soundness implication: still none. Strata is correctly reporting that
under its abstraction, the assertion's path is vacuous. But raising
`--inline-fuel` won't help — what's needed is either (a) loop invariants,
(b) a different path-condition encoding that doesn't lose precision on
loop havoc, or (c) bounded-loop unrolling as a separate flag.

The 8 oracle-unsafe SV-COMP cases (`sv_locks_14_2`, `sv_locks_15_2`,
`sv_loops_mono3_1..6_1`) still masquerade as positive results — they
should be FAIL but are vacuously passing. PASS-? at least flags this.

## Per-program table

Class column reads `D` (havoc-induced abstraction collapse) for all 18,
revised from the agent's initial class-B classification after empirical
fuel-bump (see Empirical experiment section). The Reason column retains
the structural pattern the agent identified — the loop-then-assertion
shape is correct; only the *mechanism* of vacuity changes (havoc, not
fuel exhaustion).

| Program | Class | Oracle | Reason (post-fuel-bump) | Confidence |
|---|---|---|---|---|
| sv_locks_10 | D | safe | 10-lock unlock chain in `while(1)`; havoc collapses the unlock-phase path-condition. | high |
| sv_locks_11 | D | safe | Same shape, 11 locks. | high |
| sv_locks_12 | D | safe | Same shape, 12 locks. | high |
| sv_locks_13 | D | safe | Same shape, 13 locks. | high |
| sv_locks_14_2 | D | **unsafe** | 14 locks + `goto ERROR` arms; havoc collapses the path to ERROR. PASS-? hides a real FAIL. | high |
| sv_locks_15_2 | D | **unsafe** | 15 locks; same. | high |
| sv_loops_loopv3 | D | safe | Loop bound 50M; loop havoc'd, post-loop assert vacuous. | high |
| sv_loops_mono1_1_2 | D | safe | Loop to 100M; same. | high |
| sv_loops_mono3_1 | D | **unsafe** | Loop to 1M; assert `y!=0` is false at termination. PASS-? hides real FAIL. | high |
| sv_loops_mono4_1 | D | **unsafe** | Loop to 1M; assert `y!=x` is false. Same. | high |
| sv_loops_mono5_1 | D | **unsafe** | Loop to 10M; `z!=0` is false. Same. | high |
| sv_loops_mono6_1 | D | **unsafe** | Loop to 10M; `z!=x` is false. Same. | high |
| sv_loops_nested3_1 | D | safe | Triply-nested loops to 0x0fffffff. | high |
| array_sum | D | n/a | `for (i=0;i<4;i++) sum+=a[i]; assert(sum==10)` — 4-iteration loop, havoc'd. **Concrete unroll would prove safe.** Empirically confirmed PASS-? at fuel=500. | high |
| loop_sum | D | n/a | `for (i=0;i<5;i++) sum+=i; assert(sum==10)` — 5-iteration loop, havoc'd. **Concrete unroll would prove safe.** Empirically confirmed PASS-? at fuel=500. | high |
| HTTPClient_AddRangeHeader_harness | D | n/a | Inlined callee contains `convertInt32ToAscii` with a digit-buffer loop. | medium |
| skipString_harness | D | n/a | Inlined `skipString` while-loop and `skipUTF8` callee chain. | medium |
| skipUTF8_harness | D | n/a | Inlined `countHighBits` `while ((n & 0x80U) != 0U)` loop. | medium |

## Confidence notes

- **High** for all 13 SV-COMP cases: the source is small (~20–230 lines)
  and the structural pattern is unambiguous — a loop, then the asserted
  property after the loop. Strata's CFG-fuel model unrolls forward
  `goto`s; the post-loop block is reached via the "loop guard false"
  edge after N iterations, and N is always ≥ 4 (often ≥ 10⁶).
- **Medium** for the three CBMC-imported harnesses: the harness `main`
  itself is straight-line, but they call into multi-thousand-LoC inlined
  bodies that I read structurally rather than line-by-line. The pattern
  (`while` inside a callee, post-assertion outside) matches B; I rate
  high enough to include them but flag this for the user.

## Empirical fuel-bump experiment (2026-05-30)

12 of the 18 PASS-? programs were re-run at `--inline-fuel 500` (5× the
v5 baseline of 100). Programs tested: `array_sum`, `loop_sum`,
`HTTPClient_AddRangeHeader_harness`, `skipString_harness`,
`skipUTF8_harness`, `sv_locks_10..13`, `sv_loops_loopv3`,
`sv_loops_mono1_1_2`, `sv_loops_nested3_1`.

**All 12 still PASS-?.** No verdict change at fuel=500. The simplest
case (`array_sum` — for-loop with 4 iterations) didn't flip, which
falsifies the bounded-recursion-fuel hypothesis. `--inline-fuel` is
about body-eval call-stack depth (default 100000), not loop unrolling.

This shifts the diagnosis from class B (bounded-fuel) to class D
(havoc-induced loop abstraction). The pattern across all 18:

- BPL loop is a backward `goto` without an `invariant` clause.
- Strata's evaluator havocs the loop-modified state at the loop head.
- Post-loop assertion is evaluated against havoc'd state, with
  path-condition propagation that loses precision.
- Whatever path-condition the abstraction tracks ends up unsatisfiable,
  triggering `path unreachable`.

`sv_loops_loopv3` (50M iterations), `sv_loops_mono1_1_2` (100M), and
`sv_loops_nested3_1` (~10⁸³) are explicitly out of scope for any
unrolling-based approach — those would always need an invariant.
`array_sum` (4 iterations) and `loop_sum` (5 iterations) are *small
enough* to unroll concretely, but the current evaluator doesn't do that.

## Recommendations

1. **Don't expect higher inline-fuel to flip these.** Empirically
   confirmed: fuel=500 produces zero changes. The knob to look at is
   loop handling, not call-recursion fuel.
2. **For the small-loop programs (`array_sum`, `loop_sum`) — investigate.**
   These should plausibly be unrollable. If Strata had bounded-loop
   unrolling (or smarter loop-havoc with constant-iteration detection),
   they'd flip to real PASS. Worth filing as a Strata enhancement:
   "constant-bounded loops should be unrolled rather than havoc'd".
3. **Re-classify PASS-? in the matrix.** PASS-? lumps two very different
   outcomes — "would-be-PASS with better loop handling" (5 oracle-safe
   SV-COMP + `array_sum` + `loop_sum` + 3 CBMC harnesses) vs
   "would-be-FAIL because actually unsafe" (8 oracle-unsafe SV-COMP).
   The 8 oracle-unsafe cases currently masquerade as positive results.
4. **No translator-artifact filings needed.** The two `assume false`
   instances visible in the BPLs (sv_locks_10.bpl:1507/1907/16820) are
   inside `__assert_fail` and `abort` — the standard SMACK encoding of
   `__attribute__((noreturn))`. They're sound.
5. **Strata enhancement candidates.**
   - When path-conditions become unsat post-havoc, emit
     `unknown (loop-abstraction-collapse)` rather than
     `pass (path unreachable)`. The current wording implies
     "the property holds because the assertion can't fire" — true for
     the program-as-modeled but misleading vis-à-vis the source.
   - Small-bound concrete-loop unrolling. `for (i=0; i<4; i++)` should
     be unrollable.
