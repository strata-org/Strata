# Report: cbmc timeouts and the 7 pre-existing BoogieToStrata test failures

**Branch:** `htd/smack` (no new commits — investigation only)
**Date:** 2026-05-21

## Summary

Two unresolved items from the `__VERIFIER_assume` `free ensures`
synthesis work were investigated:

1. **cbmc timeouts on 4 programs** — finite-but-pathological. Cause:
   spurious back-edges in Strata's GOTO emission, not real loops or
   non-termination. A `--no-unwinding-assertions` workaround makes
   them all verify in <50ms each, but loses soundness for programs
   with real loops.
2. **7 pre-existing BoogieToStrata integration test failures** —
   two distinct categories. 6 are stale `.expect` files (line-number
   drift, all goals still pass), trivially regeneratable. 1 is a
   real-but-known parameter-name shadowing limitation that has
   `fix_core_st.py`-level mitigation in the smack-docker pipeline
   but not in BoogieToStrata's own integration tests.

Recommended next step: regenerate the 6 stale `.expect` files. Drops
the integration-test failure count from 7 → 1, removing noise that
would otherwise mask future regressions.

---

## Investigation 1: cbmc timeouts

### What

Post-`__VERIFIER_assume` synthesis (commit `1b2231f99`), cbmc shifted
4 programs from FAIL → TIMEOUT at the default 120s: `abs_func`,
`loop_sum`, `max_func`, `nondet_branch`. The README bullet at the
time speculated this was "a combination of the SMACK prelude
assumption-axiom volume and unbounded loops in the translation."
Empirically: it's neither.

### Empirical findings

Reproduced on `nondet_branch` (the simplest of the 4; ~20 lines of
straight-line C, no actual loops):

| Invocation | Runtime | Verdict |
|---|---|---|
| `cbmc --function __cprover_entry` (default) | >120s (timeout) | TIMEOUT |
| `cbmc --function __cprover_entry --unwind 1` | <50ms | VERIFICATION FAILED (10 unwinding-assertion failures) |
| `cbmc --function __cprover_entry --unwind 4` | <100ms | VERIFICATION FAILED (1 unwinding-assertion failure) |
| `cbmc --function __cprover_entry --unwind 10 --no-unwinding-assertions` | 25ms | **VERIFICATION SUCCESSFUL** |

The same workaround verifies all 4 timing-out programs in <50ms
each. But cbmc itself prints `WARNING: Use --unwinding-assertions to
obtain sound verification results` — which is the load-bearing
caveat below.

### Root cause: spurious back-edges from out-of-order GOTO labels

`cbmc --show-loops` reports 8 "loops" (`main.0`–`main.7`) on
`nondet_branch`, despite the C source containing zero loops. By
contrast, `simple_assert` (also straight-line C, no SMACK
`__VERIFIER_assume` use) reports 0 loops, and even `aws_hash_string`
(real C `while` loop) reports 0 loops in its `__cprover_entry`.

Inspecting the GOTO with `cbmc --show-goto-functions`:

```
// 161 line 3911 function main
ASSUME true // assume_48
// 162 line 3912 function main
ASSIGN main::1::_i7 := main::1::_i8
// 163 line 0 function main
IF ¬true THEN GOTO 9
// 164 line 0 function main
GOTO 9          ← jumps backward to label "9"
// 165 line 0 function main
11: LOCATION
```

Multiple unconditional `GOTO N` instructions where label `N`
appears earlier in the listing. CBMC's loop detector treats these
as back-edges and triggers unrolling-assertion checks on each.
There's no real iteration — the backward jumps are linear
control-flow rendered out of source order — but cbmc has no way to
know that without running BMC, which is what's blowing the timeout.

The translation emitting them is `coreToGotoFiles*` /
`procedureToGotoCtxViaCFG` (the recently-wired CFG dispatch). The
order of label emission is determined by Strata's CFG block
ordering, which doesn't match the natural forward-only flow CBMC
expects.

### Why `--no-unwinding-assertions` is unsound for general programs

For our 4 `__VERIFIER_assume`-using programs, the "loops" are all
spurious — the natural unwind bound for them is 1 — so disabling
unwinding assertions produces correct results. But for any program
with a real C loop (e.g. `aws_array_eq`'s `for` loop, currently
blocked at the array-type-mismatch stage), `--no-unwinding-assertions`
with too-small `--unwind` would silently drop iterations beyond the
bound, producing **VERIFICATION SUCCESSFUL on programs with bugs in
the dropped iterations**. That's exactly the soundness problem
unwinding assertions exist to flag.

### Right fix

In `Strata/Backends/CBMC/GOTO/CoreCFGToGOTOPipeline.lean`'s
`coreCFGToGotoTransform`, emit blocks in a topological order over
the CFG's actual reachability (or a reverse-postorder traversal),
so forward-only control flow appears as forward-only GOTOs. CBMC's
loop detector would then see no spurious back-edges and skip
unwinding-assertion instrumentation for these programs.

Out of scope for the `--smack` work. Worth filing as its own issue.

### Workaround for the smack-docker pipeline

If we want PASS verdicts on the 4 timing-out programs in the
short term, the pipeline could pass `--no-unwinding-assertions
--unwind 10` to cbmc. **This is unsound** for programs with real
loops, so it should be opt-in (a flag on `run_pipeline.py`) rather
than a default change.

I do not recommend taking this workaround — better to leave the
TIMEOUTs visible until the back-edge issue is fixed properly. The
TIMEOUTs are honest signal; PASSes via `--no-unwinding-assertions`
would be misleading.

---

## Investigation 2: 7 pre-existing BoogieToStrata test failures

### What

Running `dotnet test` on `Tools/BoogieToStrata/IntegrationTests`
shows 7 failures on `htd/smack` HEAD. Verified pre-existing by
stash-pop: same 7 failures reproduce on commit `1d8687465` (before
the `__VERIFIER_assume` synthesis work).

| Test | Category |
|---|---|
| `B.bpl` | Stale `.expect` (line-number drift) |
| `Bubble.bpl` | Stale `.expect` (line-number drift) |
| `CrossNestingExit.bpl` | Stale `.expect` (line-number drift) |
| `ForwardGotos.bpl` | Stale `.expect` (line-number drift) |
| `Gauss.bpl` | Stale `.expect` (line-number drift) |
| `NamespaceCollision.bpl` | Stale `.expect` (line-number drift) |
| `ParamTypeShadow.bpl` | Real (parameter shadows type synonym) |

### Category 1: stale `.expect` files (6 of 7)

Pure line-number drift. Verifier passes all goals; the line numbers
in the failure-message format have shifted by ~9 lines. Concrete
example (`B.bpl`):

```
=== Expected (.expect committed) ===
Successfully parsed.
B.core.st(37, 4) [assert_0]: ✅ pass
B.core.st(66, 4) [assert_1]: ✅ pass
B.core.st(93, 4) [assert_2]: ✅ pass
B.core.st(121, 4) [assert_3]: ✅ pass
All 4 goals passed.

=== Actual (current run) ===
Successfully parsed.
B.core.st(28, 4) [assert_0]: ✅ pass
B.core.st(49, 4) [assert_1]: ✅ pass
B.core.st(68, 4) [assert_2]: ✅ pass
B.core.st(88, 4) [assert_3]: ✅ pass
All 4 goals passed.
```

Same number of asserts, same pass/fail status, same goal count.
Only the line-number coordinates differ. The translator was
modified to emit fewer header lines (likely the recent `--smack`
plumbing or PR-1149 cherry-picks shrank some preamble), and the
`.expect` files weren't regenerated.

Fix: regenerate the 6 `.expect` files via the same `strata verify`
invocation the runner uses. Single trivial commit, no code change.

### Category 2: ParamTypeShadow.bpl (1 of 7)

A different shape entirely — there's no `.expect` file, and the
test fails because BoogieToStrata produces output the Strata parser
rejects:

```
Error: ParamTypeShadow.core.st:11:31: error: Expected a type instead of i1
```

The `.bpl` is structured as documentation of a known limitation:

```boogie
type i1 = int;
function $add.i1(i1: i1, i2: i1) returns (i1) { i1 + i2 }
```

The function parameter named `i1` shadows the type synonym `i1`.
After translation:

```
type i1 := int;
function _add_i1(i1 : i1, i2 : i1) : (i1) { (i1 + i2) }
```

Strata's parser rejects this. The `.bpl`'s comment explicitly says
"BoogieToStrata produces output that the Strata parser rejects" —
so the test was *documenting* a known gap, expecting it to fail
cleanly with "Skipping verification." Currently it fails with the
parser error instead.

`fix_core_st.py`'s `fix_param_shadowing` function in the
smack-docker pipeline already handles this: it renames parameters
that shadow type names to `p_<name>`. But the BoogieToStrata
integration tests run `strata verify` directly, without that
post-processing.

Three options:

1. **Skip the test** — mark it `[Fact(Skip = "Known limitation")]`
   to remove the noise.
2. **Move the rename into BoogieToStrata** — port
   `fix_param_shadowing`'s logic into `StrataGenerator.cs` so the
   .core.st emitted is parser-acceptable directly. Higher effort,
   eliminates the post-processing step the smack-docker pipeline
   relies on.
3. **Empty `.expect` file with documented expected error** —
   capture the current parser-error output as the `.expect` so
   the test passes by asserting "this is the error we expect to
   see." Keeps the documentation of the limitation but stops the
   test from flagging as red.

None of these are urgent. Option 1 is the lightest touch.

### Recommended next step

**Regenerate the 6 stale `.expect` files.** Single commit, ~6 file
updates, no code change. Drops failure count 7 → 1. The remaining
`ParamTypeShadow` failure is documenting a real limitation — either
keep flagging it red (current behavior, acceptable as "this is a
known issue") or apply option 1/3 above to silence it. Either way,
the noise reduction makes future genuine regressions visible.

The cbmc back-edge issue is real but lower priority — `--smack`
users will rarely run their workloads through cbmc on these
specific programs, and the symptom (TIMEOUT, not silent
incorrectness) is honest signal. File as its own issue against
`coreCFGToGotoTransform` and revisit once the higher-leverage
deductive sub-class (a) work is done.
