# Report: `__VERIFIER_assume` `free ensures` synthesis

**Branch:** `htd/smack` (commits `1b2231f99` + `144b1f0cc`)
**Date:** 2026-05-21

## Summary

Added a `--smack`-gated synthesis in BoogieToStrata that emits
`free ensures ($i0 != 0)` on `__VERIFIER_assume` procedure declarations.
The synthesis mirrors the existing `assert_.<type>` `Requires` injection
pattern at `StrataGenerator.cs:VisitProcedure`, with the dual polarity
(`Ensures` / `free: true` instead of `Requires` / `false`).

This was prompted by the deductive sub-class (b) finding from earlier
in the session: SMACK's `assume(b)` translates to a Boogie procedure
whose body is `assume $i0 != $0`, but the body's assume doesn't
propagate to callers under modular deductive verification. A
procedure-level `free ensures` is the correct encoding — callers may
assume the constraint, the implementation has no proof obligation.

## Implementation

12-line addition in
`Tools/BoogieToStrata/Source/StrataGenerator.cs`:

```csharp
Ensures? syntheticEns = null;
if (_smack && node.Name.Equals("__VERIFIER_assume") && node.InParams.Count > 0) {
    var param = node.InParams[0];
    var paramExpr = new IdentifierExpr(param.tok, param);
    var zero = new LiteralExpr(param.tok, Microsoft.BaseTypes.BigNum.FromInt(0));
    var neqExpr = Expr.Neq(paramExpr, zero);
    syntheticEns = new Ensures(free: true, neqExpr);
    node.Ensures.Add(syntheticEns);
}
```

Plus a `finally` extension to remove the synthetic clause after
emission, mirroring the existing AST-restoration pattern.

Three regression tests:
- `VerifierAssume.bpl` + `.expect` — happy path; the integration
  runner asserts the verifier's stdout matches.
- `VerifierAssumeWithoutFlagDoesNotInjectEnsures` — gate-off
  regression. Mirrors `SmackAssertWithoutFlagDoesNotInjectRequires`.
- `VerifierAssumeProducesSingleMergedSpecBlock` — silent-drop
  regression with a procedure that already has a hand-written
  `ensures`. Mirrors `SmackAssertProducesSingleMergedSpecBlock`.

## Verifier acceptance

The synthesis lands on every `__VERIFIER_assume` declaration in the
25-program SMACK suite. Per-VC verdict (sample from `abs_func` with
`--check-level full`):

```
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
 [__VERIFIER_assume_ensures_0]: ✅ always true and is reachable from declaration entry
abs_func_fixed.core.st(3706, 2) [(Origin_assert__i32_Requires)assert__i32_requires_0]: 🔶 …
```

Six `__VERIFIER_assume_ensures_0` instances, each marked passing.
Strata's call-elim is correctly turning the synthesized `free ensures`
into caller-side assumes (verified by reading
`Strata/Transform/CallElim.lean:118-122`); `ensuresToAsserts` filters
the `.Free` flag at procedure-definition time so the implementation
has no obligation to prove (`Strata/Transform/ProcBodyVerify.lean:62-66`).

## Suite-level impact

| Backend | Pre-fix | Post-fix | Δ |
|---|---|---|---|
| deductive | 4 pass, 21 partial | **5 pass, 20 partial** | +1 PASS |
| bugFinding | 0 pass, 25 partial | unchanged | none |
| cbmc | 0 pass, 25 fail, 0 timeout | 0 pass, 21 fail, **4 timeout** | failure-mode shift |

## What we expected vs. what happened

The spec predicted three PARTIAL → PASS flips (`abs_func`, `max_func`,
`nondet_branch`). Empirically, only `nondet_branch` flipped fully.
Per-program detail on the other two:

| Program | Pre-fix VCs (pass/fail) | Post-fix VCs (pass/fail) |
|---|---|---|
| `abs_func` | 0 / 1 | 7 / 1 |
| `max_func` | 0 / 1 | 1 / 1 |
| `nondet_branch` | 0 / 1 | (clean PASS, full discharge) |

The miss is informative: the verifier's
`(Origin_assert__i32_Requires)assert__i32_requires_0` label is
**multi-causal**. Either of two distinct gaps can produce it:

1. **Sub-class (b)** — `__VERIFIER_assume` not propagating its
   constraint to callers. Closed by this synthesis.
2. **Sub-class (a)** — an `assert` downstream of a user function
   call where the callee lacks an `ensures` clause. Not addressed
   by this work.

For `abs_func` and `max_func`, both gaps were present. The synthesis
closed (b), surfacing the (a) failure underneath. The remaining
single failing VC on each program is the C-level
`assert(abs_val(x) >= 0)` / `assert(max(a, b) >= a)` failing because
the corresponding user function has no `ensures`. Closing that needs
the sub-class (a) lever (synthesizing or inlining `ensures` for user
functions), which is a much larger problem.

## Side effect: cbmc timeouts

The cbmc column moved from `0 pass, 25 fail` to `0 pass, 21 fail,
4 timeout`. The 4 newly-timing-out programs are
`abs_func`, `loop_sum`, `max_func`, `nondet_branch` — exactly the
ones using `__VERIFIER_assume`.

Cause: BoogieToStrata's `WriteProcedureHeader` emits the synthesized
clause as `free ensures ($i0 != 0)` in the `.core.st`, and the CBMC
backend translates that to a `#spec_ensures` annotation in the GOTO
JSON (`CoreToGOTOPipeline.lean:357-373`). Even though our pipeline
doesn't pass `--apply-code-contracts` to cbmc, cbmc appears to be
consuming the annotation in some form — the BMC unroller now expands
further on the `__VERIFIER_assume`-using programs, hitting the
default 120s timeout.

That's a real change in behavior, not a regression: previously these
programs fast-failed at the no-body-callee stage (rc=10 with bogus
property violations); now cbmc symbolically explores further before
giving up. Bumping `--unwind` may turn these into actual verdicts;
out of scope for this commit.

## What this closes

- **Sub-class (b)** at the SMACK→Strata translation layer:
  `__VERIFIER_assume`'s semantics now reach the verifier as
  `free ensures`. The fix lever the spec identified is implemented.
- **Test infrastructure parity** with the existing `assert_.*`
  pattern: gate-off, merged-spec-block, and happy-path tests all
  exist for the new synthesis.

## What this does not close

- The two `(Origin_assert__i32_Requires)` failures still showing
  on `abs_func` and `max_func` — those are sub-class (a), not (b).
  Solving them needs `ensures` synthesis on user-defined helpers
  (the `abs_val` and `max` functions in the C source).
- cbmc verdicts on the 4 newly-timing-out programs. Either a larger
  `--unwind` bound or a body-emission fix (the existing "callee
  bodies not emitted" blocker in the README) would help.

## Notes for future work

- The pattern of "spec predicts X, empirics show Y" was useful here:
  it forced us to read per-VC verdicts (`X passed on N paths,
  failed on M paths`) which surfaced the multi-causal nature of
  the failing label. Worth doing for future sub-class predictions
  before claiming a closure.
- BoogieToStrata's `assert_.<type>` precedent is a strong template
  for SV-COMP-convention handlers. If we ever need to handle more
  SV-COMP names (`__VERIFIER_nondet_*`, etc.), the same
  `VisitProcedure` pattern + `try/finally` AST-restoration scaffold
  applies directly.
- The 7 pre-existing test failures on this branch (`B.bpl`,
  `Bubble.bpl`, `CrossNestingExit.bpl`, `ForwardGotos.bpl`,
  `Gauss.bpl`, `NamespaceCollision.bpl`, `ParamTypeShadow.bpl`)
  are unrelated to this work — they reproduce identically on the
  prior commit `1d8687465`. Worth investigating separately.
