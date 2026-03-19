# Copilot Review — Proposed Fixes

## 1. Float64 safe ops have no preconditions (Comment 5) — HIGH PRIORITY

The Float64.SafeAdd/Sub/Mul/Div are defined as `binaryFuncUneval` with no
preconditions, so PrecondElim never generates overflow VCs. This is the most
impactful issue since Laurel already emits these safe variants.

**Fix:** Add preconditions referencing the Float64.*Overflow predicates.
Since `binaryFuncUneval` doesn't support preconditions, switch to `polyUneval`
with preconditions, or build the WFLFunc manually with precondition expressions
like the BV safe ops do.

## 2. SafeSDiv/SafeSMod div-by-zero misclassification (Comment 3) — MEDIUM

Both preconditions on SafeSDiv/SafeSMod are classified as arithmeticOverflow,
but the y≠0 precondition should be divisionByZero.

**Fix:** In `classifyPrecondition`, the classification is per-function, not
per-precondition. Change the approach: instead of classifying by function name,
classify by the precondition's content. The precondition obligation includes
`ob.funcName` — for SafeSDiv, the two obligations will have different labels.
Alternatively, special-case SafeSDiv/SafeSMod: classify the first precondition
(index 0) as divisionByZero and the rest as arithmeticOverflow.

The simplest fix: check if the obligation label contains "calls_Bv" AND the
funcName contains "SafeSDiv" or "SafeSMod", and the obligation index is 0.
Actually even simpler: look at the precondition expression itself — if it
contains `== #0` (bitvec zero), it's a div-by-zero check.

## 3. ASTtoCST overflow predicate handling (Comments 1 & 2) — MEDIUM

Overflow predicates (SNegOverflow, SAddOverflow, etc.) don't have proper CST
representations. They're mapped to wrong nodes (neg_expr) or fall through to
the error path.

**Fix:** Add all overflow predicates to the binary/unary op maps, mapping them
to function application nodes. The CST has a generic function call form that
can represent any named function. If no such form exists in the DDM grammar,
the pragmatic fix is to map them to a comment/annotation node, or simply
accept the fallback (these only appear in generated assertions that are
consumed by the SMT encoder, not printed back to .core.st files).

Actually, the cleanest fix: these predicates should never reach ASTtoCST
because they only appear inside PrecondElim-generated assertions, which are
consumed by the SMT encoder. The ASTtoCST path is for printing programs back
to text. If they DO reach ASTtoCST (e.g., in debug output), a logged warning
is acceptable. Add the overflow predicates to the maps with a reasonable
approximation (function call syntax).

## 4. unsignedOverflowCheck not wired (Comment 4) — LOW

The option exists but nothing reads it.

**Fix:** Add a TODO comment explaining that this will be wired when a front-end
language (Laurel or a future C front-end) gains BV types. The option is
forward-looking infrastructure. Alternatively, remove it and re-add when needed.
I'd prefer keeping it with a clear TODO since it documents the design intent.
