# Typed Python: native verification, by default

Python verification now lowers type-annotated values to **native SMT sorts
by default** — `int` to `Int`, `str` to `String`, and so on. The old
`Any`-boxing encoding survives only where there is no type to use. The
result is dramatically faster and more decisive verification.

## Why it's possible: Leo Leesco's typechecker

This is **not** a new type system. It is built on **Leo Leesco's**
bidirectional Laurel typechecker, which already synthesizes a type for
every expression as it resolves a program. A thin elaboration layer reuses
those types to choose the operator.

The two pieces are complementary: **his engine computes the types; this
layer uses them.** Because the work rides on the typechecker, there is no
second type system to build or keep in sync.

## What it does

It is **gradual**. Annotated values lower to native sorts; un-annotated
values stay `Any`. So the speed-up lands exactly where you have added
types, and nothing changes where you have not — no annotation is required
to "turn it on."

## Why it's faster

`Any` wraps every value in one big datatype. Even when the tag is known,
each operator has to unwrap its operands, compute, and re-wrap the result,
and the solver drags that boxed structure through the whole expression — a
cost that compounds with depth (and explodes outright when the tags are
*unknown*, since the operator then case-splits over every possible kind).

Native sorts remove the wrapper. Each operation is a single case, handed
straight to the solver's built-in theories (integer, real, string,
boolean). Exponential becomes linear.

## The evidence

We run the **same type-annotated program on `main` (before this change) and
on this branch (after)**. On `main`, every value — even an annotated `int`
— was boxed in `Any` (the annotation survived only as an `isfrom_int`
precondition); here it lowers to a native sort. The proposition proved is
identical on both; only the encoding differs. So the gap is the cost of the
representation, nothing else (✓ = proved, ✗ = did not finish within 12 s):

| property               | before — boxed `Any` | after — native | speed-up |
|------------------------|----------------------|----------------|----------|
| distributivity         | ✓ 0.8 s              | ✓ 74 ms        | ~11×     |
| binomial identity      | ✗ timeout            | ✓ 74 ms        | ∞        |
| sum of squares ≥ 0     | ✗ timeout            | ✓ 76 ms        | ∞        |
| trichotomy             | ✓ 2.6 s              | ✓ 75 ms        | ~35×     |
| string associativity   | ✓ 0.4 s              | ✓ 75 ms        | ~5×      |
| empty-string identity  | ✓ 0.10 s             | ✓ 73 ms        | ~1.4×    |
| De Morgan              | ✓ 0.20 s             | ✓ 74 ms        | ~2.7×    |
| max bounds             | ✗ timeout            | ✓ 74 ms        | ∞        |
| real norm ≥ 0          | ✗ timeout            | ✓ 76 ms        | ∞        |

## What it buys, and soundness

Same program, same meaning — far faster, and decisive enough to pinpoint a
bug instead of returning "don't know." And it stays sound: every
`Any`-to-primitive conversion is **checked**, so a value that isn't really
an `int` (for example `None`) fails verification rather than slipping
through.

## How it works, at a glance

Three steps, all riding on Leo's typechecker:

1. **The translator stays generic.** It emits a faithful program with
   native type annotations, but makes *no* type decisions — no boxing, no
   choice of operator. It runs before types are known, so it cannot.

2. **The typechecker resolves it.** As Leo's bidirectional typechecker
   walks the program, it synthesizes the type of every expression. This is
   the first point where the types are actually known.

3. **The elaboration spends those types.** Using the operand types the
   typechecker just computed, it picks the native operator when the
   operands are native, and falls back to the `Any` library when one is
   dynamic — adding the box/unbox conversions only at the boundary between
   the two worlds.

Because the decision is made inside the typechecker, it is correct by
construction and naturally scoped to user code: the hand-written `Any`
library is left untouched.
