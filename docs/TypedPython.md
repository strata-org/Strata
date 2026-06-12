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
layer spends them.** Because the work rides on the typechecker, there is no
second type system to build or keep in sync.

## What it does

It is **gradual**. Annotated values lower to native sorts; un-annotated
values stay `Any`. So the speed-up lands exactly where you have added
types, and nothing changes where you have not — no annotation is required
to "turn it on."

## Why it's faster

`Any` wraps every value in one big datatype, so the solver must reason
about *which* kind each value carries. Every operator then case-splits over
all the runtime types of its operands, and that cost compounds with
expression depth — exponential in the worst case.

Native sorts remove the wrapper. Each operation is a single case, handed
straight to the solver's built-in theories (integer, real, string,
boolean). Exponential becomes linear.

## The evidence

A microbenchmark verifies small symbolic functions twice — once with native
types, once forced through `Any` (✓ = proved, ✗ = could not prove: timed
out or inconclusive):

| scenario               | native      | `Any`         | speed-up |
|------------------------|-------------|---------------|----------|
| sum of squares ≥ 0     | ✓ 53 ms     | ✗ timeout     | ∞        |
| polynomial identity    | ✓ 55 ms     | ✗ timeout     | ∞        |
| distributivity         | ✓ 51 ms     | ✗ 575 ms      | 11×      |
| trichotomy             | ✓ 52 ms     | ✗ 2.4 s       | 46×      |
| string associativity   | ✓ 52 ms     | ✗ 0.31 s      | 6×       |
| empty-string identity  | ✓ 51 ms     | ✗ 59 ms       | 1.1×     |
| De Morgan              | ✓ 52 ms     | ✓ 99 ms       | 1.9×     |
| max bounds             | ✓ 53 ms     | ✗ timeout     | ∞        |
| real norm ≥ 0          | ✓ 52 ms     | ✗ timeout     | ∞        |

**Native proves 9 of 9 in ~52 ms median; `Any` proves only 1 of 9.** The
win is not merely speed: on most of these goals `Any` times out or gives up
entirely, while native settles them in tens of milliseconds. Native proves
things `Any` simply cannot.

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
