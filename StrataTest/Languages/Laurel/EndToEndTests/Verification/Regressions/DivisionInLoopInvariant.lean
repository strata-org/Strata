/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
## Division inside a loop invariant

A loop invariant is a *spec* position, like a `requires` or an `ensures`: it is
evaluated at the loop head, on entry and after every iteration. Nothing may be
hoisted out of one, because a hoisted statement would run exactly once, before the
loop, freezing every loop-varying operand at its pre-loop value.

This used to go wrong for `/`. `$div` carries a `requires y != 0`, which makes it a
contract-bearing procedure: the contract pass rewrites a call to it into argument
temporaries plus a precondition `assert`, and `$div` keeps a procedural twin (see
`TransparencyPass.createFunctionsForTransparentBodies`). `$add`/`$sub`/`$mul` have no
`requires`, so they stay pure functions. `LiftImperativeExpressions` then hoisted the
procedure call out of the invariant:

```
var $cp_1 : int := $ov68$$mul(2, i);   -- i == 0 here
var $cp_2 : int := 2;
assert $ov69$$div$pre0($cp_1, $cp_2);  -- checked once, before the loop
while (...) invariant $ov69$$div$asFunction($cp_1, $cp_2) == i
```

The invariant then read `$cp_1 / 2 == i` with a numerator frozen at `2 * 0`, so it was
not merely harder to prove — it no longer expressed what was written, and held only on
entry. The precondition was checked at the wrong program point too.

Three passes cooperate to keep an invariant intact:

- `LiftImperativeExpressions` leaves invariants and `decreases` untransformed, so
  nothing escapes the loop head.
- `TransparencyPass` rewrites calls in those positions to their pure `$asFunction`
  twins and strips the injected `assert`, exactly as it does for quantifier bodies —
  so what remains is a pure expression rather than a procedure call.
- `InlineLocalVariables` folds the leftover `var $cp_… :=` temporaries back into that
  expression, since a Core invariant can no more carry a declaration than a function
  body can.

The invariant therefore reaches Core inline and re-evaluated per iteration, as
`$ov69$$div$asFunction($ov68$$mul(2, i), 2) == i`.

Note that a division in a spec position no longer carries a divide-by-zero
obligation at the loop head: the `assert` is stripped along with the temporaries.
Division by a possibly-zero denominator in ordinary imperative code is still
checked (see `divisionByUnknown` below). This mirrors the pre-existing behaviour of
`PrimitiveOp`'s per-site `skipProof` flag, which `TransparencyPass` set in pure
contexts so a spec-position division lowered straight to `Int.Div`.

Upstream impact: this is what broke `StrataJavaFrontEnd`'s `GaussianSum` and
`WhileLoop`, whose `sumTo` carries `invariant(s == i * (i + 1) / 2)`.
-/

#eval testLaurelVerification <|
#strata
program Laurel;

// Division in ordinary (non-invariant) positions is unaffected: these are all
// evaluated at a single program point, so hoisting is harmless.
procedure divisionInAssert(k: int)
  opaque
{
  assert 4 / 2 == 2;
  assert (2 * k) / 2 == k
};

procedure divisionInPostcondition(k: int) returns (r: int)
  opaque
  ensures r == (2 * k) / 2
{
  r := k
};

// A division by a possibly-zero denominator is still reported, because `$div`
// has the `requires`.
procedure divisionByUnknown(a: int, b: int) returns (r: int)
  opaque
{
  r := a / b
//^^^^^^^^^^ error: precondition does not hold
};

// A loop invariant containing a division over a loop-varying operand: the operands
// stay live, so this proves. The body is linear, so nonlinear arithmetic cannot
// confound the result.
procedure divisionInLoopInvariant(n: int) returns (r: int)
  requires 0 <= n
  opaque
  ensures r == n
{
  var i: int := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant (2 * i) / 2 == i
  {
    i := i + 1
  };
  r := i
};

// The same proof written without division, as a control: it exercises the ordinary
// (non-contract-bearing) operator path through an invariant.
procedure multiplicationInLoopInvariant(n: int) returns (r: int)
  requires 0 <= n
  opaque
  ensures r == n
{
  var i: int := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant 2 * i == i + i
  {
    i := i + 1
  };
  r := i
};

// The Gaussian-sum shape from StrataJavaFrontEnd's `GaussianSum`/`WhileLoop`.
procedure sumTo(n: int) returns (r: int)
  requires 0 <= n && n <= 65535
  opaque
  ensures r == n * (n + 1) / 2
{
  var i: int := 0;
  var s: int := 0;
  while (i < n)
    invariant 0 <= i && i <= n
    invariant s == i * (i + 1) / 2
  {
    i := i + 1;
    s := s + i
  };
  r := s
};
#end
