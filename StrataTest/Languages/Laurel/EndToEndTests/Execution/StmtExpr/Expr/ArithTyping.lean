/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! Documents the current behaviour of the arithmetic typing rules.

    Two rules apply:

    - [⇐] Op-Arith — the *check* path: an expected type from context
      is pushed into every operand.
    - [⇒] Op-Arith — the *synth* path: operands are synthesized and
      folded under `join` to the result type.

    Homogeneous numeric operands type-check via either path;
    heterogeneous ones (e.g. `int + real`) are rejected by both. The
    gradual `Unknown` wildcard flows freely. -/

#eval testLaurelResolution <|
#strata
program Laurel;
procedure homogeneousInt()
  opaque
{
  var x: int := 1 + 2;
  assert x == 3
};

procedure homogeneousReal()
  opaque
{
  var x: real := 1.5 + 2.5;
  assert x == 4.0
};

// [⇐] Op-Arith: check path (the `var: real` annotation drives it).
// `+` is a call to the overloaded `$add` wrapper, so a mixed `int`/`real` pair
// matches neither the `int` nor the `real` overload and is reported as an
// overload-resolution failure over the whole call rather than as a mismatch
// against one operand.
procedure heterogeneousCheckPath()
  opaque
{
  var x: real := 1 + 2.0
//               ^^^^^^^ error: no overload of '$add' matches the argument types
};

// [⇒] Op-Arith: synth path (the `<` forces `1 + 2.0` into synth position).
procedure heterogeneousSynthPath()
  opaque
{
  assert (1 + 2.0) < 5
//        ^^^^^^^ error: no overload of '$add' matches the argument types
};

procedure unaryNegHomogeneous()
  opaque
{
  var a: int := 5;
  var b: int := -a;
  var c: real := 1.5;
  var d: real := -c;
  assert b == 0 - 5;
  assert d == 0.0 - 1.5
};

// The hole '<?>' synthesizes to 'Unknown', and `join` promotes it to
// its neighbour: 'Unknown + TInt' folds to TInt. The error against
// '2.0' (real) is what proves the join returned TInt, not Unknown
// (Unknown would have compared silently).
procedure unknownPromotesToNeighbour()
  opaque
{
  assert (<?> + 1) == 2.0
//       ^^^^^^^^^^^^^^^^ error: cannot compare 'int' with 'real' using '=='
};
#end
