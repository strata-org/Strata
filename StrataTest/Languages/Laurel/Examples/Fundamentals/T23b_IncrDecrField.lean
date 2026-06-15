/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-!
End-to-end verification of `++` and `--` applied to composite-type fields
(`obj#field`), in both statement and expression positions. The composite
type triggers Laurel's heap parameterization pass, so this is split out
from `T23_IncrDecr.lean` to avoid the heap-parameterized program perturbing
counterexample search for the failing tests there.

Why field-IncrDecr in expression position works: the pipeline runs
`EliminateIncrDecr` first, which lowers `(c#n)++` to
`(c#n := c#n + 1) - 1`. `HeapParameterization` then runs and rewrites the
inner `c#n := c#n + 1` field-assign into a sequence:

  $tmp_i := readField(...) + 1
  $heap  := updateField($heap, c, Counter.n, BoxInt($tmp_i))
  $tmp_i        -- yields the new field value

By the time `LiftImperativeExpressions` runs, every assignment target is a
local (`$tmp_i` or `$heap`), so its snapshot mechanism — which is keyed on
`Variable.Local` — handles the increment correctly. The Field-target arm of
`liftAssignExpr` (which falls through `| _ => pure ()`) is defensive but
never reached in this pipeline order.

The parentheses around `(c#n)` are needed in the surface syntax because
`#field` and `++` are both trailing operators with the same precedence
(90); `c#n++` parses ambiguously without them.
-/

#eval testLaurel <|
#strata
program Laurel;
composite IncrDecrCounter {
  var n: int
}

procedure postIncrFieldStatement()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 10;
  (c#n)++;
  assert c#n == 11
};

procedure preIncrFieldStatement()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 10;
  ++(c#n);
  assert c#n == 11
};

procedure postDecrFieldStatement()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 10;
  (c#n)--;
  assert c#n == 9
};

procedure preDecrFieldStatement()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 10;
  --(c#n);
  assert c#n == 9
};

procedure mixedFieldIncrDecrStatements()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 0;
  (c#n)++;
  (c#n)++;
  ++(c#n);
  (c#n)--;
  assert c#n == 2
};

procedure postIncrFieldInExpression()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 5;
  // Postfix yields the OLD field value (5); c#n is updated to 6.
  var y: int := (c#n)++;
  assert c#n == 6;
  assert y == 5
};

procedure preIncrFieldInExpression()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 5;
  // Prefix yields the NEW field value (6).
  var y: int := ++(c#n);
  assert c#n == 6;
  assert y == 6
};

procedure postDecrFieldInExpression()
  opaque
{
  var c: IncrDecrCounter := new IncrDecrCounter;
  c#n := 5;
  // Postfix decrement yields the OLD field value (5); c#n becomes 4.
  var y: int := (c#n)--;
  assert c#n == 4;
  assert y == 5
};
#end
