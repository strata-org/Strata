/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Perf / regression: the array-theory frame is not merely faster, it is more
complete on heap-heavy code.

`stress` makes a deep chain of opaque heap-modifying calls on freshly allocated
objects, then asserts that an object allocated *before* the chain is untouched.

  - Under the `∀` frame (array theory off) the solver historically could not
    instantiate the quantified frame across the whole chain. With the heap
    well-formedness preconditions and the monotonic-heap postcondition
    synthesized by `HeapParameterization`, the solver now has the algebraic
    facts (`Composite..ref!(target) < Heap..nextReference!($heap_in)` plus
    monotonicity across each call) to discharge the assertion even with the
    `∀` frame.
  - Under the quantifier-free frame (`--use-array-theory`) the same assertion
    also verifies, more directly: each step is a `store` on a single row, so
    the read of the untouched object is a pure array rewrite.

The two blocks are identical apart from `useArrayTheory`. Both now succeed;
the array-theory variant remains the recommended path for performance.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

-- ∀ frame (array theory off): heap-WF preconditions + monotonic-heap
-- postcondition supply the facts the solver needs to discharge the assertion.
#eval testLaurelVerification
    (options := { defaultLaurelTestOptions with
      translateOptions := { defaultLaurelTestOptions.translateOptions with enumeratedModifiesClauses := false },
      verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := false } }) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure modifyOne(c: Container)
  opaque
  modifies c;

procedure stress()
  opaque
  modifies *
{
  var target: Container := new Container;
  var x: int := target#value;
  var c0: Container := new Container; modifyOne(c0);
  var c1: Container := new Container; modifyOne(c1);
  var c2: Container := new Container; modifyOne(c2);
  var c3: Container := new Container; modifyOne(c3);
  var c4: Container := new Container; modifyOne(c4);
  var c5: Container := new Container; modifyOne(c5);
  var c6: Container := new Container; modifyOne(c6);
  var c7: Container := new Container; modifyOne(c7);
  var c8: Container := new Container; modifyOne(c8);
  var c9: Container := new Container; modifyOne(c9);
  var c10: Container := new Container; modifyOne(c10);
  var c11: Container := new Container; modifyOne(c11);
  var c12: Container := new Container; modifyOne(c12);
  var c13: Container := new Container; modifyOne(c13);
  var c14: Container := new Container; modifyOne(c14);
  var c15: Container := new Container; modifyOne(c15);
  var c16: Container := new Container; modifyOne(c16);
  var c17: Container := new Container; modifyOne(c17);
  var c18: Container := new Container; modifyOne(c18);
  var c19: Container := new Container; modifyOne(c19);
  assert x == target#value
};
#end

-- Quantifier-free frame (--use-array-theory): the same program verifies.
#eval testLaurelVerification
    (options := { defaultLaurelTestOptions with
      translateOptions := { defaultLaurelTestOptions.translateOptions with enumeratedModifiesClauses := true },
      verifyOptions := { defaultLaurelTestOptions.verifyOptions with useArrayTheory := true } }) <|
#strata
program Laurel;
composite Container {
  var value: int
}

procedure modifyOne(c: Container)
  opaque
  modifies c;

procedure stress()
  opaque
  modifies *
{
  var target: Container := new Container;
  var x: int := target#value;
  var c0: Container := new Container; modifyOne(c0);
  var c1: Container := new Container; modifyOne(c1);
  var c2: Container := new Container; modifyOne(c2);
  var c3: Container := new Container; modifyOne(c3);
  var c4: Container := new Container; modifyOne(c4);
  var c5: Container := new Container; modifyOne(c5);
  var c6: Container := new Container; modifyOne(c6);
  var c7: Container := new Container; modifyOne(c7);
  var c8: Container := new Container; modifyOne(c8);
  var c9: Container := new Container; modifyOne(c9);
  var c10: Container := new Container; modifyOne(c10);
  var c11: Container := new Container; modifyOne(c11);
  var c12: Container := new Container; modifyOne(c12);
  var c13: Container := new Container; modifyOne(c13);
  var c14: Container := new Container; modifyOne(c14);
  var c15: Container := new Container; modifyOne(c15);
  var c16: Container := new Container; modifyOne(c16);
  var c17: Container := new Container; modifyOne(c17);
  var c18: Container := new Container; modifyOne(c18);
  var c19: Container := new Container; modifyOne(c19);
  assert x == target#value
};
#end
