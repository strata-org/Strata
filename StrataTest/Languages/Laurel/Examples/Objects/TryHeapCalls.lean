/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-
Regression coverage for `heapParameterization` handling `try`/`catch` (and
`throw`). Previously the heap analysis (`collectExpr`) and transform
(`heapTransformExpr`) both skipped `Try`/`Throw` nodes: calls inside a `try`
body were not counted toward heap classification and did not get `$heap`
threaded, so a caller invoking a heap-using procedure inside a `try` failed
re-resolution with an internal `strata-bug` (`expected 'Heap', got 'int'`).

Now such programs parse, resolve, heap-parameterize, and re-resolve cleanly,
reaching the expected `not-yet-implemented` lowering (E7) instead.
-/

-- Minimal: a heap-using callee (`alloc` allocates, so it is a heap writer) is
-- invoked inside a `try` body. This must reach the `try/catch` NYI lowering
-- without any prior `strata-bug`.
#eval testLaurel <|
#strata
program Laurel;
composite ParseError extends BaseException {}
procedure alloc() returns (r: int) opaque {
  var e: ParseError := new ParseError;
  r := 1
};
procedure computeViaTry() returns (r: int) opaque {
  try {
//^ not-yet-implemented: try/catch is not yet supported (requires generic Result lowering, E7)
    r := alloc()
  } catch e {
    r := 0
  }
};
#end

-- Realistic: multiple heap-using, throwing callees invoked inside a
-- multi-catch `try`. Reaches the throw/try NYIs (no strata-bug).
#eval testLaurel <|
#strata
program Laurel;
composite ArithError extends BaseException {}
composite ParseError extends BaseException {}
procedure parsePositive(s: int) returns (r: int) throws ParseError opaque {
  if s < 0 then {
    var pe: ParseError := new ParseError;
    throw pe
//  ^^^^^^^^ not-yet-implemented: throw is not yet supported (requires generic Result lowering, E7)
  };
  r := s
};
procedure safeDivide(a: int, b: int) returns (r: int) throws ArithError opaque {
  if b == 0 then {
    var ae: ArithError := new ArithError;
    throw ae
//  ^^^^^^^^ not-yet-implemented: throw is not yet supported (requires generic Result lowering, E7)
  };
  r := a / b
};
procedure compute(s: int) returns (r: int) opaque {
  try {
//^ not-yet-implemented: try/catch is not yet supported (requires generic Result lowering, E7)
    var n: int := parsePositive(s);
    r := safeDivide(100, n)
  } catch e when e is ParseError {
    r := -1
  } catch e when e is ArithError {
    r := -2
  }
};
#end
