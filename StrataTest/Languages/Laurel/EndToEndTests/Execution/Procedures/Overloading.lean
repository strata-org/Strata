/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! # Overloaded static procedures through the full pipeline

The resolution tests (`EndToEndTests/Resolution/Procedures/Overloading.lean`)
stop at resolution. These tests run overloaded procedures through the *entire*
pipeline (`testLaurelMultiple`: translate + all lowering passes + verify +
interpret), ensuring that overloads distinguished by `uniqueId` flow correctly
through the pipeline.

Each overload's body computes a *different* function of its argument, and the
caller asserts the concrete result. If overload selection picked the wrong
overload — or if the two overloads collapsed onto a single id/name during
lowering — the wrong body would execute and the assertion would fail. -/

#eval testLaurelMultiple
#strata
program Laurel;

procedure f(x: int): int { return x + 1 };
procedure f(x: bool): bool { return !x };
procedure f_ov(x: int): int { return x + 2 };

procedure g(): int { return 0 };
procedure g(x: int): int { return x };
procedure g(x: int, y: int): int { return x + y };

procedure testTypeOverloads()
  entry
  opaque
{
  var a: int := f(1);
  assert a == 2;
  var b: bool := f(true);
  assert b == false
};

procedure testArityOverloads()
  entry
  opaque
{
  var a: int := g();
  assert a == 0;
  var b: int := g(5);
  assert b == 5;
  var c: int := g(2, 3);
  assert c == 5
};

procedure testCoexistWithNonOverloaded()
  entry
  opaque
{
  var a: int := f(1);
  assert a == 2;
  var b: int := f_ov(1);
  assert b == 3
};
#end

/-! ## Selecting the wrong overload's contract is caught

The caller asserts the result the *other* overload would have produced. The
assertion must fail — confirming the tests above are actually pinning the
selected overload's postcondition, not passing vacuously. -/

#eval testLaurelMultiple
#strata
program Laurel;
procedure f(x: int): int { return x + 1 };
procedure f(x: bool): bool { return !x };
procedure caller()
  entry
  opaque
{
  var a: int := f(1);
  assert a == 1
//^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## A no-overload call produces the expected error through the full pipeline -/

#eval testLaurel
#strata
program Laurel;
procedure f(x: int) returns (r: int) opaque ensures r == x;
procedure f(x: bool) returns (r: bool) opaque ensures r == x;
procedure caller() opaque {
  var a: int := f("hello")
//              ^^^^^^^^^^ error: no overload of 'f' matches the argument types
};
#end

/-! ## Identical signatures are rejected without a spurious internal-error banner -/

#eval testLaurel
#strata
program Laurel;
procedure foo(x: int) opaque { };
procedure foo(x: int) opaque { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
#end
