/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import StrataTest.Languages.Laurel.EndToEndTests.Verification.Concurrency.CoroutineTest

open StrataTest.Util.Concurrency

/-!
Regression: a coroutine whose `relies` / `guarantees` reference a file-scope
global must still verify. `GlobalParameterization` runs before `YieldElim` and
erases `staticFields`; if it did not rename the global reference *inside* the
rely/guarantee clauses (only in preconditions/body), the name spliced into the
per-yield `assert`/`assume` by `YieldElim` would dangle after the global's
binding is gone — an unresolved name at best, a silent misresolution at worst.
Here the global `g` (a `Cell`) is read as `g#x` in both the `relies` and the
`guarantees`; verification passing confirms the global is threaded through those
clauses.
-/

def prog :=
#strata

program Laurel;

composite Cell { var x: int }

var g: Cell := new Cell

coroutine tick()
  requires g#x == 0
  relies old(g#x) <= g#x
  guarantees old(g#x) < g#x
  modifies g
{
  while (true)
      invariant oldGuarantee(g#x) <= g#x
  {
    g#x := g#x + 1;
    yield
  }
};

#end

#eval testCoroutine <| prog
