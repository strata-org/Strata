/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

import StrataDDM.Integration.Lean
meta import Strata.Languages.Core
meta import Strata.Transform.CoreTransform
meta import Strata.Transform.ConstantPropagation
meta import StrataTest.Util.TestCore

meta section

open Core
open Strata
open StrataTest.Util

/-! ## ConstantPropagation Tests -/

section ConstantPropagationTests

/-- Run constant propagation on a program, unwrapping the `CoreTransformM`
    result. This drives the public `constantPropagationPipelinePhase`, which
    bakes in the default `small ground value` predicate (`propagateConstants`
    now takes the predicate as a parameter, instantiated at the pipeline caller
    site). Running in `CoreTransformM` also lets the transform reject
    `exit`-containing programs, so the tests drive the monad here to recover the
    transformed `Program` before comparing printed output. -/
def runCP (p : Core.Program) : Core.Program :=
  match Core.Transform.run p (fun prog => do
      let (_, prog') ← constantPropagationPipelinePhase.transform prog
      return prog') with
  | .ok res => res
  | .error e => panic! (toString e) -- nopanic:ok

/-! ### Test: literal assignment is propagated into subsequent use -/

def constPropPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 42;
  assert x > 0;
};

#end

-- Expected result: `x` in the assert is replaced by its constant value `42`.
def constPropPgmAns :=
#strata
program Core;

procedure test()
{
  var x : int := 42;
  assert 42 > 0;
};

#end

#guard
  toString (runCP (translate constPropPgm)).eraseTypes ==
    toString (translate constPropPgmAns).eraseTypes

/-! ### Test: havoc kills propagated value -/

def havocKillsPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 42;
  havoc x;
  assert x > 0;
};

#end

-- After `havoc x`, the constant is killed: the program is unchanged.
#guard
  let pgm := translate havocKillsPgm
  toString (runCP pgm).eraseTypes == toString pgm.eraseTypes

/-! ### Test: propagation through branch -/

def branchPgm :=
#strata
program Core;

procedure test(b : bool)
{
  var x : int := 42;
  if (b) {
    assert x > 0;
  } else {
    assert x > 0;
  }
};

#end

def branchPgmAns :=
#strata
program Core;

procedure test(b : bool)
{
  var x : int := 42;
  if (b) {
    assert 42 > 0;
  } else {
    assert 42 > 0;
  }
};

#end

#guard
  toString (runCP (translate branchPgm)).eraseTypes ==
    toString (translate branchPgmAns).eraseTypes

/-! ### Test: assignment in one branch kills propagation after ite -/

def branchKillsPgm :=
#strata
program Core;

procedure test(b : bool)
{
  var x : int := 42;
  if (b) {
    x := 99;
  } else {
  }
  assert x > 0;
};

#end

-- The branches disagree on `x`, so it is killed at the join: program unchanged.
#guard
  let pgm := translate branchKillsPgm
  toString (runCP pgm).eraseTypes == toString pgm.eraseTypes

/-! ### Test: a `set` to an outer variable inside a block kills propagation past it

Soundness regression: the block body `set`s the outer `x`, which persists in the
parent store, so the pre-block constant `42` must NOT be propagated into the
post-block `assert x == 99`; the propagated program must be left unchanged. -/

def blockSetOuterPgm :=
#strata
program Core;

procedure test()
{
  var x : int := 42;
  blk: {
    x := 99;
  }
  assert x == 99;
};

#end

-- `x` is dropped at the block boundary, so the program is left unchanged
-- (in particular the assert keeps `x`, never the stale `42`).
#guard
  let pgm := translate blockSetOuterPgm
  toString (runCP pgm).eraseTypes == toString pgm.eraseTypes

/-! ### Test: branch-local shadow re-declarations do not leak past an `ite`

Soundness regression: both branches re-declare a block-local `var x := 99`
shadowing the outer `x := 42`. Those inner declarations are projected away on
join, so the outer `assert x == 42` must stay true. -/

def iteShadowPgm :=
#strata
program Core;

procedure test(b : bool)
{
  var x : int := 42;
  if (b) {
    var x : int := 99;
    assert x == 99;
  } else {
    var x : int := 99;
    assert x == 99;
  }
  assert x == 42;
};

#end

-- The outer assertion must not be rewritten to the false `99 == 42`.
#guard
  let out := toString (runCP (translate iteShadowPgm)).eraseTypes
  (out.splitOn "99 == 42").length == 1

end ConstantPropagationTests

end
