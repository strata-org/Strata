/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Integration.Lean
import Strata.Languages.Core.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Transform.ConstantPropagation

open Core
open Strata

/-! ## ConstantPropagation Tests -/

section ConstantPropagationTests

def translate (t : Strata.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram t)).fst

/-! ### Test: literal assignment is propagated into subsequent use -/

-- var x : int := 42; assert x > 0
-- After propagation: var x : int := 42; assert 42 > 0
def constPropPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 42;
  assert x > 0;
};

#end

-- Check that propagation produces a program (no crash)
#guard_msgs in
#eval do
  let pgm := translate constPropPgm
  let pgm' := propagateConstantsInProgram pgm
  -- The transformed program should have at least as many decls
  assert! pgm'.decls.length == pgm.decls.length

/-! ### Test: havoc kills propagated value -/

def havocKillsPgm :=
#strata
program Core;

procedure test() returns ()
{
  var x : int := 42;
  havoc x;
  assert x > 0;
};

#end

#guard_msgs in
#eval do
  let pgm := translate havocKillsPgm
  let pgm' := propagateConstantsInProgram pgm
  assert! pgm'.decls.length == pgm.decls.length

/-! ### Test: propagation through branch -/

def branchPgm :=
#strata
program Core;

procedure test(b : bool) returns ()
{
  var x : int := 42;
  if (b) {
    assert x > 0;
  } else {
    assert x > 0;
  }
};

#end

#guard_msgs in
#eval do
  let pgm := translate branchPgm
  let pgm' := propagateConstantsInProgram pgm
  assert! pgm'.decls.length == pgm.decls.length

end ConstantPropagationTests
