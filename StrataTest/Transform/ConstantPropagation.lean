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

private def hasSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

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

#guard_msgs in
#eval do
  let pgm := translate constPropPgm
  let pgm' := propagateConstantsInProgram pgm
  let fmt := toString (Core.formatProgram pgm')
  -- x should be replaced by 42 in the assert
  assert! hasSubstr fmt "42 > 0"
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
  let fmt := toString (Core.formatProgram pgm')
  -- After havoc, x should NOT be replaced — assert should not contain "42 > 0"
  assert! !hasSubstr fmt "42 > 0"

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
  let fmt := toString (Core.formatProgram pgm')
  -- x should be propagated into both branches
  assert! hasSubstr fmt "42 > 0"

/-! ### Test: assignment in one branch kills propagation after ite -/

def branchKillsPgm :=
#strata
program Core;

procedure test(b : bool) returns ()
{
  var x : int := 42;
  if (b) {
    x := 99;
  } else {
  }
  assert x > 0;
};

#end

#guard_msgs in
#eval do
  let pgm := translate branchKillsPgm
  let pgm' := propagateConstantsInProgram pgm
  let fmt := toString (Core.formatProgram pgm')
  -- After ite where one branch reassigns x, x should NOT be propagated
  assert! !hasSubstr fmt "42 > 0"
  assert! !hasSubstr fmt "99 > 0"

end ConstantPropagationTests
