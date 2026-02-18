/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core

/-!
# Test parsing of variable declarations without initialization

This file tests that the Core CST grammar can parse variable declarations
without an initializer expression (i.e., `var x : int;` instead of `var x : int := 0;`).
-/

namespace Strata.Core.Test

open Core

def testProgramWithUninitializedVar :=
#strata
program Core;

procedure test() returns () {
  var x : int;
  x := 5;
  assert [x_eq_5]: (x == 5);
};

#end

def testProgramWithMultipleUninitializedVars :=
#strata
program Core;

procedure test2() returns () {
  var x : int, y : bool;
  x := 10;
  y := true;
  assert [xy_check]: ((x == 10) && y);
};

#end

-- Just check that they parse without errors
#check testProgramWithUninitializedVar
#check testProgramWithMultipleUninitializedVars

end Strata.Core.Test
