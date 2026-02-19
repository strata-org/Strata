/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Core
import Strata.DDM.Integration.Lean
import Strata.Languages.Core.DDMTransform.Translate

namespace StrataTest.Languages.Core.DDMTransform

open Strata

-- Test init without RHS
def testInitNoRhs : Program :=
#strata
program Core;

procedure test() returns () {
  var x : int;
  assert [x_nonneg]: (x >= 0);
};
#end

-- Test mix of init with and without RHS
def testMixedInit : Program :=
#strata
program Core;

procedure test() returns () {
  var x : int := 5;
  var y : int;
  assert [sum_positive]: ((x + y) > 0);
};
#end

end StrataTest.Languages.Core.DDMTransform
