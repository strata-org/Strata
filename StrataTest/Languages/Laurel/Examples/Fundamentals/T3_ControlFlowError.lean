/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

#eval testLaurel <|
#strata
program Laurel;

procedure localVariableWithoutInitializer(): int {
  var x: int;
//^^^^^^^^^^ error: local variables must have initializers in transparent bodies or contracts
  return 3
};
#end
