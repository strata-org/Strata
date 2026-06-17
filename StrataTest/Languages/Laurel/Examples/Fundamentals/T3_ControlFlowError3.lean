/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

meta section

#eval testLaurel <|
#strata
program Laurel;

procedure letExpressionsInTransparent() returns (r: int) {
  var x: int := 0;
//^^^^^^^^^^^^^^^ error: local variables in transparent bodies are not YET supported
  var y: int := x + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in transparent bodies are not YET supported
  var z: int := y + 1;
//^^^^^^^^^^^^^^^^^^^ error: local variables in transparent bodies are not YET supported
  return z
};

procedure callLetExpressionsInTransparent() opaque {
  var x: int := letExpressionsInTransparent();
  assert x == 2
};

#end

end
