/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Backends.CBMC.BoogieToCProverGOTO

open Std (ToFormat Format format)
-------------------------------------------------------------------------------

namespace Strata

protected def simpleAddUnsigned : Program :=
#strata
program Boogie;
procedure simpleAddUnsigned (x : bv32, y : bv32) returns () {

  assume (x < bv{32}(0xFFFF0000));
  assume (y < bv{32}(0x00001111));

  var z : bv32 := bv{32}(0);
  z := x + y;

  assert [z_assertion]: (z < bv{32}(0xFFFF1110));

};
#end

-- #eval BoogieToGOTO.printToGotoJson "simpleAddUnsigned" Strata.simpleAddUnsigned

-- #eval BoogieToGOTO.writeToGotoJson
--   "StrataTest/Backends/CBMC/SimpleAddUnsigned/function.json"
--   "simpleAddUnsigned"
--   Strata.simpleAddUnsigned

end Strata

-------------------------------------------------------------------------------
