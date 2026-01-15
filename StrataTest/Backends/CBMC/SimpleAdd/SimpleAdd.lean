/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Backends.CBMC.CoreToCProverGOTO

open Std (ToFormat Format format)
-------------------------------------------------------------------------------

namespace Strata

protected def simpleAdd : Program :=
#strata
program Core;
procedure simpleAdd (x : bv32, y : bv32) returns () {

  assume (x < bv{32}(0xFFFF0000));
  assume (y < bv{32}(0x00001111));

  var z : bv32 := bv{32}(0);
  z := x + y;

  assert [z_assertion]: (z < bv{32}(0xFFFF1110));

};
#end

-- #eval CoreToGOTO.getGotoJson "simpleAddU" Strata.simpleAddU

-- #eval CoreToGOTO.writeToGotoJson (programName := "simpleAdd")
--       (symTabFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.symtab.json")
--       (gotoFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.goto.json")
--       Strata.simpleAdd

end Strata

-------------------------------------------------------------------------------
