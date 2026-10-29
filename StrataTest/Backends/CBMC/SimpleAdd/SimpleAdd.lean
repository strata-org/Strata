/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Backends.CBMC.GOTO.CoreToCProverGOTO
import StrataDDM.Integration.Lean

open Std (ToFormat Format format)
open StrataDDM (Program)
-------------------------------------------------------------------------------

namespace Strata

protected def simpleAdd : Program :=
#strata
program Core;
procedure simpleAdd (x : bv W32, y : bv W32) {

  assume (bv32.uLt(x, bv{32}(0xFFFF0000)));
  assume (bv32.uLt(y, bv{32}(0x00001111)));

  var z : bv W32 := bv{32}(0);
  z := bv32.add(x, y);

  assert [z_assertion]: (bv32.uLt(z, bv{32}(0xFFFF1110)));

};
#end

-- #eval CoreToGOTO.getGotoJson "simpleAddU" Strata.simpleAddU

-- #eval CoreToGOTO.writeToGotoJson (programName := "simpleAdd")
--       (symTabFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.symtab.json")
--       (gotoFileName := "StrataTest/Backends/CBMC/SimpleAdd/simpleAdd.goto.json")
--       Strata.simpleAdd

end Strata

-------------------------------------------------------------------------------
