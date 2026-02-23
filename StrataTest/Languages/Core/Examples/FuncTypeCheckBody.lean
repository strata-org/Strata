/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

private def program : Program :=
#strata
program Core;

function bool_to_int (b: bool) : int {if b then 1 else 0}
function str_to_bool (s: string) : bool;

procedure test () returns ()
{
  var b: string, i: int;
  var x: string;
  i := bool_to_int(str_to_bool(b));
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:

---
info:
-/
#guard_msgs in
#eval verify program (options := Options.default)

---------------------------------------------------------------------
end Strata
