/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
/-! # Test: WF lemmas survive FilterProcedures under selective verification

Ensures that the well-formedness lemma that `PrecondElim` generates for a
procedure's contract is kept by `FilterProcedures` together with the procedure.
-/

namespace Strata

def noFilterWFPgm :=
#strata
program Core;

procedure P(a : int, b : int, out r : int)
spec {
  requires [b_nonzero]: (b != 0);
  ensures [result_ok]: (r == int.safeDiv(a, b));
}
{
  r := int.safeDiv(a, b);
};

#end

-- Selectively verify only P. Its WF lemma P$$wf must survive filtering.
/--
info:
Obligation: P_post_result_ok_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: set_r_calls_Int.SafeDiv_0
Property: division by zero check
Result: ✅ pass

Obligation: result_ok
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify noFilterWFPgm
        (options := { Core.VerifyOptions.quiet with proceduresToVerify := some ["P"] })

-- Don't verify P, and drop the WF lemma of its contract with it
/--
info:
-/
#guard_msgs in
#eval Core.verify noFilterWFPgm
        (options := { Core.VerifyOptions.quiet with proceduresToVerify := some [] })

def funcWFPgm :=
#strata
program Core;

function half(x : int, y : int) : int
  requires !(y == 0);
{ int.safeDiv(x, y) }

function bad(x : int, y : int) : int
{ int.safeDiv(x, y) }

#end

-- Naming a function among the targets checks its WF lemmas; the WF lemmas of
-- functions not named are dropped.
/--
info:
Obligation: bad_body_calls_Int.SafeDiv_0
Property: division by zero check
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify funcWFPgm
        (options := { Core.VerifyOptions.quiet with proceduresToVerify := some ["bad"] })

end Strata
end
