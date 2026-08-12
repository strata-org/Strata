/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
---------------------------------------------------------------------
namespace Strata

/-! ## Regression test for https://github.com/cvc5/cvc5/issues/12548

Verifying a program with an opaque (uninterpreted) type at `check-level full`
used to crash the SMT solver while extracting domain elements for the opaque
sort after an `unsat` response:

```
Obligation R_check: SMT Solver Crash! stderr:
solver stdout: unsat
(error "Parse Error: ...: cannot get domain elements unless after a SAT or
 UNKNOWN response.")
```

This was a cvc5 bug (https://github.com/cvc5/cvc5/issues/12548) fixed in
cvc5 1.3.4. With cvc5 1.3.4 the full two-sided check completes cleanly and the
assertion is reported as always false: the axiom `is_good(R) == false` makes the
obligation `is_good(R)` unsatisfiable, so it can never hold.
-/

def opaqueDomainFullCheckPgm :=
#strata
program Core;

type Opaque;
function R () : Opaque;

function is_good (r : Opaque) : bool;
axiom [r_bad]: is_good(R) == false;

procedure Check_R()
{
  assert [R_check]: is_good(R);
};
#end

/--
info:
Obligation: R_check
Property: assert
Result: ❌ always false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify opaqueDomainFullCheckPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .full })

end Strata
end
---------------------------------------------------------------------
