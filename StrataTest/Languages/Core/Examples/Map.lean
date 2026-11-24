/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section
open Strata

---------------------------------------------------------------------
private def mapPgm :=
#strata
program Core;

const a : Map int bool;

procedure P()
{
  assume [a_zero_true_assumption]: (a[0] == true);
  assert [a_zero_true]: a[0];
  assert [a_one_true]: a[1];
};
#end

/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.snd |>.isEmpty

/--
info: program Core;

function a () : Map int bool;
procedure P ()
{
  assume [a_zero_true_assumption]: a[0] == true;
  assert [a_zero_true]: a[0];
  assert [a_one_true]: a[1];
};
-/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram mapPgm) |>.fst

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: a_zero_true
Property: assert
Assumptions:
a_zero_true_assumption: a[0] == true
Obligation:
a[0]

Label: a_one_true
Property: assert
Assumptions:
a_zero_true_assumption: a[0] == true
Obligation:
a[1]

---
info:
Obligation: a_zero_true
Property: assert
Result: ✅ pass

Obligation: a_one_true
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Strata.Core.verify mapPgm

---------------------------------------------------------------------
-- Extensionality depends on the SMT encoding. Two maps equal at every key are
-- equal under the array encoding, but not provably so under the default encoding,
-- whose `Map` axioms speak only about `select`. The tests run quietly, so they pin
-- the verdicts and not the models the solver chooses.
private def mapExtPgm :=
#strata
program Core;

procedure MapExt(m : Map int int, n : Map int int)
{
  assume [same_values]: (forall k : int :: m[k] == n[k]);
  assert [ext]: m == n;
};
#end

/--
info:
Obligation: ext
Property: assert
Result: ❓ unknown
-/
#guard_msgs in
#eval Strata.Core.verify mapExtPgm (options := .quiet)

/--
info:
Obligation: ext
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify mapExtPgm
  (options := { Core.VerifyOptions.quiet with useArrayTheory := true })

end
---------------------------------------------------------------------
