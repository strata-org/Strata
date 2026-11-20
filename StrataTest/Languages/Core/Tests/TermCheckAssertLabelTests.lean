/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# Termination lemmas are named apart from procedure check labels

Termination checking names each lemma it generates apart from every declaration name and every
label of a procedure's checks (`Program.takenNames`): its asserts at any depth, loop invariants,
covers and contract clauses. A check labeled like a termination lemma (`bad_terminates_0`) keeps
its label, and the termination lemma gets the next free suffix, so the two results have distinct
names and each verdict is read off its own obligation.
-/

namespace Strata.TermCheckAssertLabelTest

open StrataDDM (Program)

---------------------------------------------------------------------
-- The termination lemma fails, the assertion with its label passes.
---------------------------------------------------------------------

def lemmaFailsPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), int.sub(n, 1))
};

procedure P() {
  assert [bad_terminates_0]: true;
};
#end

/--
info:
Obligation: bad_terminates_0_1
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Core.verify lemmaFailsPgm (options := .quiet)

---------------------------------------------------------------------
-- The termination lemma passes, the assertion with its label fails.
---------------------------------------------------------------------

def assertFailsPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), int.sub(n, 1))
};

procedure P() {
  assert [bad_terminates_1]: false;
};
#end

/--
info:

Obligation bad_terminates_1: failed!

Result obtained during evaluation.
---
info:
Obligation: bad_terminates_0
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify assertFailsPgm (options := .quiet)

---------------------------------------------------------------------
-- The same for an assertion inside a conditional branch.
---------------------------------------------------------------------

def nestedAssertPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), int.sub(n, 1))
};

procedure P(y : int) {
  if (int.gt(y, 0)) {
    assert [bad_terminates_1]: y == 2;
  }
};
#end

/--
info:
Obligation: bad_terminates_0
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify nestedAssertPgm (options := .quiet)

---------------------------------------------------------------------
-- The same for a postcondition, which the procedure check asserts.
---------------------------------------------------------------------

def ensuresPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), int.sub(n, 1))
};

procedure P(y : int)
spec { ensures [bad_terminates_1]: y == 2; }
{
};
#end

/--
info:
Obligation: bad_terminates_0
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1_1
Property: assert
Result: ✅ pass

Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_1
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify ensuresPgm (options := .quiet)

end Strata.TermCheckAssertLabelTest

end
