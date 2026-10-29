/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-!
End-to-end test: two sequential nondeterministic `if *` statements at the same
scope depth in one procedure, verified through `Core.verify`.

`nondetElim` gives each `if *` a distinct guard name before symbolic evaluation,
so both assertions produce obligations and both verify.
-/

meta section
open Strata
open StrataDDM (Program)

private def nondetIfsProgram : Program :=
#strata
program Core;

procedure P()
{
  if * {
    assert [a]: true;
  }
  if * {
    assert [b]: true;
  }
};

#end

/--
info:
Obligation: a
Property: assert
Result: ✅ pass

Obligation: b
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nondetIfsProgram (options := .quiet)

/-- A nondeterministic loop guard (`while *`) is likewise eliminated before
symbolic evaluation, so an assertion in its body produces a verifiable
obligation. -/
private def nondetWhileProgram : Program :=
#strata
program Core;

procedure Q()
{
  while * {
    assert [c]: true;
  }
};

#end

/--
info:
Obligation: c
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nondetWhileProgram (options := .quiet)

/-- Nested nondeterministic guards receive distinct names, so both `if *`s are
eliminated and the inner assertion produces an obligation. -/
private def nestedNondetIfProgram : Program :=
#strata
program Core;

procedure R()
{
  if * {
    if * {
      assert [inner]: true;
    }
  }
};

#end

/--
info:
Obligation: inner
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval Strata.Core.verify nestedNondetIfProgram (options := .quiet)

end
