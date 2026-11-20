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

/-! ## Datatype constructors named like solver verdicts

In two-sided checking (check level `full`) the solver answers two `check-sat` commands, each
followed by the response to a `get-value`. A value of type `Verdict` below prints as `sat`,
`unsat` or `unknown`, and z3 prints a model of the twenty-field `Big` over several lines, one
field per line, the second field on a line of its own. The second verdict is the one after that
whole model, not a model line that reads like a verdict.

Each procedure fixes the second field to one of the three constructors. In each, `holds` is
always true and `fails` is false for some `x` (any `x` whose fourth field is not `sat`). A
reader that took the first line reading like a verdict as the second verdict would, on z3,
report `fails_unsat` always true, `holds_sat` possibly false and `fails_unknown` unknown.
cvc5 prints each model on one line, so its answers are read the same either way.
-/

def verdictNamedConstructorsPgm :=
#strata
program Core;

datatype Verdict { sat(), unsat(), unknown() };
datatype Big { MkBig(f1: Verdict, f2: Verdict, f3: Verdict, f4: Verdict, f5: Verdict,
                     f6: Verdict, f7: Verdict, f8: Verdict, f9: Verdict, f10: Verdict,
                     f11: Verdict, f12: Verdict, f13: Verdict, f14: Verdict, f15: Verdict,
                     f16: Verdict, f17: Verdict, f18: Verdict, f19: Verdict, f20: Verdict) };

procedure SecondUnsat(x : Big)
  spec { requires [second_unsat]: Big..f2(x) == unsat(); }
{
  assert [holds_unsat]: Big..f2(x) == unsat();
  assert [fails_unsat]: Big..f4(x) == sat();
};

procedure SecondSat(x : Big)
  spec { requires [second_sat]: Big..f2(x) == sat(); }
{
  assert [holds_sat]: Big..f2(x) == sat();
  assert [fails_sat]: Big..f4(x) == sat();
};

procedure SecondUnknown(x : Big)
  spec { requires [second_unknown]: Big..f2(x) == unknown(); }
{
  assert [holds_unknown]: Big..f2(x) == unknown();
  assert [fails_unknown]: Big..f4(x) == sat();
};
#end

/--
info: Obligation: holds_unsat
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_unsat
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: holds_sat
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_sat
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: holds_unknown
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_unknown
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify verdictNamedConstructorsPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .full, solver := "z3" })

/--
info: Obligation: holds_unsat
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_unsat
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: holds_sat
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_sat
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry

Obligation: holds_unknown
Property: assert
Result: ✅ always true and is reachable from declaration entry

Obligation: fails_unknown
Property: assert
Result: 🔶 can be both true and false and is reachable from declaration entry
-/
#guard_msgs in
#eval Core.verify verdictNamedConstructorsPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .full, solver := "cvc5" })

/--
info: Obligation: holds_unsat
Property: assert
Result: ✅ pass

Obligation: fails_unsat
Property: assert
Result: ❌ fail

Obligation: holds_sat
Property: assert
Result: ✅ pass

Obligation: fails_sat
Property: assert
Result: ❌ fail

Obligation: holds_unknown
Property: assert
Result: ✅ pass

Obligation: fails_unknown
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify verdictNamedConstructorsPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .minimal, solver := "z3" })

/--
info: Obligation: holds_unsat
Property: assert
Result: ✅ pass

Obligation: fails_unsat
Property: assert
Result: ❌ fail

Obligation: holds_sat
Property: assert
Result: ✅ pass

Obligation: fails_sat
Property: assert
Result: ❌ fail

Obligation: holds_unknown
Property: assert
Result: ✅ pass

Obligation: fails_unknown
Property: assert
Result: ❌ fail
-/
#guard_msgs in
#eval Core.verify verdictNamedConstructorsPgm
        (options := { Core.VerifyOptions.quiet with checkLevel := .minimal, solver := "cvc5" })

end Strata
end
---------------------------------------------------------------------
