/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Simple Datatype Example: Option

This example demonstrates basic datatype usage with the Option type,
including constructors, testers, and destructors.
-/

def optionPgm : Program :=
#strata
program Boogie;

datatype Option (α : Type) {
  None(),
  Some(value: α)
};

procedure testOption(x: int) returns (r: Option int)
spec {
  ensures [r_is_some]: (Option$isSome(r));
  ensures [r_value]: (Option$SomeProj0(r) == x);
}
{
  r := Some(x);
  assert [r_is_some]: Option$isSome(r);
  assert [r_value_correct]: (Option$SomeProj0(r) == x);
};
#end

/-
/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram optionPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_some
Assumptions:


Proof Obligation:
(~Option$isSome (~Some $__x0))

Label: r_value_correct
Assumptions:


Proof Obligation:
((~Option$SomeProj0 (~Some $__x0)) == $__x0)

Label: testOption_ensures_0
Assumptions:


Proof Obligation:
(~Option$isSome (~Some $__x0))

Label: testOption_ensures_1
Assumptions:


Proof Obligation:
((~Option$SomeProj0 (~Some $__x0)) == $__x0)

---
info:
Obligation: r_is_some
Result: verified

Obligation: r_value_correct
Result: verified

Obligation: testOption_ensures_0
Result: verified

Obligation: testOption_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" optionPgm
-/

---------------------------------------------------------------------

def optionNonePgm : Program :=
#strata
program Boogie;

datatype Option (α : Type) {
  None(),
  Some(value: α)
};

procedure testNone() returns (r: Option int)
spec {
  ensures [r_is_none]: (Option$isNone(r));
  ensures [r_not_some]: (!Option$isSome(r));
}
{
  r := None();
  assert [r_is_none]: Option$isNone(r);
  assert [r_not_some]: !Option$isSome(r);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionNonePgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_none
Assumptions:


Proof Obligation:
(~Option$isNone ~None)

Label: r_not_some
Assumptions:


Proof Obligation:
(~Bool.Not (~Option$isSome ~None))

Label: testNone_ensures_0
Assumptions:


Proof Obligation:
(~Option$isNone ~None)

Label: testNone_ensures_1
Assumptions:


Proof Obligation:
(~Bool.Not (~Option$isSome ~None))

---
info:
Obligation: r_is_none
Result: verified

Obligation: r_not_some
Result: verified

Obligation: testNone_ensures_0
Result: verified

Obligation: testNone_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" optionNonePgm
-/

---------------------------------------------------------------------

def optionMatchPgm : Program :=
#strata
program Boogie;

datatype Option (α : Type) {
  None(),
  Some(value: α)
};

procedure getOrDefault(opt: Option int, default: int) returns (result: int)
spec {
  ensures [none_case]: (Option$isNone(opt) ==> (result == default));
  ensures [some_case]: (Option$isSome(opt) ==> (result == Option$SomeProj0(opt)));
}
{
  if (Option$isSome(opt)) {
    result := Option$SomeProj0(opt);
  } else {
    result := default;
  }
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram optionMatchPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: getOrDefault_ensures_0
Assumptions:


Proof Obligation:
((~Bool.Implies (~Option$isNone $__opt0)) ($__result1 == $__default0))

Label: getOrDefault_ensures_1
Assumptions:


Proof Obligation:
((~Bool.Implies (~Option$isSome $__opt0)) ($__result1 == (~Option$SomeProj0 $__opt0)))

---
info:
Obligation: getOrDefault_ensures_0
Result: verified

Obligation: getOrDefault_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" optionMatchPgm
-/

---------------------------------------------------------------------

end Strata
