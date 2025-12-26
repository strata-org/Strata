/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

/-!
# Simple Datatype Example: IntOption

This example demonstrates basic datatype usage with a concrete IntOption type,
including constructors, testers, and destructors.
-/

def intOptionPgm : Program :=
#strata
program Boogie;

datatype IntOption {
  None(),
  Some(value: int)
};

procedure testIntOption(x: int) returns (r: IntOption)
spec {
  ensures [r_is_some]: (IntOption..isSome(r));
  ensures [r_value]: (IntOption..SomeProj0(r) == x);
}
{
  r := Some(x);
  assert [r_is_some]: IntOption..isSome(r);
  assert [r_value_correct]: (IntOption..SomeProj0(r) == x);
};
#end

/-
/-- info: true -/
#guard_msgs in
-- No errors in translation.
#eval TransM.run Inhabited.default (translateProgram intOptionPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_some
Assumptions:


Proof Obligation:
(~IntOption$isSome (~Some $__x0))

Label: r_value_correct
Assumptions:


Proof Obligation:
((~IntOption$SomeProj0 (~Some $__x0)) == $__x0)

Label: testIntOption_ensures_0
Assumptions:


Proof Obligation:
(~IntOption$isSome (~Some $__x0))

Label: testIntOption_ensures_1
Assumptions:


Proof Obligation:
((~IntOption$SomeProj0 (~Some $__x0)) == $__x0)

---
info:
Obligation: r_is_some
Result: verified

Obligation: r_value_correct
Result: verified

Obligation: testIntOption_ensures_0
Result: verified

Obligation: testIntOption_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" intOptionPgm
-/

---------------------------------------------------------------------

def intOptionNonePgm : Program :=
#strata
program Boogie;

datatype IntOption {
  None(),
  Some(value: int)
};

procedure testNone() returns (r: IntOption)
spec {
  ensures [r_is_none]: (IntOption$isNone(r));
  ensures [r_not_some]: (!IntOption$isSome(r));
}
{
  r := None();
  assert [r_is_none]: IntOption$isNone(r);
  assert [r_not_some]: !IntOption$isSome(r);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intOptionNonePgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: r_is_none
Assumptions:


Proof Obligation:
(~IntOption$isNone ~None)

Label: r_not_some
Assumptions:


Proof Obligation:
(~Bool.Not (~IntOption$isSome ~None))

Label: testNone_ensures_0
Assumptions:


Proof Obligation:
(~IntOption$isNone ~None)

Label: testNone_ensures_1
Assumptions:


Proof Obligation:
(~Bool.Not (~IntOption$isSome ~None))

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
#eval verify "cvc5" intOptionNonePgm
-/

---------------------------------------------------------------------

def intOptionMatchPgm : Program :=
#strata
program Boogie;

datatype IntOption {
  None(),
  Some(value: int)
};

procedure getOrDefault(opt: IntOption, default: int) returns (result: int)
spec {
  ensures [none_case]: (IntOption$isNone(opt) ==> (result == default));
  ensures [some_case]: (IntOption$isSome(opt) ==> (result == IntOption$SomeProj0(opt)));
}
{
  if (IntOption$isSome(opt)) {
    result := IntOption$SomeProj0(opt);
  } else {
    result := default;
  }
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram intOptionMatchPgm) |>.snd |>.isEmpty
-/

/-
/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: getOrDefault_ensures_0
Assumptions:


Proof Obligation:
((~Bool.Implies (~IntOption$isNone $__opt0)) ($__result1 == $__default0))

Label: getOrDefault_ensures_1
Assumptions:


Proof Obligation:
((~Bool.Implies (~IntOption$isSome $__opt0)) ($__result1 == (~IntOption$SomeProj0 $__opt0)))

---
info:
Obligation: getOrDefault_ensures_0
Result: verified

Obligation: getOrDefault_ensures_1
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" intOptionMatchPgm
-/

---------------------------------------------------------------------

/-!
# Additional Non-Polymorphic Datatype Examples

These examples demonstrate the same capabilities with different concrete types
to ensure comprehensive testing without polymorphism.
-/

def boolResultPgm : Program :=
#strata
program Boogie;

datatype BoolResult {
  Error(message: int),
  Success(value: bool)
};

procedure testBoolResult(b: bool) returns (r: BoolResult)
spec {
  ensures [r_is_success]: (BoolResult$isSuccess(r));
  ensures [r_value]: (BoolResult$SuccessProj0(r) == b);
}
{
  r := Success(b);
  assert [r_is_success]: BoolResult$isSuccess(r);
  assert [r_value_correct]: (BoolResult$SuccessProj0(r) == b);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram boolResultPgm) |>.snd |>.isEmpty
-/

---------------------------------------------------------------------

def pairPgm : Program :=
#strata
program Boogie;

datatype IntPair {
  Pair(first: int, second: int)
};

procedure makePair(x: int, y: int) returns (p: IntPair)
spec {
  ensures [first_correct]: (IntPair$PairProj0(p) == x);
  ensures [second_correct]: (IntPair$PairProj1(p) == y);
}
{
  p := Pair(x, y);
  assert [first_check]: (IntPair$PairProj0(p) == x);
  assert [second_check]: (IntPair$PairProj1(p) == y);
};
#end

/-
/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram pairPgm) |>.snd |>.isEmpty
-/

---------------------------------------------------------------------

end Strata
