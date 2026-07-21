/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

meta section

/-!
# Int-Valued Recursion Termination Checking Tests

Tests termination checking for recursive functions with integer-valued
termination measures (`decreases <int expr>`).
-/

namespace Strata.IntRecursionTermCheckTest

open StrataDDM (Program)

---------------------------------------------------------------------
-- Test 1: int-valued recursion — decreases on int parameter
-- Non-negativity obligation fails without a precondition on n.
---------------------------------------------------------------------

def decreasesIntNoPrecondPgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function bad (@[cases] xs : IntList, n : int) : int
  decreases n
{
  if IntList..isNil(xs) then 0 else bad(IntList..tl(xs), n - 1)
};
#end

/-- info:
Obligation: bad_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_0
Property: assert
Result: ❌ fail

Obligation: bad_terminates_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify decreasesIntNoPrecondPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 2: fib
---------------------------------------------------------------------

def fibPgm : Program :=
#strata
program Core;

rec function fib (n : int) : int
  decreases n
{
  if n <= 1 then n else fib(n - 1) + fib(n - 2)
};
#end

/-- info: [Strata.Core] Type checking succeeded.


VCs:
Label: fib_terminates_0
Property: assert
Obligation:
!(n@1 <= 1) ==> 0 <= n@1 - 1

Label: fib_terminates_1
Property: assert
Obligation:
!(n@1 <= 1) ==> n@1 - 1 < n@1

Label: fib_terminates_2
Property: assert
Obligation:
!(n@1 <= 1) ==> 0 <= n@1 - 2

Label: fib_terminates_3
Property: assert
Obligation:
!(n@1 <= 1) ==> n@1 - 2 < n@1

---
info: Obligation: fib_terminates_0
Property: assert
Result: ✅ pass

Obligation: fib_terminates_1
Property: assert
Result: ✅ pass

Obligation: fib_terminates_2
Property: assert
Result: ✅ pass

Obligation: fib_terminates_3
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify fibPgm (options := .default)

---------------------------------------------------------------------
-- Test 3: factorial — int recursion with precondition
---------------------------------------------------------------------

def factorialPgm : Program :=
#strata
program Core;

rec function factorial (n : int) : int
  requires n >= 0;
  decreases n
{
  if n <= 0 then 1 else n * factorial(n - 1)
};
#end

/-- info:
Obligation: factorial_body_calls_factorial_0
Property: assert
Result: ✅ pass

Obligation: factorial_terminates_0
Property: assert
Result: ✅ pass

Obligation: factorial_terminates_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify factorialPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 4: non-terminating — f(n) calls f(n+1), termination VC fails
---------------------------------------------------------------------

def nonTermIntPgm : Program :=
#strata
program Core;

rec function bad (n : int) : int
  requires n >= 0;
  decreases n
{
  if n <= 0 then 0 else bad(n + 1)
};
#end

/-- info:
Obligation: bad_body_calls_bad_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_0
Property: assert
Result: ✅ pass

Obligation: bad_terminates_1
Property: assert
Result: ❌ fail-/
#guard_msgs in
#eval Core.verify nonTermIntPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 5: power function — two params, decreases on one
---------------------------------------------------------------------

def powerPgm : Program :=
#strata
program Core;

rec function power (base : int, exp : int) : int
  decreases exp
{
  if exp <= 0 then 1 else base * power(base, exp - 1)
};
#end

/-- info:
Obligation: power_terminates_0
Property: assert
Result: ✅ pass

Obligation: power_terminates_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify powerPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 6: compound measure — decreases on expression over params
-- merge of two sorted lists with decreases listLen(l1) + listLen(l2)
-- NOTE: without `nat` or `ensures`, cannot prove length nonneg
---------------------------------------------------------------------

def compoundMeasurePgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function listLen (@[cases] xs : IntList) : int
{
  if IntList..isNil(xs) then 0 else 1 + listLen(IntList..tl(xs))
};

rec function merge (l1 : IntList, l2 : IntList) : IntList
  requires listLen(l1) >= 0;
  requires listLen(l2) >= 0;
  decreases listLen(l1) + listLen(l2)
{
  if IntList..isNil(l1) then l2
  else if IntList..isNil(l2) then l1
  else if IntList..hd(l1) <= IntList..hd(l2)
    then Cons(IntList..hd(l1), merge(IntList..tl(l1), l2))
    else Cons(IntList..hd(l2), merge(l1, IntList..tl(l2)))
};
#end

/-- info:
Obligation: listLen_body_calls_IntList..tl_0
Property: assert
Result: ✅ pass

Obligation: listLen_terminates_0
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..hd_1
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..hd_2
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..tl_3
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_merge_4
Property: assert
Result: ❓ unknown

Obligation: merge_body_calls_merge_5
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..hd_6
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_IntList..tl_7
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_merge_8
Property: assert
Result: ✅ pass

Obligation: merge_body_calls_merge_9
Property: assert
Result: ❓ unknown

Obligation: merge_terminates_0
Property: assert
Result: ❓ unknown

Obligation: merge_terminates_1
Property: assert
Result: ✅ pass

Obligation: merge_terminates_2
Property: assert
Result: ❓ unknown

Obligation: merge_terminates_3
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify compoundMeasurePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 7: compound measure with provable non-negativity
-- decreases m + n where m >= 0 and n >= 0 are preconditions
---------------------------------------------------------------------

def compoundArithPgm : Program :=
#strata
program Core;

rec function diagonal (m : int, n : int) : int
  requires m >= 0;
  requires n >= 0;
  decreases m + n
{
  if m <= 0 then (if n <= 0 then 0 else diagonal(m, n - 1))
  else diagonal(m - 1, n)
};
#end

/-- info:
Obligation: diagonal_body_calls_diagonal_0
Property: assert
Result: ✅ pass

Obligation: diagonal_body_calls_diagonal_1
Property: assert
Result: ✅ pass

Obligation: diagonal_body_calls_diagonal_2
Property: assert
Result: ✅ pass

Obligation: diagonal_body_calls_diagonal_3
Property: assert
Result: ✅ pass

Obligation: diagonal_terminates_0
Property: assert
Result: ✅ pass

Obligation: diagonal_terminates_1
Property: assert
Result: ✅ pass

Obligation: diagonal_terminates_2
Property: assert
Result: ✅ pass

Obligation: diagonal_terminates_3
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify compoundArithPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 8: mutual int recursion
---------------------------------------------------------------------

def mutualIntRecPgm : Program :=
#strata
program Core;

rec function isEven (n : int) : bool
  requires n >= 0;
  decreases n
{
  if n <= 0 then true else isOdd(n - 1)
}
function isOdd (n : int) : bool
  requires n >= 0;
  decreases n
{
  if n <= 0 then false else isEven(n - 1)
};
#end

/-- info:
Obligation: isEven_body_calls_isOdd_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_isEven_0
Property: assert
Result: ✅ pass

Obligation: isEven_terminates_0
Property: assert
Result: ✅ pass

Obligation: isEven_terminates_1
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_0
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify mutualIntRecPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 8b: mutual int recursion — concrete evaluation via PE
---------------------------------------------------------------------

def mutualIntRecConcretePgm : Program :=
#strata
program Core;

rec function isEven (n : int) : bool
  requires n >= 0;
  decreases n
{
  if n <= 0 then true else isOdd(n - 1)
}
function isOdd (n : int) : bool
  requires n >= 0;
  decreases n
{
  if n <= 0 then false else isEven(n - 1)
};

procedure TestMutualConcrete() spec {
  ensures true;
}
{
  assert [even4]: isEven(4) == true;
  assert [odd3]: isOdd(3) == true;
  assert [even3]: isEven(3) == false;
  assert [odd4]: isOdd(4) == false;
};
#end

/-- info:
Obligation: isEven_body_calls_isOdd_0
Property: assert
Result: ✅ pass

Obligation: isOdd_body_calls_isEven_0
Property: assert
Result: ✅ pass

Obligation: isEven_terminates_0
Property: assert
Result: ✅ pass

Obligation: isEven_terminates_1
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_0
Property: assert
Result: ✅ pass

Obligation: isOdd_terminates_1
Property: assert
Result: ✅ pass

Obligation: assert_even4_calls_isEven_0
Property: assert
Result: ✅ pass

Obligation: even4
Property: assert
Result: ✅ pass

Obligation: assert_odd3_calls_isOdd_0
Property: assert
Result: ✅ pass

Obligation: odd3
Property: assert
Result: ✅ pass

Obligation: assert_even3_calls_isEven_0
Property: assert
Result: ✅ pass

Obligation: even3
Property: assert
Result: ✅ pass

Obligation: assert_odd4_calls_isOdd_0
Property: assert
Result: ✅ pass

Obligation: odd4
Property: assert
Result: ✅ pass

Obligation: TestMutualConcrete_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify mutualIntRecConcretePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 9: int-recursive function is a pure UF — no definitional axioms.
-- Cannot prove fib(n) == fib(n-1) + fib(n-2) since fib has no axioms.
---------------------------------------------------------------------

def intRecUFPgm : Program :=
#strata
program Core;

rec function fib (n : int) : int
  requires n >= 0;
  decreases n
{
  if n <= 1 then n else fib(n - 1) + fib(n - 2)
};

procedure TestFibUF(n : int) spec {
  requires n > 1;
  ensures true;
}
{
  assert [fibDef]: fib(n) == fib(n - 1) + fib(n - 2);
};
#end

/-- info:
Obligation: fib_body_calls_fib_0
Property: assert
Result: ✅ pass

Obligation: fib_body_calls_fib_1
Property: assert
Result: ✅ pass

Obligation: fib_terminates_0
Property: assert
Result: ✅ pass

Obligation: fib_terminates_1
Property: assert
Result: ✅ pass

Obligation: fib_terminates_2
Property: assert
Result: ✅ pass

Obligation: fib_terminates_3
Property: assert
Result: ✅ pass

Obligation: assert_fibDef_calls_fib_0
Property: assert
Result: ✅ pass

Obligation: assert_fibDef_calls_fib_1
Property: assert
Result: ✅ pass

Obligation: assert_fibDef_calls_fib_2
Property: assert
Result: ✅ pass

Obligation: fibDef
Property: assert
Result: ❌ fail

Obligation: TestFibUF_ensures_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify intRecUFPgm (options := .quiet)

---------------------------------------------------------------------
-- Test 10: concrete evaluation — factorial evaluates concretely
---------------------------------------------------------------------

def factorialConcretePgm : Program :=
#strata
program Core;

rec function factorial (n : int) : int
  requires n >= 0;
  decreases n
{
  if n <= 0 then 1 else n * factorial(n - 1)
};

procedure TestFactConcrete() spec {
  ensures true;
}
{
  assert [fact0]: factorial(0) == 1;
  assert [fact3]: factorial(3) == 6;
  assert [fact5]: factorial(5) == 120;
};
#end

/-- info:
Obligation: factorial_body_calls_factorial_0
Property: assert
Result: ✅ pass

Obligation: factorial_terminates_0
Property: assert
Result: ✅ pass

Obligation: factorial_terminates_1
Property: assert
Result: ✅ pass

Obligation: assert_fact0_calls_factorial_0
Property: assert
Result: ✅ pass

Obligation: fact0
Property: assert
Result: ✅ pass

Obligation: assert_fact3_calls_factorial_0
Property: assert
Result: ✅ pass

Obligation: fact3
Property: assert
Result: ✅ pass

Obligation: assert_fact5_calls_factorial_0
Property: assert
Result: ✅ pass

Obligation: fact5
Property: assert
Result: ✅ pass

Obligation: TestFactConcrete_ensures_0
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify factorialConcretePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 11: @[cases] with int-valued decreases — int measure takes priority
-- but @[cases] allows unfolding
---------------------------------------------------------------------

def casesWithIntMeasurePgm : Program :=
#strata
program Core;

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

rec function sumFirst (@[cases] xs : IntList, n : int) : int
  requires n >= 0;
  decreases n
{
  if n <= 0 then 0
  else if IntList..isNil(xs) then 0
  else IntList..hd(xs) + sumFirst(IntList..tl(xs), n - 1)
};

procedure TestSumFirstCons(h : int, t : IntList, n : int) spec {
  requires n >= 1;
  ensures true;
}
{
  assert [consUnfold]: sumFirst(Cons(h, t), 1) == h + sumFirst(t, 0);
};
#end

/-- info:
Obligation: sumFirst_body_calls_IntList..hd_0
Property: assert
Result: ✅ pass

Obligation: sumFirst_body_calls_IntList..tl_1
Property: assert
Result: ✅ pass

Obligation: sumFirst_body_calls_sumFirst_2
Property: assert
Result: ✅ pass

Obligation: sumFirst_terminates_0
Property: assert
Result: ✅ pass

Obligation: sumFirst_terminates_1
Property: assert
Result: ✅ pass

Obligation: assert_consUnfold_calls_sumFirst_0
Property: assert
Result: ✅ pass

Obligation: assert_consUnfold_calls_sumFirst_1
Property: assert
Result: ✅ pass

Obligation: consUnfold
Property: assert
Result: ✅ pass

Obligation: TestSumFirstCons_ensures_1
Property: assert
Result: ✅ pass -/
#guard_msgs in
#eval Core.verify casesWithIntMeasurePgm (options := .quiet)

---------------------------------------------------------------------
-- Test 12: constant measure `decreases 10` should fail termination
---------------------------------------------------------------------

def constantMeasureFailPgm : Program :=
#strata
program Core;

rec function loop (n : int) : int
  decreases 10
{
  if n <= 0 then 0 else loop(n - 1)
};
#end

/-- info:
Obligation: loop_terminates_0
Property: assert
Result: ✅ pass

Obligation: loop_terminates_1
Property: assert
Result: ❌ fail -/
#guard_msgs in
#eval Core.verify constantMeasureFailPgm (options := .quiet)

end Strata.IntRecursionTermCheckTest

end
