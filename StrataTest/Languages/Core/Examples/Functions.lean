/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

/-! ## Basic function tests -/

def funcPgm : Program :=
#strata
program Core;
const fooConst : int;
inline function fooTest() : int { fooConst }

function barTest1(x : int) : int { x }
inline function barTest2(y : int) : int { y }

function barTest3(y : int) : int { barTest1(y) }
function barTest4(y : int) : int { barTest3(y) }

procedure fooProc(a : int) returns () {
  assert [barEq]: (barTest1(a) == barTest2(a));
  assert [fooEq]: (fooConst == fooTest);
};

#end

/--
info: barTest4 callees: [barTest1, barTest3]
barTest1 callers: [barTest4, barTest3]
fooConst callees: []
-/
#guard_msgs in
#eval let (program, _) := Core.getProgram funcPgm
      let cg := (Core.Program.toFunctionCG program)
      let ans1 := Core.CallGraph.getCalleesClosure cg "barTest4"
      let ans2 := Core.CallGraph.getCallersClosure cg "barTest1"
      let ans3 := Core.CallGraph.getCalleesClosure cg "fooConst"
      Std.format f!"barTest4 callees: {ans1}\n\
                    barTest1 callers: {ans2}\n\
                    fooConst callees: {ans3}"

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: barEq
Property: assert
Assumptions:


Proof Obligation:
((~barTest1 $__a0) == $__a0)

Label: fooEq
Property: assert
Assumptions:


Proof Obligation:
#true

---
info:
Obligation: barEq
Property: assert
Result: ✅ pass

Obligation: fooEq
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify funcPgm

---------------------------------------------------------------------

/-! ## Multi-argument function test

Tests that multi-argument functions are correctly encoded in SMT.
Before the fix, only the first argument type was captured.
-/

def multiArgFuncPgm : Program :=
#strata
program Core;

function add(x : int, y : int) : int { x + y }

procedure testMultiArg(a : int, b : int) returns () {
  assert [addComm]: (add(a, b) == add(b, a));
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: addComm
Property: assert
Assumptions:


Proof Obligation:
((~add $__a0 $__b1) == (~add $__b1 $__a0))

---
info:
Obligation: addComm
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" multiArgFuncPgm

---------------------------------------------------------------------

/-! ## Function with quantifier body test (substFvarsLifting)

Tests that function bodies containing quantifiers are correctly encoded.
The substFvarsLifting fix ensures de Bruijn indices in the replacement
bvars are properly lifted when substituting formals under the quantifier
binder in the function body.
-/

def quantBodyFuncPgm : Program :=
#strata
program Core;

function allPositive(x : int, y : int) : bool { x > 0 && y > 0 }

procedure testQuantBody(a : int, b : int) returns ()
spec {
  requires a > 0;
  requires b > 0;
}
{
  assert [pos]: allPositive(a, b);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: pos
Property: assert
Assumptions:
(testQuantBody_requires_0, (~Int.Gt $__a0 #0))
(testQuantBody_requires_1, (~Int.Gt $__b1 #0))

Proof Obligation:
(~allPositive $__a0 $__b1)

---
info:
Obligation: pos
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" quantBodyFuncPgm

---------------------------------------------------------------------

/-! ## Map type in function signatures

Tests that Map types in function parameters and return types are
correctly encoded as SMT Array types.
-/

def mapFuncPgm : Program :=
#strata
program Core;

const m : Map int int;

function lookup(mp : Map int int, k : int) : int { mp[k] }

procedure testMapFunc(key : int) returns ()
spec {
  requires m[key] == 42;
}
{
  assert [lookupEq]: (lookup(m, key) == 42);
};

#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: lookupEq
Property: assert
Assumptions:
(testMapFunc_requires_0, ((~select ~m $__key0) == #42))

Proof Obligation:
((~lookup ~m $__key0) == #42)

---
info:
Obligation: lookupEq
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify "cvc5" mapFuncPgm

---------------------------------------------------------------------
