/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier
import Strata.Languages.Boogie.CallGraph

---------------------------------------------------------------------
namespace Strata

def funcPgm : Program :=
#strata
program Boogie;
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
#eval let (program, _) := Boogie.getProgram funcPgm
      let cg := (Boogie.Program.toFunctionCG program)
      let ans1 := Boogie.CallGraph.getCalleesClosure cg "barTest4"
      let ans2 := Boogie.CallGraph.getCallersClosure cg "barTest1"
      let ans3 := Boogie.CallGraph.getCalleesClosure cg "fooConst"
      Std.format f!"barTest4 callees: {ans1}\n\
                    barTest1 callers: {ans2}\n\
                    fooConst callees: {ans3}"

/--
info: [Strata.Boogie] Type checking succeeded.


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
#eval verify "cvc5" funcPgm

---------------------------------------------------------------------
