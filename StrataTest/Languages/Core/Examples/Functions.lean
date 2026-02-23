/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier
import Strata.Languages.Core.CallGraph

---------------------------------------------------------------------
namespace Strata

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
Obligation:
barTest1($__a0) == $__a0

Label: fooEq
Property: assert
Obligation:
true

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
