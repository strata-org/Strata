/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def funcEnv : Environment :=
#strata
program Boogie;
const fooConst : int;
inline function fooTest() : int { fooConst }

function barTest1(x : int) : int { x }
inline function barTest2(y : int) : int { y }

procedure fooProc(a : int) returns () {
  assert [barEq]: (barTest1(a) == barTest2(a));
  assert [fooEq]: (fooConst == fooTest);
};

#end

/--
info: [Strata.Boogie] Type checking succeeded.


VCs:
Label: barEq
Assumptions:
Proof Obligation:
((~barTest1 $__a0) == $__a0)

Label: fooEq
Assumptions:
Proof Obligation:
#true

Wrote problem to vcs/barEq.smt2.
Wrote problem to vcs/fooEq.smt2.
---
info:
Obligation: barEq
Result: verified

Obligation: fooEq
Result: verified
-/
#guard_msgs in
#eval verify "cvc5" funcEnv

---------------------------------------------------------------------
