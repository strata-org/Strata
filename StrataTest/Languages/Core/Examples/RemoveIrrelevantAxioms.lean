/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def irrelevantAxiomsTestPgm : Strata.Program :=
#strata
program Core;
type StrataHeap;
type StrataRef;
type StrataField (t: Type);

// Constants
const a : bool;
const b : bool;
const c : bool;
const d : bool;

// Functions
function f(x0 : int) : (bool);

// Axioms
axiom [ax_l11c1]: (forall x: int :: ((x >= 0) ==> f(x)));

// Uninterpreted procedures
// Implementations
procedure P() returns ()

{
  anon0: {
    assert ((a ==> ((b ==> c) ==> d)) <==> (a ==> ((b ==> c) ==> d)));
    assert ((a ==> (b ==> c)) <==> ((a ==> b) ==> c));
    assert f(23);
    assert f(-(5));
  }
  end : {}
};

procedure Q0(x : int) returns ()

{
  anon0: {
    assert (x == 2);
    assert (x == 2);
  }
  end : {}
};

procedure Q1(x : int) returns ()

{
  anon0: {
    assert (x == 2);
    assert (x == 2);
  }
  end : {}
};

procedure Q2(x : int) returns ()

{
  anon0: {
    assert (x == 2);
    assert (x == 2);
  }
  end : {}
};

procedure Q3(x : int) returns ()

{
  anon0: {
    assert (x == 2);
    assert (x == 2);
  }
  end : {}
};
#end

---------------------------------------------------------------------

/--
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: 🟡 unknown

Obligation: assert_2
Property: assert
Result: ✅ pass

Obligation: assert_3
Property: assert
Result: 🟡 unknown

Obligation: assert_4
Property: assert
Result: ❌ fail
Model:
($__x0, 3)

Obligation: assert_5
Property: assert
Result: ❌ fail
Model:
($__x0, 3)

Obligation: assert_6
Property: assert
Result: ❌ fail
Model:
($__x1, 3)

Obligation: assert_7
Property: assert
Result: ❌ fail
Model:
($__x1, 3)

Obligation: assert_8
Property: assert
Result: ❌ fail
Model:
($__x2, 3)

Obligation: assert_9
Property: assert
Result: ❌ fail
Model:
($__x2, 3)

Obligation: assert_10
Property: assert
Result: ❌ fail
Model:
($__x3, 3)

Obligation: assert_11
Property: assert
Result: ❌ fail
Model:
($__x3, 3)
-/
#guard_msgs in
#eval verify "z3" irrelevantAxiomsTestPgm
        (options := {Options.quiet with removeIrrelevantAxioms := true})

---------------------------------------------------------------------

/--
info:
Obligation: assert_0
Property: assert
Result: ✅ pass

Obligation: assert_1
Property: assert
Result: 🟡 unknown

Obligation: assert_2
Property: assert
Result: ✅ pass

Obligation: assert_3
Property: assert
Result: 🟡 unknown

Obligation: assert_4
Property: assert
Result: 🟡 unknown

Obligation: assert_5
Property: assert
Result: 🟡 unknown

Obligation: assert_6
Property: assert
Result: 🟡 unknown

Obligation: assert_7
Property: assert
Result: 🟡 unknown

Obligation: assert_8
Property: assert
Result: 🟡 unknown

Obligation: assert_9
Property: assert
Result: 🟡 unknown

Obligation: assert_10
Property: assert
Result: 🟡 unknown

Obligation: assert_11
Property: assert
Result: 🟡 unknown
-/
#guard_msgs in
#eval verify "z3" irrelevantAxiomsTestPgm
        (options := {Options.quiet with removeIrrelevantAxioms := false})

---------------------------------------------------------------------
