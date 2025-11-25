/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def irrelevantAxiomsTestPgm : Strata.Program :=
#strata
program Boogie;
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

Obligation assert_1: could not be proved!

Result: unknown


Obligation assert_3: could not be proved!

Result: unknown


Obligation assert_4: could not be proved!

Result: failed
CEx: ($__x0, 3)


Obligation assert_5: could not be proved!

Result: failed
CEx: ($__x0, 3)


Obligation assert_6: could not be proved!

Result: failed
CEx: ($__x1, 3)


Obligation assert_7: could not be proved!

Result: failed
CEx: ($__x1, 3)


Obligation assert_8: could not be proved!

Result: failed
CEx: ($__x2, 3)


Obligation assert_9: could not be proved!

Result: failed
CEx: ($__x2, 3)


Obligation assert_10: could not be proved!

Result: failed
CEx: ($__x3, 3)


Obligation assert_11: could not be proved!

Result: failed
CEx: ($__x3, 3)
---
info:
Obligation: assert_0
Result: verified

Obligation: assert_1
Result: unknown

Obligation: assert_2
Result: verified

Obligation: assert_3
Result: unknown

Obligation: assert_4
Result: failed
CEx: ($__x0, 3)

Obligation: assert_5
Result: failed
CEx: ($__x0, 3)

Obligation: assert_6
Result: failed
CEx: ($__x1, 3)

Obligation: assert_7
Result: failed
CEx: ($__x1, 3)

Obligation: assert_8
Result: failed
CEx: ($__x2, 3)

Obligation: assert_9
Result: failed
CEx: ($__x2, 3)

Obligation: assert_10
Result: failed
CEx: ($__x3, 3)

Obligation: assert_11
Result: failed
CEx: ($__x3, 3)
-/
#guard_msgs in
#eval verify "z3" irrelevantAxiomsTestPgm Inhabited.default {Options.quiet with removeIrrelevantAxioms := true}

---------------------------------------------------------------------

/--
info:

Obligation assert_1: could not be proved!

Result: unknown


Obligation assert_3: could not be proved!

Result: unknown


Obligation assert_4: could not be proved!

Result: unknown


Obligation assert_5: could not be proved!

Result: unknown


Obligation assert_6: could not be proved!

Result: unknown


Obligation assert_7: could not be proved!

Result: unknown


Obligation assert_8: could not be proved!

Result: unknown


Obligation assert_9: could not be proved!

Result: unknown


Obligation assert_10: could not be proved!

Result: unknown


Obligation assert_11: could not be proved!

Result: unknown
---
info:
Obligation: assert_0
Result: verified

Obligation: assert_1
Result: unknown

Obligation: assert_2
Result: verified

Obligation: assert_3
Result: unknown

Obligation: assert_4
Result: unknown

Obligation: assert_5
Result: unknown

Obligation: assert_6
Result: unknown

Obligation: assert_7
Result: unknown

Obligation: assert_8
Result: unknown

Obligation: assert_9
Result: unknown

Obligation: assert_10
Result: unknown

Obligation: assert_11
Result: unknown
-/
#guard_msgs in
#eval verify "z3" irrelevantAxiomsTestPgm Inhabited.default {Options.quiet with removeIrrelevantAxioms := false}

---------------------------------------------------------------------
