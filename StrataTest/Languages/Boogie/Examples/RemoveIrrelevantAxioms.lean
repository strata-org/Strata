/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Boogie.Verifier

---------------------------------------------------------------------
namespace Strata

def irrelevantAxiomsTestPgm1 : Strata.Program :=
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


Obligation assert_5: could not be proved!

Result: failed


Obligation assert_6: could not be proved!

Result: failed


Obligation assert_7: could not be proved!

Result: failed


Obligation assert_8: could not be proved!

Result: failed


Obligation assert_9: could not be proved!

Result: failed


Obligation assert_10: could not be proved!

Result: failed


Obligation assert_11: could not be proved!

Result: failed
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

Obligation: assert_5
Result: failed

Obligation: assert_6
Result: failed

Obligation: assert_7
Result: failed

Obligation: assert_8
Result: failed

Obligation: assert_9
Result: failed

Obligation: assert_10
Result: failed

Obligation: assert_11
Result: failed
-/
#guard_msgs in
#eval verify "z3" irrelevantAxiomsTestPgm1 Inhabited.default {Options.quiet with removeIrrelevantAxioms := .Aggressive}

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
#eval verify "z3" irrelevantAxiomsTestPgm1 Inhabited.default {Options.quiet with removeIrrelevantAxioms := .Precise}
-- Note: Precise irrelevant axiom removal performs just like no axiom removal in
-- this case.

---------------------------------------------------------------------

def irrelevantAxiomsTestPgm2 : Strata.Program :=
#strata
program Boogie;

function f(x : int) : bool;
function g(x : int) : bool;
function h(x : int) : bool;

function f2(x : int) : bool { f(x) }
function fh(x : int) : bool { f2(x) || h(x) }

function h2(x : int) : bool { h(x) }

axiom [f_eq_g]: (forall x : int :: f(x) == g(x));
axiom [g_eq]: (forall x : int :: g(x) == false);
axiom [h_eq]: (forall x : int :: h(x) == false);
axiom [h2_eq]: (forall x : int :: h2(x) == false);

#end

-- Note `g_eq` is detected as relevant for `f` because `g_eq` contains `g`,
-- which is relevant to axiom `f_eq_g`, which is also relevant to `f`.
/-- info: ["h_eq", "h2_eq"] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["f"]

/-- info: ["h_eq", "h2_eq"] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["g"]

-- Note `h2_eq` is detected as relevant for `h` because `h2` is a caller of `h`.
/-- info: ["f_eq_g", "g_eq"] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["h"]

-- Note `h_eq` is detected as relevant for `h2` because `h` is a callee of `h2`.
/-- info: ["f_eq_g", "g_eq"] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["h2"]

-- Similarly, `f2`'s callee, `f` is considered in the irrelevant axiom
-- computation.
/-- info: ["h_eq", "h2_eq"] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["f2"]

/-- info: [] -/
#guard_msgs in
#eval let (program, _) := Boogie.getProgram irrelevantAxiomsTestPgm2
      Boogie.Program.getIrrelevantAxioms program ["fh"]

---------------------------------------------------------------------
