/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

/-!
# Datatype Typing Tests

Tests for the Core typechecker's handling of datatype declarations:
strict positivity, uniformity, nesting, inhabitedness, and name clashes.
-/

namespace Strata.DatatypeTypingTests

---------------------------------------------------------------------
-- Test 1: Non-Positive Occurrence (direct)
---------------------------------------------------------------------

def nonPositiveDirectPgm : Program :=
#strata
program Core;

datatype OK {mkOK(x: int)};

datatype Bad () { MkBad(f: Bad -> int) };
#end

/--
info: error: Error in constructor MkBad: Non-strictly positive occurrence of Bad in type (arrow Bad int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonPositiveDirectPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 2: Non-Strictly Positive (nested under two arrows)
---------------------------------------------------------------------

def nonPositiveNestedPgm : Program :=
#strata
program Core;

datatype Bad (a : Type) { Base(), C(x: (Bad a -> int) -> int) };
#end

/--
info: error: Error in constructor C: Non-strictly positive occurrence of Bad in type (arrow (arrow (Bad a) int) int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonPositiveNestedPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 3: Non-Strictly Positive (not in outermost arrow)
---------------------------------------------------------------------

def nonPositiveInnerPgm : Program :=
#strata
program Core;

datatype Bad (a : Type) { Base(), C(x: int -> (Bad a -> int)) };
#end

/--
info: error: Error in constructor C: Non-strictly positive occurrence of Bad in type (arrow (Bad a) int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonPositiveInnerPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 4: Strictly Positive (should pass)
---------------------------------------------------------------------

def strictlyPositivePgm : Program :=
#strata
program Core;

datatype Good (a : Type) { Base(), C(x: int -> int -> Good a) };
#end

/-- info: true -/
#guard_msgs in
#eval TransM.run Inhabited.default (translateProgram strictlyPositivePgm) |>.snd |>.isEmpty

---------------------------------------------------------------------
-- Test 5: Non-Uniform Recursive Occurrence
---------------------------------------------------------------------

def nonUniformPgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

datatype Nonunif (a : Type) { Base(), C(x: int -> Nonunif (List a)) };
#end

/--
info: error: Error in constructor C: Non-uniform occurrence of Nonunif, which is applied to [(List a)] when it should be applied to [a]
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nonUniformPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 6: Nested Datatype
---------------------------------------------------------------------

def nestedDatatypePgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

datatype Nest (a : Type) { Base(), MkNest(xs: List (Nest a)) };
#end

/--
info: error: Error in constructor MkNest: Datatype Nest appears nested inside (List (Nest a)). Nested datatypes are not supported in Strata Core.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nestedDatatypePgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 7: Type Depending on Previously Defined Type
---------------------------------------------------------------------

def previouslyDefinedTypePgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

datatype Wrapper () { MkWrapper(xs: List int) };
#end

/-- info: [Strata.Core] Type checking succeeded.

---
info: ok: datatype List (a : Type) {(
  (Nil())),
  (Cons(hd : a, tl : (List a)))
};
datatype Wrapper {
  (MkWrapper(xs : (List int)))
}; -/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram previouslyDefinedTypePgm) |>.fst).stripMetaData
---------------------------------------------------------------------
-- Test 8: Nested Datatype with Map
---------------------------------------------------------------------

def nestedMapPgm : Program :=
#strata
program Core;

datatype Nest2 (a : Type) { Base(), MkNest2(xs: Map int (Nest2 a)) };
#end

/--
info: error: Error in constructor MkNest2: Datatype Nest2 appears nested inside (Map int (Nest2 a)). Nested datatypes are not supported in Strata Core.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram nestedMapPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 9: Mutually Recursive Nesting
---------------------------------------------------------------------

def mutualNestedPgm : Program :=
#strata
program Core;

datatype List (a : Type) { Nil(), Cons(hd: a, tl: List a) };

forward type MutNestA (a : Type);
forward type MutNestB (a : Type);
mutual
  datatype MutNestA (a : Type) { MkA(x: List (MutNestB a)) };
  datatype MutNestB (a : Type) { BBase(), MkB(x: MutNestA a) };
end;
#end

/--
info: error: Error in constructor MkA: Datatype MutNestB appears nested inside (List (MutNestB a)). Nested datatypes are not supported in Strata Core.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram mutualNestedPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 10: Constructor Name Clashes with Built-in Function
---------------------------------------------------------------------

def constrClashPgm : Program :=
#strata
program Core;

datatype Bad () { select(x: int) };
#end

/--
info: error: A function of name select already exists! Redefinitions are not allowed.
Existing Function: func select : ∀[k, v]. ((m : (Map k v)) (i : k)) → v;
New Function:func select :  ((x : int)) → Bad;
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram constrClashPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 11: Non-Strictly Positive in Mutual Block
---------------------------------------------------------------------

def mutualNonPositivePgm : Program :=
#strata
program Core;

forward type BadA;
forward type BadB;
mutual
  datatype BadA () { MkA(f: BadB -> int) };
  datatype BadB () { BadBBase(), MkB(a: BadA) };
end;
#end

/--
info: error: Error in constructor MkA: Non-strictly positive occurrence of BadB in type (arrow BadB int)
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram mutualNonPositivePgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 12: Uninhabited Datatype
---------------------------------------------------------------------

def uninhabitedPgm : Program :=
#strata
program Core;

datatype Void () { MkVoid(x: Void) };
#end

/--
info: error: Error: datatype Void not inhabited
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram uninhabitedPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 13: Mutually Uninhabited Datatypes
---------------------------------------------------------------------

def mutualUninhabitedPgm : Program :=
#strata
program Core;

forward type Bad1;
forward type Bad2;
mutual
  datatype Bad1 () { B1(x: Bad2) };
  datatype Bad2 () { B2(x: Bad1) };
end;
#end

/--
info: error: Error: datatype Bad1 not inhabited
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram mutualUninhabitedPgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 14: Three-Way Mutual Uninhabited Cycle
---------------------------------------------------------------------

def threeWayCyclePgm : Program :=
#strata
program Core;

forward type Cycle1;
forward type Cycle2;
forward type Cycle3;
mutual
  datatype Cycle1 () { C1(x: Cycle2) };
  datatype Cycle2 () { C2(x: Cycle3) };
  datatype Cycle3 () { C3(x: Cycle1) };
end;
#end

/--
info: error: Error: datatype Cycle1 not inhabited
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram threeWayCyclePgm) |>.fst).stripMetaData

end Strata.DatatypeTypingTests
