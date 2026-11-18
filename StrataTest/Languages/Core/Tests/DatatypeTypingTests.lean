/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Verifier
import StrataDDM.Integration.Lean.HashCommands
meta import StrataTest.Languages.Core.Tests.TestUtil

meta section
open StrataDDM (Program)

/-!
# Datatype Typing Tests

Tests for the Core typechecker's handling of datatype declarations:
strict positivity, uniformity, nesting, inhabitedness, name clashes, duplicate or reserved
type parameters, and agreement of type parameters across a mutual block.
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
info: ok: program Core;

datatype List (a : Type) {
  Nil(),
  Cons(hd : a, tl : List a)
};
datatype Wrapper {
  MkWrapper(xs : List int)
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

  datatype MutNestA (a : Type) { MkA(x: List (MutNestB a)) }
  datatype MutNestB (a : Type) { BBase(), MkB(x: MutNestA a) };
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

  datatype BadA () { MkA(f: BadB -> int) }
  datatype BadB () { BadBBase(), MkB(a: BadA) };
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

  datatype Bad1 () { B1(x: Bad2) }
  datatype Bad2 () { B2(x: Bad1) };
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

  datatype Cycle1 () { C1(x: Cycle2) }
  datatype Cycle2 () { C2(x: Cycle3) }
  datatype Cycle3 () { C3(x: Cycle1) };
#end

/--
info: error: Error: datatype Cycle1 not inhabited
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram threeWayCyclePgm) |>.fst).stripMetaData

---------------------------------------------------------------------
-- Test 15: Mutual Block with Different Type Parameters
---------------------------------------------------------------------

def mutualParamMismatchPgm : Program :=
#strata
program Core;

  datatype A () { ABase(), MkA(b: B int) }
  datatype B (T : Type) { BBase(), MkB(a: A, t: T) };
#end

-- Rejected: `A` declares no type parameters and `B` declares `T`.
/--
info: error: Datatypes in a mutual block must declare the same type parameters, but A declares [] and B declares [T]. If these datatypes are not mutually recursive, declare them in separate blocks.
-/
#guard_msgs in
#eval Core.typeCheck .default (TransM.run Inhabited.default (translateProgram mutualParamMismatchPgm) |>.fst).stripMetaData

/-! ## Duplicate type parameters -/

open Core.TestUtil (translate)

def dupTypeParamsPgm : Program :=
#strata
program Core;

datatype Dup (x : Type, x : Type) { MkDup(f: x) };
#end

/--
info: error: Datatype 'Dup': duplicates found in the type arguments!
Type Arguments: [x, x]
-/
#guard_msgs in
#eval Core.typeCheck .default (translate dupTypeParamsPgm)

/-! ## Type parameter with a reserved prefix -/

def reservedTyParamPgm : Program :=
#strata
program Core;

datatype Res ($__ty0 : Type) { MkRes(f: $__ty0) };
#end

/--
info: error: Datatype 'Res': type parameter '$__ty0' is a reserved name
-/
#guard_msgs in
#eval Core.typeCheck .default (translate reservedTyParamPgm)

/-! ## Reserved substring after the first character -/

-- A reserved prefix is rejected only when it starts the parameter name.
def okTypeParamsPgm : Program :=
#strata
program Core;

datatype Ok (a : Type, b$__ty0 : Type) { MkOk(f: a, g: b$__ty0) };
#end

/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

datatype Ok (a : Type, b$__ty0 : Type) {
  MkOk(f : a, g : b$__ty0)
};
-/
#guard_msgs in
#eval Core.typeCheck .default (translate okTypeParamsPgm)

end Strata.DatatypeTypingTests

/-! ## Datatype blocks built directly as Core declarations -/

namespace Core.MutualDatatypeTypeCheckTests

open Lambda
open Core.TestUtil (aliasEnv programVerdict)

/-- The default context with `Alias` in its declaration-name registry. -/
private def aliasContext : Expression.TyContext :=
  { initTyContext with idents := initTyContext.idents.insert "Alias" () }

/-- A program containing one mutual datatype block. -/
private def dataProgram (block : List (LDatatype Unit)) : Program :=
  { decls := [.type (.data block) .empty] }

/-- A datatype with one constructor and no type parameters. -/
private def baseDatatype : LDatatype Unit :=
  { name := "D", typeArgs := [],
    constrs := [{ name := ⟨"C", ()⟩, args := [], testerName := "D..isC" }],
    constrs_ne := rfl }

/-- A type environment containing the nullary synonym `Alias := int`. -/
private def aliasIntEnv : Expression.TyEnv :=
  aliasEnv [{ name := "Alias", typeArgs := [], type := .int }]

-- A reserved datatype name declared twice gets the duplicate-name error.
private def duplicateReservedDatatype : LDatatype Unit :=
  { baseDatatype with name := "$__rigid_D" }

/--
info: REJECTED: Error in type $__rigid_D: a declaration of this name already exists.
-/
#guard_msgs in
#eval programVerdict (dataProgram [duplicateReservedDatatype, duplicateReservedDatatype])

-- A datatype type parameter may not use the namespace reserved for rigid type constants.
/-- info: REJECTED: Datatype 'D': type parameter '$__rigid_a' is a reserved name -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      typeArgs := ["$__rigid_a"],
      constrs := [{ name := ⟨"C", ()⟩,
                    args := [(⟨"value", ()⟩, .ftvar "$__rigid_a")],
                    testerName := "D..isC" }] }])

-- A constructor may have a reserved name.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      constrs := [{ name := ⟨"$__rigid_C", ()⟩, args := [],
                    testerName := "D..isC" }] }])

-- A tester may have a reserved name.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      constrs := [{ name := ⟨"C", ()⟩, args := [],
                    testerName := "$__rigid_isC" }] }])

-- A constructor argument type naming the unregistered type `$__rigid_a` is rejected.
/-- info: REJECTED: Error in datatype D, constructor C: Undefined type '$__rigid_a' -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      constrs := [{ name := ⟨"C", ()⟩,
                    args := [(⟨"value", ()⟩, .tcons "$__rigid_a" [])],
                    testerName := "D..isC" }] }])

-- Through the entry point, a datatype may have a reserved name.
/--
info: [Strata.Core] Type checking succeeded.

---
info: ok: program Core;

datatype $__rigid_a {
  C()
};
-/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default
  (dataProgram [{ baseDatatype with name := "$__rigid_a" }]))

-- Through the entry point, a constructor argument type naming the unregistered type
-- `$__rigid_a` is rejected.
/-- info: error: Error in datatype D, constructor C: Undefined type '$__rigid_a' -/
#guard_msgs (whitespace := lax) in
#eval Std.format (Core.typeCheck .default
  (dataProgram
    [{ baseDatatype with
        constrs := [{ name := ⟨"C", ()⟩,
                      args := [(⟨"value", ()⟩, .tcons "$__rigid_a" [])],
                      testerName := "D..isC" }] }]))

-- A datatype name cannot also denote a type synonym, even in a caller-supplied environment.
/-- info: REJECTED: Error in type Alias: a declaration of this name already exists. -/
#guard_msgs in
#eval programVerdict (dataProgram [{ baseDatatype with name := "Alias" }]) aliasContext aliasIntEnv

-- An ambient alias missing from the name registry is accepted: the checker does not validate
-- the ambient aliases.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram [{ baseDatatype with name := "Alias" }]) initTyContext aliasIntEnv

-- A legal generic datatype is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      typeArgs := ["a"],
      constrs := [{ name := ⟨"C", ()⟩,
                    args := [(⟨"value", ()⟩, .ftvar "a")],
                    testerName := "D..isC" }] }])

-- A constructor argument type may be an alias.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ baseDatatype with
      constrs := [{ name := ⟨"C", ()⟩,
                    args := [(⟨"value", ()⟩, .tcons "Alias" [])],
                    testerName := "D..isC" }] }]) aliasContext aliasIntEnv

-- An inhabited recursive datatype is accepted.
/-- info: ACCEPTED -/
#guard_msgs in
#eval programVerdict (dataProgram
  [{ name := "Natish", typeArgs := [],
     constrs := [
       { name := ⟨"Zero", ()⟩, args := [], testerName := "Natish..isZero" },
       { name := ⟨"Next", ()⟩,
         args := [(⟨"pred", ()⟩, .tcons "Natish" [])],
         testerName := "Natish..isNext" }],
     constrs_ne := rfl }])

end Core.MutualDatatypeTypeCheckTests

end
