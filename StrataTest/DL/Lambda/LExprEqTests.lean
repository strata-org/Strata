/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprEval
import Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.Lambda

/-!
## Tests for `eql`

Tests that equality comparison correctly:
- Proves inequality of lambdas with different bodies
- Returns `none` for lambdas with syntactically different but potentially equal bodies
- Proves equality and inequality of datatype constructor applications
-/

namespace Lambda
open LTy.Syntax LExpr.SyntaxMono

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TP.Identifier where
  coe s := Identifier.mk s ()

private def emptyFactory : @Factory TP := #[]

private abbrev eqMM (F : @Factory TP) (e1 e2 : LExpr TP.mono) : Option Bool :=
  LExpr.eql F e1 e2

/-! ### Lambda equality tests -/

-- Different constant bodies → provably not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ #1] esM[λ #2]

-- Same body → provably equal
/-- info: some true -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ %0] esM[λ %0]

-- Different types → provably not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory
  (LExpr.abs () "" (some LMonoTy.int) (LExpr.bvar () 0))
  (LExpr.abs () "" (some LMonoTy.bool) (LExpr.bvar () 0))

-- Syntactically different but semantically equal (identity vs if true then x else x)
-- Should return none (inconclusive), NOT some false
/-- info: none -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ %0] esM[λ (if #true then %0 else %0)]

-- Open lambdas (containing free variables) → inconclusive
/-- info: none -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ (x : int)] esM[λ (y : int)]

-- Closed lambdas that are not equal but eqModuloMeta can't prove it → inconclusive
/-- info: none -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ (if (%0 == #1) then #1 else #0)] esM[λ %0]

/-! ### Constant equality tests -/

-- Same constants → equal
/-- info: some true -/
#guard_msgs in
#eval eqMM emptyFactory esM[#42] esM[#42]

-- Different constants → not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory esM[#1] esM[#2]

-- Bool constants
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory esM[#true] esM[#false]

-- Constant vs lambda → not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory esM[#1] esM[λ %0]

-- Lambda vs constant → not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM emptyFactory esM[λ %0] esM[#1]

/-! ### Real constant equality tests -/

-- Different real constants are incomparable (eql cannot decide inequality)
/-- info: none -/
#guard_msgs in
#eval eqMM emptyFactory (LExpr.realConst () 1) (LExpr.realConst () 2)

/-! ### Datatype constructor equality tests -/

private def intListTy : LDatatype Unit :=
  { name := "IntList", typeArgs := [],
    constrs := [
      { name := "Nil", args := [], testerName := "isNil" },
      { name := "Cons",
        args := [("hd", .int), ("tl", .tcons "IntList" [])],
        testerName := "isCons" }
    ], constrs_ne := rfl }

private def tripleTy : LDatatype Unit :=
  { name := "Triple", typeArgs := [],
    constrs := [
      { name := "MkTriple",
        args := [("fst", .int), ("snd", .int), ("thd", .int)],
        testerName := "isTriple" }
    ], constrs_ne := rfl }

private def tf : @TypeFactory Unit := #[[intListTy], [tripleTy]]

private def constrFactory : @Factory TP :=
  let C := LContext.default.addFactoryFunctions (@IntBoolFactory TP _ _)
  match C.addTypeFactory tf with
  | .error _ => panic "failed to add type factory"
  | .ok C => C.functions

-- Nil == Nil → equal
/-- info: some true -/
#guard_msgs in
#eval eqMM constrFactory esM[(~Nil)] esM[(~Nil)]

-- Nil vs Cons → not equal (different constructors)
/-- info: some false -/
#guard_msgs in
#eval eqMM constrFactory esM[(~Nil)] esM[((~Cons #1) (~Nil))]

-- Cons with same args → equal
/-- info: some true -/
#guard_msgs in
#eval eqMM constrFactory esM[((~Cons #1) (~Nil))] esM[((~Cons #1) (~Nil))]

-- Cons with different head → not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM constrFactory esM[((~Cons #1) (~Nil))] esM[((~Cons #2) (~Nil))]

-- Cons with different tail → not equal
/-- info: some false -/
#guard_msgs in
#eval eqMM constrFactory
  esM[((~Cons #1) (~Nil))]
  esM[((~Cons #1) ((~Cons #2) (~Nil)))]

-- Nested equal constructors
/-- info: some true -/
#guard_msgs in
#eval eqMM constrFactory
  esM[((~Cons #1) ((~Cons #2) (~Nil)))]
  esM[((~Cons #1) ((~Cons #2) (~Nil)))]

-- Cons with symbolic arg → inconclusive
/-- info: none -/
#guard_msgs in
#eval eqMM constrFactory esM[((~Cons x) (~Nil))] esM[((~Cons y) (~Nil))]

-- One arg equal, one not equal, one inconclusive → false (false dominates)
/-- info: some false -/
#guard_msgs in
#eval eqMM constrFactory
  esM[(((~MkTriple #1) #2) x)]
  esM[(((~MkTriple #1) #3) y)]

end Lambda
