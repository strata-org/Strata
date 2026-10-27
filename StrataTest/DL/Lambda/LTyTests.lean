/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Lambda.LTyWFCheckSound

/-! ## Tests for LTy -/

meta section
namespace Lambda

open Std (format)
open LTy.Syntax

/--
info: [Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"],
 Lambda.LMonoTy.tcons "bool" [],
 Lambda.LMonoTy.tcons "foo" [Lambda.LMonoTy.ftvar "_dummy0"],
 Lambda.LMonoTy.tcons "a" [Lambda.LMonoTy.ftvar "_dummy0", Lambda.LMonoTy.ftvar "_dummy1"]]
-/
#guard_msgs in
#eval LMonoTy.getTyConstructors
        ((.tcons "arrow" [.tcons "bool" [], .tcons "foo" [.tcons "a" [.ftvar "b", .tcons "bool" []]]]))

/-- info: 3 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → (int → int))]
/-- info: 2 -/
#guard_msgs in
#eval LTy.inputArity t[int → (int → int)]
/-- info: 1 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. (%a → int) → int]
/-- info: 0 -/
#guard_msgs in
#eval LTy.inputArity t[∀a. pair %a bool]

/-- info: [int, int, int] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (int → (int → int))]
/-- info: [int, bool] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → int)]
/-- info: [int, bool, bit] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[int → (bool → (bit → nat))]
/-- info: [(arrow int int)] -/
#guard_msgs in
#eval format $ LMonoTy.inputTypes mty[(int → int) → nat]
/-- info: [] -/
#guard_msgs in
#eval LMonoTy.inputTypes mty[pair int bool]

private abbrev TypeJudgmentParams : LExprParams := ⟨Unit, Unit⟩

private def resolvedTypeContext : LContext TypeJudgmentParams := LContext.default

/-- The resolved judgment accepts a free variable the policy admits. -/
example : ResolvedTyWF resolvedTypeContext (fun v => v == "a") mty[%a] :=
  .ftvar (by decide)

/-- The resolved judgment rejects a free variable the policy excludes. -/
example : ¬ ResolvedTyWF resolvedTypeContext (fun v => v == "a") mty[%b] := by
  intro h
  cases h with
  | ftvar hadmissible => simp at hadmissible

/-- A type accepted by the resolved judgment uses only registered type constructors. -/
example (h : ResolvedTyWF resolvedTypeContext policy ty) :
    ty.knownInstance resolvedTypeContext.knownTypes = true :=
  h.knownInstance

/-- Resolved well-formedness entails constructor-arity well-kindedness. -/
example (h : ResolvedTyWF resolvedTypeContext policy ty) :
    resolvedTypeContext.WellKindedTy ty :=
  h.wellKinded

end Lambda
end

/-! ## Syntax Tests for LTy -/

namespace LTy.SyntaxTests

open Lambda
open LTy.Syntax

/-- info: LMonoTy.tcons "list" [LMonoTy.tcons "int" []] : LMonoTy -/
#guard_msgs in
#check mty[list int]

/-- info: LMonoTy.tcons "pair" [LMonoTy.tcons "int" [], LMonoTy.tcons "bool" []] : LMonoTy -/
#guard_msgs in
#check mty[pair int bool]

/--
info: LMonoTy.tcons "arrow"
  [LMonoTy.tcons "Map" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"],
    LMonoTy.tcons "arrow" [LMonoTy.ftvar "k", LMonoTy.ftvar "v"]] : LMonoTy
-/
#guard_msgs in
#check mty[(Map %k %v) → %k → %v]

/--
info: LMonoTy.tcons "arrow"
  [LMonoTy.ftvar "a",
    LMonoTy.tcons "arrow" [LMonoTy.ftvar "b", LMonoTy.tcons "arrow" [LMonoTy.ftvar "c", LMonoTy.ftvar "d"]]] : LMonoTy
-/
#guard_msgs in
#check mty[%a → %b → %c → %d]

/-- info: LTy.forAll ["α"] (LMonoTy.tcons "myType" [LMonoTy.ftvar "α"]) : LTy -/
#guard_msgs in
#check t[∀α. myType %α]

/--
info: LTy.forAll ["α"]
  (LMonoTy.tcons "arrow" [LMonoTy.ftvar "α", LMonoTy.tcons "arrow" [LMonoTy.ftvar "α", LMonoTy.tcons "int" []]]) : LTy
-/
#guard_msgs in
#check t[∀α. %α → %α → int]

end LTy.SyntaxTests
