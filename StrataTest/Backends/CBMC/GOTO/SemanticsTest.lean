/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Semantics

/-!
# Tests for GOTO Semantics

Basic sanity checks that the semantics rules can be instantiated and
that the simple properties hold.
-/

open CProverGOTO CProverGOTO.Semantics

/-! ## Test helpers -/

/-- A trivial expression evaluator that handles constants and symbols. -/
def testEval : ExprEval
  | σ, e => match e.id with
    | .nullary (.constant "true") => some (.vBool true)
    | .nullary (.constant "false") => some (.vBool false)
    | .nullary (.constant v) => v.toInt?.map .vInt
    | .nullary (.symbol name) => σ name
    | _ => none

/-- A no-call relation (no function calls succeed). -/
def noCall : CallResultRel := fun _ _ _ _ _ _ => False

/-! ## Simple program: SKIP; END_FUNCTION -/

def skipProg : Program :=
  { name := "test"
    instructions := #[
      { type := .SKIP, locationNum := 0 },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example : ExecProg noCall testEval (fun _ => none) skipProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.skip rfl
  · exact ExecProg.end_function rfl

/-! ## ASSERT pass -/

def assertPassProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSERT, locationNum := 0,
        guard := Expr.constant "true" .Boolean },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example : ExecProg noCall testEval (fun _ => none) assertPassProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.assert_pass rfl rfl
  · exact ExecProg.end_function rfl

/-! ## ASSERT fail still advances -/

def assertFailProg : Program :=
  { name := "test"
    instructions := #[
      { type := .ASSERT, locationNum := 0,
        guard := Expr.constant "false" .Boolean,
        sourceLoc := { SourceLocation.nil with comment := "test assertion" } },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

-- Assertion failure still allows execution to continue
example : ExecProg noCall testEval (fun _ => none) assertFailProg 0
    Store.empty Store.empty none := by
  apply ExecProg.step (pc' := 1)
  · exact StepInstr.assert_fail rfl rfl
  · exact ExecProg.end_function rfl

-- But the program is NOT safe
example : ¬ ProgramSafe noCall testEval (fun _ => none) assertFailProg Store.empty := by
  intro hsafe
  apply hsafe 0 Store.empty
  · exact Reachable.refl
  · exact ⟨rfl, rfl⟩

/-! ## Reachability transitivity -/

example {cr : CallResultRel} {eval : ExprEval} {fenv : FuncEnv}
    {prog : Program} {σ : Store} :
    Reachable cr eval fenv prog 0 σ 0 σ := Reachable.refl
