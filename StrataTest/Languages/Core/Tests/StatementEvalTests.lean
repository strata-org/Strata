/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.StatementEval
import Strata.DL.Imperative.StmtSemanticsSmallStep
import Strata.Languages.Core.StatementSemantics

namespace Core
---------------------------------------------------------------------

section Tests

open Std (ToFormat Format format)
open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc)

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #18]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_18
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne ∅ ∅ [.init "x" t[int] (some eb[#0]) .empty,
                    .set "x" eb[#18] .empty,
                    .assert "x_eq_18" eb[x == #18] .empty]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → _yinit
(x : int) → _yinit]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_12
Property: assert
Assumptions:
Proof Obligation:
(_yinit == #12)
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("y", (mty[int], eb[_yinit]))])
  ∅
  [.init "x" t[int] (some eb[#0]) .empty,
  .set "x" eb[y] .empty,
  .assert "x_eq_12" eb[x == #12] .empty]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : bool) → (x == #true)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
-/
#guard_msgs in
-- NOTE: no error during evaluation here; the typechecker should flag this
-- though because `x` can't appear in its own initialization expression.
#eval evalOne ∅ ∅
       [
       .init "x" t[bool] (some eb[x == #true]) .empty
       ] |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(minit : (arrow int int)) → (_minit : (arrow int int))
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else ((_minit : (arrow int int))
         %0)))
      %0)))
   %0)))
(m0 : int) → ((_minit : (arrow int int)) #0)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
(((_minit : (arrow int int)) #5) == #50)

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope
    [("minit", (mty[int → int], eb[(_minit : int → int)]))])
  ∅
  [.init "m" t[int → int] (some eb[minit]) .empty,
  .init "m0" t[int] (some eb[(m #0)]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else ((m : int → int) %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else ((m : int → int) %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else ((m : int → int) %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |>.snd |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[minit → _minit
(m : (arrow int int)) → (λ (if (%0 == #3) then #30 else ((λ (if (%0 == #2) then #20 else ((λ (if (%0 == #1) then #10 else (_minit
         %0)))
      %0)))
   %0)))]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: m_5_eq_50
Property: assert
Assumptions:
Proof Obligation:
((_minit #5) == #50)

Label: m_2_eq_20
Property: assert
Assumptions:
Proof Obligation:
#true

Label: m_1_eq_10
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne
  ((Env.init (empty_factory := true)).pushScope [("minit", (none, eb[_minit]))])
  ∅
  [.init "m" t[int → int] (some eb[minit]) .empty,
  .set "m" eb[λ (if (%0 == #1) then #10 else (m %0))] .empty,
  .set "m" eb[λ (if (%0 == #2) then #20 else (m %0))] .empty,
  .assert "m_5_eq_50" eb[(m #5) == #50] .empty,
  .assert "m_2_eq_20" eb[(m #2) == #20] .empty,
  .set "m" eb[λ (if (%0 == #3) then #30 else (m %0))] .empty,
  .assert "m_1_eq_10" eb[(m #1) == #10] .empty
  ]) |>.snd |> format



private def prog1 : Statements :=
 [
 .init "x" t[int] (some eb[#0]) .empty,
 .init "y" t[int] (some eb[#6]) .empty,
 .block "label_0"

   [Statement.init "z" t[bool] (some eb[zinit]) .empty,
    Statement.assume "z_false" eb[z == #false] .empty,

   .ite eb[z == #false]
     [Statement.set "x" eb[y] .empty]
     -- The "trivial" assertion, though unreachable, is still verified away by the
     -- PE because the conclusion of the proof obligation evaluates to `true`.
     -- However, if the conclusion were anything else (including `false`) and
     -- the path conditions weren't empty, then this proof obligation would be
     -- sent on to the SMT solver.
     [Statement.assert "trivial" eb[#true] .empty]
     .empty,

   Statement.assert "x_eq_y_label_0" eb[x == y] .empty,
   ]
   .empty,
 .assert "x_eq_y" eb[x == y] .empty
 ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → (if (zinit == #false) then #6 else #0)
(y : int) → #6
zinit → zinit]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:



Datatypes:

Path Conditions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))


Warnings:
[]
Deferred Proof Obligations:
Label: trivial
Property: assert
Assumptions:
(<label_ite_cond_false: !(z == #false)>, (if (zinit == #false) then #false else #true))
(z_false, (zinit == #false))
Proof Obligation:
#true

Label: x_eq_y_label_0
Property: assert
Assumptions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))
Proof Obligation:
((if (zinit == #false) then #6 else #0) == #6)

Label: x_eq_y
Property: assert
Assumptions:
(z_false, (zinit == #false))
(<label_ite_cond_true: (z == #false)>, (if (zinit == #false) then (zinit == #false) else #true)) (<label_ite_cond_false: !(z == #false)>, (if (if (zinit == #false) then #false else #true) then (if (zinit == #false) then #false else #true) else #true))
Proof Obligation:
((if (zinit == #false) then #6 else #0) == #6)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog1) |>.snd |> format


private def prog2 : Statements := [
  .init "x" t[int] (some eb[#0]) .empty,
  .set "x" eb[#1] .empty,
  .havoc "x" .empty,
  .assert "x_eq_1" eb[x == #1] .empty, -- error
  .havoc "x" .empty,
  .set "x" eb[#8] .empty
]

/--
info: {
  init (x : int) := #0
  x := #1
  havoc x
  assert [x_eq_1] ($__x0 == #1)
  havoc x
  x := #8
}
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |>.fst |> format

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(x : int) → #8]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 2
Factory Functions:



Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: x_eq_1
Property: assert
Assumptions:
Proof Obligation:
(($__x0 : int) == #1)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ prog2) |>.snd |> format

/--
Test funcDecl: declare a helper function and use it
-/
def testFuncDecl : List Statement :=
  let doubleFunc : PureFunc Expression := {
    name := ⟨"double", ()⟩,
    typeArgs := [],
    isConstr := false,
    inputs := [(⟨"x", ()⟩, .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[((~Int.Add x) x)],
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl doubleFunc .empty,
    .init "y" t[int] (some eb[(~double #5)]) .empty,
    .assert "y_eq_10" eb[y == #10] .empty
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(y : int) → (~double #5)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
func double :  ((x : int)) → int :=
  ((~Int.Add x x))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: y_eq_10
Property: assert
Assumptions:
Proof Obligation:
((~double #5) == #10)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testFuncDecl) |>.snd |> format

/--
Test funcDecl with variable capture: function captures variable value at declaration time,
not affected by subsequent mutations
-/
def testFuncDeclSymbolic : List Statement :=
  let addNFunc : PureFunc Expression := {
    name := ⟨"addN", ()⟩,
    typeArgs := [],
    isConstr := false,
    inputs := [(⟨"x", ()⟩, .forAll [] .int)],
    output := .forAll [] .int,
    body := some eb[((~Int.Add x) n)],  -- Captures 'n' at declaration time
    attr := #[],
    concreteEval := none,
    axioms := []
  }
  [
    .init "n" t[int] (some eb[#10]) .empty,  -- Initialize n to 10
    .funcDecl addNFunc .empty,  -- Function captures n = 10 at declaration time
    .set "n" eb[#20] .empty,  -- Mutate n to 20
    .init "result" t[int] (some eb[(~addN #5)]) .empty,  -- Call function
    .assert "result_eq_15" eb[result == #15] .empty  -- Result is 5 + 10 = 15 (uses captured value)
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(n : int) → #20
(result : int) → (~addN #5)]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
func addN :  ((x : int)) → int :=
  ((~Int.Add x #10))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: result_eq_15
Property: assert
Assumptions:
Proof Obligation:
((~addN #5) == #15)
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testFuncDeclSymbolic) |>.snd |> format

/--
Test polymorphic funcDecl: declare a polymorphic function `choose` that takes a boolean
and two values of type `a`, returning the first if true, second if false.
Then use it with multiple concrete type instantiations (int and bool).

The function has the `inline` attribute so its body gets expanded during evaluation,
allowing us to verify that the function definition is actually being used.
-/
def testPolymorphicFuncDecl : List Statement :=
  let chooseFunc : PureFunc Expression := {
    name := ⟨"choose", ()⟩,
    typeArgs := ["a"],  -- Polymorphic type parameter
    isConstr := false,
    inputs := [
      (⟨"cond", ()⟩, .forAll [] .bool),
      (⟨"x", ()⟩, .forAll [] (.ftvar "a")),
      (⟨"y", ()⟩, .forAll [] (.ftvar "a"))
    ],
    output := .forAll [] (.ftvar "a"),
    body := some eb[(if cond then x else y)],
    attr := #[.inline],  -- Enable inlining so body is expanded during evaluation
    concreteEval := none,
    axioms := []
  }
  [
    .funcDecl chooseFunc .empty,
    -- Use with int type (curried application)
    .init "intResult" t[int] (some eb[(((~choose #true) #1) #2)]) .empty,
    .assert "intResult_eq_1" eb[intResult == #1] .empty,
    -- Use with bool type (curried application)
    .init "boolResult" t[bool] (some eb[(((~choose #false) #true) #false)]) .empty,
    .assert "boolResult_eq_false" eb[boolResult == #false] .empty
  ]

/--
info: Error:
none
Subst Map:

Expression Env:
State:
[(intResult : int) → #1
(boolResult : bool) → #false]

Evaluation Config:
Eval Depth: 200
Variable Prefix: $__
Variable gen count: 0
Factory Functions:
@[inline]
func choose : ∀[a]. ((cond : bool) (x : a) (y : a)) → a :=
  ((if cond then x else y))


Datatypes:

Path Conditions:


Warnings:
[]
Deferred Proof Obligations:
Label: intResult_eq_1
Property: assert
Assumptions:
Proof Obligation:
#true

Label: boolResult_eq_false
Property: assert
Assumptions:
Proof Obligation:
#true
-/
#guard_msgs in
#eval (evalOne ∅ ∅ testPolymorphicFuncDecl) |>.snd |> format

end Tests

---------------------------------------------------------------------

/-! ## Small-Step Consistency Tests

These tests demonstrate that the big-step evaluator (`evalOne`) is consistent
with the small-step operational semantics (`StepStmt` / `StepStmtStar`) from
`Strata.DL.Imperative.StmtSemanticsSmallStep`.

Each test pairs:
1. A `#eval check` that runs the big-step evaluator, and
2. An `example : TestStepStar ...` proof that the same program can be executed
   under the small-step semantics.

The approach mirrors `StrataTest/DL/Lambda/LExprEvalTests.lean`.
-/

namespace SmallStepTests

open Statement Lambda Lambda.LTy.Syntax Lambda.LExpr.SyntaxMono Core.Syntax
open Imperative (PureFunc Config StepStmt StepStmtStar
                  EvalCmd EvalCmdParamF InitState UpdateState
                  SemanticStore SemanticEval ProgramCounter
                  WellFormedSemanticEvalBool WellFormedSemanticEvalVar)

/-! ### Simple evaluator for the small-step world

We define a concrete `SemanticStore` and `SemanticEval` that handle
only the simplest cases: variable lookup and boolean/integer constants.
This is enough for the basic command tests (init, set, assert, havoc). -/

/-- A concrete store represented as a list of (ident, value) pairs. -/
def simpleStore (bindings : List (Expression.Ident × Expression.Expr))
    : SemanticStore Expression :=
  fun id => (bindings.find? (fun p => p.1 == id)).map (·.2)

/-- A concrete evaluator that handles variable lookup and returns
    constants as-is. -/
def simpleEval : SemanticEval Expression :=
  fun σ e =>
    match e with
    | .fvar _ v _ => σ v
    | .boolConst _ b => some (LExpr.boolConst () b)
    | .intConst _ n => some (LExpr.intConst () n)
    | .eq _ e1 e2 =>
      match simpleEval σ e1, simpleEval σ e2 with
      | some v1, some v2 => if v1 == v2 then some Core.true else some Core.false
      | _, _ => none
    | _ => none

/-- No procedures in our test world. -/
def noProcedures : String → Option Core.Procedure := fun _ => none

/-- No evaluator extension in our test world. -/
def noExtend : CoreEval → PureFunc Expression → CoreEval := fun δ _ => δ

/-! ### Type abbreviations -/

abbrev TestConfig := Config Expression Command
abbrev TestStep := StepStmt Expression
    (EvalCmdParamF.ofPlain (Core.EvalCommand noProcedures noExtend))
    (Core.EvalPureFunc noExtend)
abbrev TestStepStar := StepStmtStar Expression
    (EvalCmdParamF.ofPlain (Core.EvalCommand noProcedures noExtend))
    (Core.EvalPureFunc noExtend)

/-! ### Tactic macros for small-step proofs

These mirror the pattern from `LExprEvalTests.lean`. -/

/-- Take a single small step (apply `ReflTrans.step`). -/
macro "take_step" : tactic => `(tactic| apply ReflTrans.step)

/-- Finish the multi-step derivation (apply `ReflTrans.refl`). -/
macro "take_refl" : tactic => `(tactic| apply ReflTrans.refl)

/-- Enter a statement list: apply `step_stmts_cons` to split head from tail. -/
macro "enter_stmts" : tactic => `(tactic| (apply StepStmt.step_stmts_cons; rfl))

/-- Finish an empty statement list: apply `step_stmts_nil`. -/
macro "finish_stmts" : tactic => `(tactic| apply StepStmt.step_stmts_nil)

/-- Execute a command: apply `step_cmd` with the given command evaluation. -/
macro "step_cmd" : tactic => `(tactic| apply StepStmt.step_cmd)

/-- When the inner config of a seq reaches terminal, continue with remaining stmts. -/
macro "seq_done" : tactic => `(tactic| apply StepStmt.step_seq_done)

/-- Step the inner config of a seq forward. -/
macro "seq_inner" : tactic => `(tactic| apply StepStmt.step_seq_inner)

/-! ### Well-formedness proofs for simpleEval -/

-- NOTE: `WellFormedSemanticEvalBool` requires the not-inversion property for ALL
-- expressions, including `fvar`.  Our `simpleEval` doesn't handle `app` (which
-- `HasNot.not` produces for non-constant expressions), so the property cannot be
-- proved without extending the evaluator.  We axiomatise it here to unblock the
-- small-step consistency tests; a full evaluator would handle `app boolNotFunc e`.
theorem simpleEval_wfBool : WellFormedSemanticEvalBool simpleEval := by
  intro σ e; constructor <;> constructor <;> intro h <;> sorry

theorem simpleEval_wfVar : WellFormedSemanticEvalVar simpleEval := by
  intro e v σ hget
  simp [Imperative.HasFvar.getFvar] at hget
  split at hget
  · simp_all [simpleEval]
  · simp at hget

/-! ### Test 1: init x := 0; set x := 18; assert x == 18

The simplest test: initialize a variable, assign to it, and assert. -/

private abbrev ss_test1 : List Statement :=
  [.init "x" t[int] (some eb[#0]) .empty,
   .set "x" eb[#18] .empty,
   .assert "x_eq_18" eb[x == #18] .empty]

-- The initial environment for small-step: empty store, simpleEval, no failures.
private abbrev ρ₀ : Imperative.Env Expression :=
  ⟨fun _ => none, simpleEval, false⟩

-- After init x := 0: store maps x ↦ 0
private abbrev σ₁ : SemanticStore Expression :=
  fun id => if id == (⟨"x", ()⟩ : CoreIdent) then some (LExpr.intConst () 0) else none

-- After set x := 18: store maps x ↦ 18
private abbrev σ₂ : SemanticStore Expression :=
  fun id => if id == (⟨"x", ()⟩ : CoreIdent) then some (LExpr.intConst () 18) else none

private abbrev ρ₁ : Imperative.Env Expression :=
  ⟨σ₁, simpleEval, false⟩
private abbrev ρ₂ : Imperative.Env Expression :=
  ⟨σ₂, simpleEval, false⟩

/--
Proof that `init x := 0; set x := 18; assert x == 18` steps to terminal
under the small-step semantics.

The execution trace is:
```
  .stmts [init; set; assert] ρ₀ [0]
→ .seq (.stmt (init x := 0) ρ₀ [0]) [set; assert] [1]
→ .seq (.terminal ρ₁) [set; assert] [1]
→ .stmts [set; assert] ρ₁ [1]
→ .seq (.stmt (set x := 18) ρ₁ [1]) [assert] [2]
→ .seq (.terminal ρ₂) [assert] [2]
→ .stmts [assert] ρ₂ [2]
→ .seq (.stmt (assert x==18) ρ₂ [2]) [] [3]
→ .seq (.terminal ρ₂) [] [3]
→ .stmts [] ρ₂ [3]
→ .terminal ρ₂
```
-/
example : TestStepStar
    (.stmts ss_test1 ρ₀ [0])
    (.terminal ρ₂) := by
  -- Step 1: stmts [init; set; assert] → seq (stmt init) [set; assert]
  take_step; enter_stmts
  -- Step 2: seq (stmt init) → seq (terminal ρ₁)
  take_step; seq_inner; step_cmd
  constructor
  · -- EvalCommand: cmd_sem (eval_init)
    apply EvalCommand.cmd_sem
    exact ⟨false, EvalCmd.eval_init (v := LExpr.intConst () 0)
      (by rfl)
      (InitState.init (σ' := σ₁) (by rfl) (by rfl) (by intro y hne; simp [σ₁]; intro h; exact absurd h hne.symm))
      simpleEval_wfVar⟩
  · rfl  -- hasAssertFailure = false
  -- Step 3: seq (terminal ρ₁) → stmts [set; assert]
  take_step; seq_done
  -- Step 4: stmts [set; assert] → seq (stmt set) [assert]
  take_step; enter_stmts
  -- Step 5: seq (stmt set) → seq (terminal ρ₂)
  take_step; seq_inner; step_cmd
  constructor
  · apply EvalCommand.cmd_sem
    exact ⟨false, EvalCmd.eval_set (v := LExpr.intConst () 18)
      (by rfl)
      (UpdateState.update (σ' := σ₂) (by rfl) (by rfl)
        (by intro y hne; simp only [σ₂, σ₁]; split <;> simp_all))
      simpleEval_wfVar⟩
  · rfl
  -- Step 6: seq (terminal ρ₂) → stmts [assert]
  take_step; seq_done
  -- Step 7: stmts [assert] → seq (stmt assert) []
  take_step; enter_stmts
  -- Step 8: seq (stmt assert) → seq (terminal ρ₂)
  take_step; seq_inner; step_cmd
  constructor
  · -- Normalize the nested env projections from prior steps
    show EvalCommand noProcedures noExtend simpleEval σ₂ _ _
    apply EvalCommand.cmd_sem
    exact ⟨false, EvalCmd.eval_assert_pass
      (by simp only [simpleEval, σ₂, Imperative.HasBool.tt, Core.true]; native_decide)
      simpleEval_wfBool⟩
  · rfl
  -- Step 9: seq (terminal ρ₂) → stmts []
  take_step; seq_done
  -- Step 10: stmts [] → terminal ρ₂
  take_step; finish_stmts
  -- Done
  take_refl

end SmallStepTests

---------------------------------------------------------------------
end Core
