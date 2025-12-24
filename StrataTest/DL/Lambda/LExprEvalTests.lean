/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Semantics
import Strata.DL.Lambda.LExprEval

---------------------------------------------------------------------

namespace Lambda
open Std (ToFormat Format format)

namespace LExpr
---------------------------------------------------------------------

section EvalTest

open LTy.Syntax LExpr.SyntaxMono
open Std (ToFormat Format format)

/-
Each test is a pair of
1. Lambda.LExpr.eval invocation, and
2. Its equivalent Lambda.LExpr.Step version.
-/

-- A helper tactic for proving 'isCanonicalValue e = b'.
macro "discharge_isCanonicalValue": tactic => `(tactic|
    conv =>
      lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
  )
-- Take a small step.
macro "take_step": tactic => `(tactic |
    (conv => lhs; reduce) <;> apply ReflTrans.step
  )
-- Finish taking small steps!
macro "take_refl": tactic => `(tactic |
    (conv => lhs; reduce) <;> apply ReflTrans.refl
  )
-- Do beta reduction.
macro "reduce_beta": tactic => `(tactic |
    apply Step.beta <;> discharge_isCanonicalValue
  )
-- A helper tactic to exhibit an instance of Metadata (which is Unit)
macro "inhabited_metadata": tactic => `(tactic |
    solve | (simp; apply ())
  )

private abbrev TestParams : LExprParams := ⟨Unit, Unit⟩

private instance : Coe String TestParams.Identifier where
  coe s := Identifier.mk s ()


/- Test cases -/

structure TestCase where
  -- Input state
  σ: LState TestParams
  -- Input expression
  e: LExpr (TestParams.mono)
  -- Reduced output
  e_out: LExpr (TestParams.mono)

def check (t:TestCase) (n:=100) := (Lambda.LExpr.eval n t.σ t.e) == t.e_out

/-- The two kinds of propositions we would like to test! -/
abbrev steps_well (t:TestCase):Prop :=
  Lambda.StepStar (Tbase:=TestParams)
    t.σ.config.factory (Scopes.toEnv t.σ.state) t.e t.e_out

abbrev stuck (t:TestCase):Prop :=
  ∀ eres, ¬ Lambda.Step (Tbase:=TestParams)
    t.σ.config.factory (Scopes.toEnv t.σ.state) t.e eres


-------------------------------- Tests ------------------------------

def test1 := TestCase.mk
  ({Lambda.LState.init with state := [[("m", (mty[int → int], esM[_minit]))]] })
  (esM[λ (if (%0 == #1) then #10 else (m %0))])
  (esM[λ (if (%0 == #1) then #10 else (_minit %0))])

/-- info: true -/
#guard_msgs in
#eval (check test1)

-- Small step stucks because abstraction is a value.
example: stuck test1 := by
  intros e H
  contradiction


def test2 := TestCase.mk
  { LState.init with state := [[("x", (mty[int], esM[#32]))]] }
  esM[((λ (if (%0 == #23) then #17 else #42)) (x : int))]
  esM[#42]

/-- info: true -/
#guard_msgs in
#eval (check test2)

example: steps_well test2 := by
  unfold steps_well Scopes.toEnv test2
  take_step; apply Step.reduce_2 <;> try inhabited_metadata
  · discharge_isCanonicalValue
  · repeat constructor
  take_step; reduce_beta
  take_step; constructor <;> try inhabited_metadata
  · apply Step.eq_reduce <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; apply Step.ite_reduce_else
  apply ReflTrans.refl


def test3 := TestCase.mk
  ∅
  esM[(f #true)]
  esM[(f #true)]

/-- info: true -/
#guard_msgs in
#eval check test3

example: stuck test3 := by
  intros e H
  contradiction


def test4 := TestCase.mk
  { LState.init with state :=
      [[("m", (none, esM[(λ (minit %0))]))], -- most recent scope
      [("m", (none, (.intConst () 12)))]] }
  esM[((λ (if (%0 == #23) then #17 else (m %0)) #24))]
  esM[(minit #24)]

/-- info: true -/
#guard_msgs in
#eval check test4

example: steps_well test4 := by
  unfold steps_well Scopes.toEnv test4
  take_step; reduce_beta
  take_step; apply Step.ite_reduce_cond <;> try inhabited_metadata
  · apply Step.eq_reduce <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; apply Step.ite_reduce_else
  take_step; apply Step.reduce_1; inhabited_metadata; apply Step.expand_fvar; rfl
  take_step; reduce_beta
  take_refl


def test5 := TestCase.mk
  { LState.init with state := [[("m", (none, esM[minit]))]] }
  esM[((λ (if (%0 == #23) then #17 else (m %0))) #24)]
  esM[(minit #24)]

/-- info: true -/
#guard_msgs in
#eval check test5

example: steps_well test5 := by
  unfold steps_well Scopes.toEnv test5
  take_step; reduce_beta
  take_step; apply Step.ite_reduce_cond; inhabited_metadata
  · apply Step.eq_reduce <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; apply Step.ite_reduce_else
  take_step; apply Step.reduce_1; inhabited_metadata; apply Step.expand_fvar; rfl
  take_refl


def test6 := TestCase.mk
  ∅
  esM[if #true then x else y]
  esM[x]

/-- info: true -/
#guard_msgs in
#eval check test6

example: steps_well test6 := by
  unfold steps_well Scopes.toEnv test6
  take_step
  · constructor
  take_refl


-- Ill-formed `abs` is returned as-is in this Curry style...
def test7 := TestCase.mk
  ∅
  esM[(λ %1)]
  esM[(λ %1)]

/-- info: true -/
#guard_msgs in
#eval check test7

example: stuck test7 := by
  intros e H
  contradiction


/- Tests for evaluation of BuiltInFunctions. -/

open LTy.Syntax

private def testBuiltIn : @Factory TestParams :=
  #[{ name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval := some (fun e args => match args with
                        | [e1, e2] =>
                          let e1i := LExpr.denoteInt e1
                          let e2i := LExpr.denoteInt e2
                          match e1i, e2i with
                          | some x, some y => .some (.intConst e1.metadata (x + y))
                          | _, _ => .none
                        | _ => .none) },
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval :=  some (fun e args => match args with
                          | [e1, e2] =>
                            let e1i := LExpr.denoteInt e1
                            let e2i := LExpr.denoteInt e2
                            match e1i, e2i with
                            | some x, some y =>
                              if y == 0 then .none
                              else .some (.intConst e1.metadata (x / y))
                            | _, _ => .none
                          | _ => .none) },
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int],
      concreteEval :=  some (fun e args => match args with
                              | [e1] =>
                                let e1i := LExpr.denoteInt e1
                                match e1i with
                                | some x => .some (.intConst e1.metadata (- x))
                                | _ => .none
                              | _ => .none) },

    { name := "IntAddAlias",
      attr := #["inline"],
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      body := some esM[((~Int.Add x) y)]
    }]

private def testState : LState TestParams :=
  let ans := LState.addFactory LState.init testBuiltIn
  match ans with
  | .error e => panic s!"{e}"
  | .ok ok => ok


def test8 := TestCase.mk
  testState
  esM[((~IntAddAlias #20) #30)]
  esM[(#50)]

/-- info: true -/
#guard_msgs in
#eval check test8

example: steps_well test8 := by
  unfold steps_well Scopes.toEnv test8
  take_step; apply Step.expand_fn <;> discharge_isCanonicalValue
  take_step; apply Step.eval_fn <;> try discharge_isCanonicalValue
  · inhabited_metadata
  take_refl


def test9 := TestCase.mk
  testState
  esM[((~IntAddAlias #20) x)]
  esM[((~Int.Add #20) x)]

/-- info: true -/
#guard_msgs in
#eval check test9

-- Note: this case diverges from concrete evaluator, because 'x' is not a
-- canonical value! Small step reduces only when the arguments are values,
-- to avoid nondeterminism in the small-step semantics (unless this becomes
-- explicitly allowed in the future).
example: stuck test9 := by
  intro e H; cases H
  case reduce_2 => contradiction
  case reduce_1 => contradiction
  case expand_fn =>
    rename_i Hlfunc Hfv
    conv at Hlfunc => lhs; reduce
    cases Hlfunc
    rename_i Hconst Htmp
    conv at Hconst => lhs; reduce; unfold isCanonicalValue; reduce
    contradiction
  case eval_fn =>
    rename_i Hlfunc _
    conv at Hlfunc => lhs; reduce
    cases Hlfunc
    rename_i Hconst Htmp
    conv at Hconst => lhs; reduce; unfold isCanonicalValue; reduce
    contradiction


-- A sanity check that confirms the parse tree of λλ x y
/-- info: true -/
#guard_msgs in
#eval esM[(λλ (~Int.Add %1) %0)] = esM[((λ(λ (~Int.Add %1))) %0)]


def test10 := TestCase.mk
  LState.init
  esM[(( ((λ(λ ((~Int.Add %1) %0)))) ((λ ((~Int.Add %0) #100)) #5)) x)]
  esM[((~Int.Add ((~Int.Add #5) #100)) x)]

/-- info: true -/
#guard_msgs in
#eval check test10

-- The small step semantics of this example will stuck in the middle because
-- 'Int.Add %0 100' cannot be evaluated because the definition of Int.Add is
-- not available in LState.init .


def test11 := TestCase.mk
  testState
  esM[((~Int.Add #20) #30)]
  esM[#50]

/-- info: true -/
#guard_msgs in
#eval check test11

example: steps_well test11 := by
  unfold steps_well Scopes.toEnv test11
  take_step; apply Step.eval_fn <;> try discharge_isCanonicalValue
  · inhabited_metadata
  take_refl


def test12 := TestCase.mk
  testState
  esM[((((λ(λ (~Int.Add %1) %0))) ((λ ((~Int.Add %0) #100)) #5)) x)]
  esM[((~Int.Add #105) x)]

/-- info: true -/
#guard_msgs in
#eval check test12

example: steps_well test12 := by
  unfold steps_well Scopes.toEnv test12
  take_step; apply Step.reduce_1; inhabited_metadata; apply Step.reduce_2
  · inhabited_metadata;
  · discharge_isCanonicalValue
  · reduce_beta
  take_step; apply Step.reduce_1; inhabited_metadata; apply Step.reduce_2;
  · inhabited_metadata;
  · discharge_isCanonicalValue
  · apply Step.eval_fn <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_refl

/-- info: false -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState.config.factory esM[((~Int.Add #100) #200)]

/-- info: true -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState.config.factory esM[(~Int.Add #100)]


def test13 := TestCase.mk
  testState
  esM[( ((λ(λ (#f %1) %0) #20)) ((λ (~Int.Neg %0)) #5))]
  esM[((#f #20) #-5)]

/-- info: true -/
#guard_msgs in
#eval check test13

-- The small step semantics of this example will stuck in the middle because
-- '(#f 20) e' cannot be evaluated because the definition of #f is
-- not available.


def test14 := TestCase.mk
  testState
  esM[( ((λ(λ (~Int.Add %1) %0)) #20) ((λ (~Int.Neg %0)) x))]
  esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: true -/
#guard_msgs in
#eval check test14

-- The result stops at (.. ((λ (~Int.Neg %0)) x)) because definition of
-- x is not available.
example: steps_well { test14 with e_out := esM[((~Int.Add #20) ((λ (~Int.Neg %0)) x))] }
  := by
  unfold steps_well Scopes.toEnv test14
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_refl


def test15 := TestCase.mk
  testState
  esM[((~Int.Add #20) (~Int.Neg x))]
  esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: true -/
#guard_msgs in
#eval check test15

example: stuck test15 := by
  intros e H
  cases H <;> try contradiction
  case reduce_2 =>
    rename_i a
    cases a <;> try contradiction
    · rename_i a a2 _
      cases a2; cases a
    · rename_i a a2 a3 _
      cases a3
      conv at a => lhs ; reduce; unfold isCanonicalValue; reduce
      contradiction
  case expand_fn =>
    rename_i a a2 a3
    cases a2
    contradiction
  case eval_fn =>
    rename_i a a2 a3 _
    cases a3
    conv at a => lhs ; reduce; unfold isCanonicalValue; reduce
    contradiction


def test16 := TestCase.mk
  testState
  esM[((~Int.Add x) (~Int.Neg #30))]
  esM[((~Int.Add x) #-30)]

/-- info: true -/
#guard_msgs in
#eval check test16

-- test16 stucks because '~Int.Add x' isn't canonical value.
example: stuck test16 := by
  intros e H
  cases H <;> try contradiction
  case reduce_2 =>
    rename_i a a2
    conv at a => lhs; unfold isCanonicalValue; reduce; unfold isCanonicalValue; reduce
    contradiction
  case expand_fn =>
    rename_i a a2 a3
    cases a2
    contradiction
  case eval_fn =>
    rename_i a a2 a3 _
    cases a3
    conv at a => lhs ; reduce; unfold isCanonicalValue; reduce
    contradiction


def test17 := TestCase.mk
  testState
  esM[((λ %0) ((~Int.Add #20) #30))]
  esM[(#50)]

/-- info: true -/
#guard_msgs in
#eval check test17

example: steps_well test17 := by
  unfold steps_well Scopes.toEnv test17
  take_step; apply Step.reduce_2
  · inhabited_metadata
  · discharge_isCanonicalValue
  · apply Step.eval_fn <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; reduce_beta
  take_refl


def test18 := TestCase.mk
  testState
  esM[((~Int.Div #300) ((~Int.Add #2) #1))]
  esM[(#100)]

/-- info: true -/
#guard_msgs in
#eval check test18

example: steps_well test18 := by
  unfold steps_well Scopes.toEnv test18
  take_step; apply Step.reduce_2
  · inhabited_metadata
  · discharge_isCanonicalValue
  · apply Step.eval_fn <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_step; apply Step.eval_fn <;> try discharge_isCanonicalValue
  · simp; rfl
  · inhabited_metadata
  take_refl


def test19 := TestCase.mk
  testState
  esM[((~Int.Add #3) (~Int.Neg #3))]
  esM[(#0)]

/-- info: true -/
#guard_msgs in
#eval check test19

example: steps_well test19 := by
  unfold steps_well Scopes.toEnv test19
  take_step
  · apply Step.reduce_2
    · inhabited_metadata
    · discharge_isCanonicalValue
    · apply Step.eval_fn <;> try discharge_isCanonicalValue
      · inhabited_metadata
  take_step
  · apply Step.eval_fn <;> try rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
    · inhabited_metadata
  take_refl


def test20 := TestCase.mk
  testState
  esM[((~Int.Add (~Int.Neg #3)) #3)]
  esM[(#0)]

/-- info: true -/
#guard_msgs in
#eval check test20

example: steps_well test20 := by
  unfold steps_well Scopes.toEnv test20
  take_step; apply Step.reduce_1
  · inhabited_metadata
  · apply Step.reduce_2
    · inhabited_metadata
    · discharge_isCanonicalValue
    · apply Step.eval_fn <;> try discharge_isCanonicalValue
      · inhabited_metadata
  take_step; apply Step.eval_fn <;> try discharge_isCanonicalValue
  · inhabited_metadata
  take_refl


def test21 := TestCase.mk
  testState
  esM[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]
  esM[((~Int.Div #300) #0)]

/-- info: true -/
#guard_msgs in
#eval check test21

example: steps_well test21 := by
  unfold steps_well Scopes.toEnv test21
  take_step; apply Step.reduce_2
  · inhabited_metadata
  · discharge_isCanonicalValue
  · apply Step.reduce_2
    · inhabited_metadata
    · discharge_isCanonicalValue
    · apply Step.eval_fn <;> try discharge_isCanonicalValue
      · inhabited_metadata
  take_step; apply Step.reduce_2
  · inhabited_metadata
  · discharge_isCanonicalValue
  · apply Step.eval_fn <;> try discharge_isCanonicalValue
    · inhabited_metadata
  take_refl


def test22 := TestCase.mk
  testState
  esM[((~Int.Div x) ((~Int.Add #2) #1))]
  esM[((~Int.Div x) #3)]

/-- info: true -/
#guard_msgs in
#eval check test22

-- TODO: steps_well proof of test22


def test23 := TestCase.mk
  testState
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) x)]
  esM[((~Int.Le #100) x)]

/-- info: true -/
#guard_msgs in
#eval check test23

-- TODO: steps_well proof of test23


def test24 := TestCase.mk
  testState
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]

/-- info: true -/
#guard_msgs in
#eval check test24

-- TODO: stuck proof of test24


def test25 := TestCase.mk
  testState
  esM[((~Int.Div x) x)]
  esM[((~Int.Div x) x) ]

/-- info: true -/
#guard_msgs in
#eval check test25

-- TODO: stuck proof of test25


end EvalTest
---------------------------------------------------------------------
end LExpr
end Lambda
