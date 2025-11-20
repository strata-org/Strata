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

/-- info: (λ (if (%0 == #1) then #10 else (_minit %0))) -/
#guard_msgs in
#eval format $ Lambda.LExpr.eval 100
                  {Lambda.LState.init with state :=
                      [[("m", (mty[int → int], esM[_minit]))]] }
        esM[λ (if (%0 == #1) then #10 else (m %0))]

-- Small step stucks because abstraction is a value.
example:
  ∀ σ e, ¬ (Lambda.Step σ (esM[(λ (if (%0 == #1) then #10 else (m %0)))]) e)
  := by
  intros σ e H
  contradiction


/-- info: #42 -/
#guard_msgs in
#eval format $ LExpr.eval 100
                          { LState.init with state := [[("x", (mty[int], esM[#32]))]] }
                          esM[((λ (if (%0 == #23) then #17 else #42)) (x : int))]

example:
  Lambda.StepStar
    { LState.init with state := [[("x", (mty[int], esM[#32]))]] }
    esM[((λ (if (%0 == #23) then #17 else #42)) (x : int))]
    esM[#42] := by
  apply StepStar.step
  · apply Step.reduce_2
    · unfold LExpr.isCanonicalValue; rfl
    · repeat constructor
  apply StepStar.step
  · apply Step.beta; unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_reduce_cond
    apply Step.beta_eq <;> unfold isCanonicalValue <;> rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_beta_else
  apply StepStar.refl


/-- info: (f #true) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[(f #true)]

theorem nil_state_empty {Ty}: (∅:LState Ty).state = [] := by
  rfl

example:
  ∀ e, ¬ Lambda.Step ∅ esM[(f #true)] e := by
  intros e H
  contradiction


/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state :=
                        [[("m", (none, esM[(λ (minit %0))]))], -- most recent scope
                         [("m", (none, (.intConst 12)))]] }
                    esM[((λ (if (%0 == #23) then #17 else (m %0)) #24))]

example:
  Lambda.StepStar
    { LState.init with state :=
      [[("m", (none, esM[(λ (minit %0))]))], -- most recent scope
      [("m", (none, (.intConst 12)))]] }
    esM[((λ (if (%0 == #23) then #17 else (m %0)) #24))]
    esM[(minit #24)] := by
  apply StepStar.step
  · apply Step.beta; unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_reduce_cond
    apply Step.beta_eq <;> unfold isCanonicalValue <;> rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_beta_else
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.expand_fvar
    rfl
  apply StepStar.step
  · apply Step.beta
    unfold isCanonicalValue; rfl
  apply StepStar.refl


/-- info: (minit #24) -/
#guard_msgs in
#eval format $ LExpr.eval 100
                    { LState.init with state := [[("m", (none, esM[minit]))]] }
                    esM[((λ (if (%0 == #23) then #17 else (m %0))) #24)]

example:
  Lambda.StepStar
    { LState.init with state := [[("m", (none, esM[minit]))]] }
    esM[((λ (if (%0 == #23) then #17 else (m %0))) #24)]
    esM[(minit #24)] := by
  apply StepStar.step
  · apply Step.beta; unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_reduce_cond
    apply Step.beta_eq <;> unfold isCanonicalValue <;> rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.ite_beta_else
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.expand_fvar
    rfl
  apply StepStar.refl


/-- info: x -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[if #true then x else y]

example:
  Lambda.StepStar ∅ esM[if #true then x else y] esM[x] := by
  apply StepStar.step
  · constructor
  apply StepStar.refl


-- Ill-formed `abs` is returned as-is in this Curry style...
/-- info: (λ %1) -/
#guard_msgs in
#eval format $ LExpr.eval 10 ∅ esM[(λ %1)]

example:
  ∀ e, ¬ Lambda.Step ∅ esM[(λ %1)] e := by
  intros e H
  contradiction


/-- info: ((λ %1) #true) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 ∅ (.app (.mdata ⟨"x"⟩ (.abs .none (.bvar 1))) .true)

example:
  ∀ e, ¬ Lambda.Step (IDMeta:=Unit) ∅
      (.app (.mdata ⟨"x"⟩ (.abs .none (.bvar 1))) .true) e := by
  intros e H
  contradiction


/- Tests for evaluation of BuiltInFunctions. -/

open LTy.Syntax

private def testBuiltIn : @Factory Unit :=
  #[{ name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval := some (fun e args => match args with
                        | [e1, e2] =>
                          let e1i := LExpr.denoteInt e1
                          let e2i := LExpr.denoteInt e2
                          match e1i, e2i with
                          | some x, some y => .intConst (x + y)
                          | _, _ => e
                        | _ => e) },
    { name := "Int.Div",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval :=  some (fun e args => match args with
                          | [e1, e2] =>
                            let e1i := LExpr.denoteInt e1
                            let e2i := LExpr.denoteInt e2
                            match e1i, e2i with
                            | some x, some y =>
                              if y == 0 then e else .intConst (x / y)
                            | _, _ => e
                          | _ => e) },
    { name := "Int.Neg",
      inputs := [("x", mty[int])],
      output := mty[int],
      concreteEval :=  some (fun e args => match args with
                              | [e1] =>
                                let e1i := LExpr.denoteInt e1
                                match e1i with
                                | some x => .intConst (- x)
                                | _ => e
                              | _ => e) },

    { name := "IntAddAlias",
      attr := #["inline"],
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      body := some esM[((~Int.Add x) y)]
    }]

private def testState : LState Unit :=
  let ans := LState.addFactory LState.init testBuiltIn
  match ans with
  | .error e => panic s!"{e}"
  | .ok ok => ok

/-- info: #50 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~IntAddAlias #20) #30)]

example:
  Lambda.StepStar testState esM[((~IntAddAlias #20) #30)] esM[#50] := by
  apply StepStar.step
  · apply Step.expand_fn <;> try rfl
    · simp only [HAppend.hAppend, Append.append, List.append, List.all]
      unfold isCanonicalValue; rfl
  apply StepStar.step
  · apply Step.eval_fn
    · rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
    · conv => lhs; rhs; reduce
  apply StepStar.refl

/-- info: ((~Int.Add #20) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~IntAddAlias #20) x)]

-- Note: this case diverges from concrete evaluator, because 'x' is not a
-- canonical value! Small step reduces only when the arguments are values,
-- to avoid nondeterminism in the small-step semantics (unless this becomes
-- explicitly allowed in the future).
example:
  ∀ e, ¬ Lambda.Step testState esM[((~IntAddAlias #20) x)] e
  := by
  intro e H; cases H
  case reduce_2 =>
    contradiction
  case reduce_1 =>
    contradiction
  case expand_fn =>
    rename_i Hlfunc Hfv
    conv at Hlfunc =>
      lhs; reduce
    cases Hlfunc
    rename_i Hconst Htmp
    conv at Hconst =>
      lhs; reduce; unfold isCanonicalValue; reduce
    contradiction
  case eval_fn =>
    rename_i Hlfunc
    conv at Hlfunc =>
      lhs; reduce
    cases Hlfunc
    rename_i Hconst Htmp
    conv at Hconst =>
      lhs; reduce; unfold isCanonicalValue; reduce
    contradiction


-- A sanity check that confirms the parse tree of λλ x y
/-- info: true -/
#guard_msgs in
#eval esM[(λλ (~Int.Add %1) %0)] = esM[((λ(λ (~Int.Add %1))) %0)]

/-- info: ((~Int.Add ((~Int.Add #5) #100)) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 LState.init
  esM[(( ((λ(λ ((~Int.Add %1) %0)))) ((λ ((~Int.Add %0) #100)) #5)) x)]

-- The small step semantics of this example will stuck in the middle because
-- 'Int.Add %0 100' cannot be evaluated because the definition of Int.Add is
-- not available in LState.init .


/-- info: #50 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #20) #30)]

example:
  Lambda.StepStar testState esM[((~Int.Add #20) #30)] esM[#50] := by
  apply StepStar.step
  · apply Step.eval_fn <;> try rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  apply StepStar.refl


/-- info: ((~Int.Add #105) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState
  esM[((((λ(λ (~Int.Add %1) %0))) ((λ ((~Int.Add %0) #100)) #5)) x)]

/-- info: false -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState esM[((~Int.Add #100) #200)]

/-- info: true -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState esM[(~Int.Add #100)]

example:
  Lambda.StepStar testState
    esM[((((λ(λ (~Int.Add %1) %0))) ((λ ((~Int.Add %0) #100)) #5)) x)]
    esM[((~Int.Add #105) x)] := by
  unfold LExpr.absUntyped
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.reduce_2
    · unfold isCanonicalValue; rfl
    · apply Step.beta
      · unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.reduce_2
    · unfold isCanonicalValue; rfl
    · apply Step.eval_fn
      · conv => lhs; reduce; unfold isCanonicalValue; reduce
      · conv => lhs; reduce; unfold isCanonicalValue; reduce
      · conv => lhs; reduce
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.beta
    · unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.beta
    · unfold isCanonicalValue; rfl
  conv => lhs; reduce
  apply StepStar.refl


/-- info: ((#f #20) #-5) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState
  esM[( ((λ(λ (#f %1) %0) #20)) ((λ (~Int.Neg %0)) #5))]

-- The small step semantics of this example will stuck in the middle because
-- '(#f 20) e' cannot be evaluated because the definition of #f is
-- not available.


/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState
  esM[( ((λ(λ (~Int.Add %1) %0)) #20) ((λ (~Int.Neg %0)) x))]

-- The result stops at (.. ((λ (~Int.Neg %0)) x)) because definition of
-- x is not available.
example:
  Lambda.StepStar testState
    esM[( ((λ(λ (~Int.Add %1) %0)) #20) ((λ (~Int.Neg %0)) x))]
    esM[((~Int.Add #20) ((λ (~Int.Neg %0)) x))]
  := by
  unfold LExpr.absUntyped
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.beta
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.beta
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.refl


/-- info: ((~Int.Add #20) (~Int.Neg x)) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: ((~Int.Add x) #-30) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add x) (~Int.Neg #30))]

/-- info: #50 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((λ %0) ((~Int.Add #20) #30))]

example:
  Lambda.StepStar testState
    esM[((λ %0) ((~Int.Add #20) #30))]
    esM[(#50)]
  := by
  unfold LExpr.absUntyped
  apply StepStar.step
  · apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
    · apply Step.eval_fn <;> try rfl
      · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.beta
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.refl


/-- info: #100 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div #300) ((~Int.Add #2) #1))]

example:
  Lambda.StepStar testState esM[((~Int.Div #300) ((~Int.Add #2) #1))] esM[(#100)]
  := by
  apply StepStar.step
  · apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
    · apply Step.eval_fn <;> try rfl
      · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.eval_fn <;> try rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.refl

/-- info: #0 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add #3) (~Int.Neg #3))]

example:
  Lambda.StepStar testState esM[((~Int.Add #3) (~Int.Neg #3))] esM[(#0)]
  := by
  apply StepStar.step
  · apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
    · apply Step.eval_fn <;> try rfl
      · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.eval_fn <;> try rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce
  conv => lhs; reduce
  apply StepStar.refl

/-- info: #0 -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Add (~Int.Neg #3)) #3)]

example:
  Lambda.StepStar testState esM[((~Int.Add (~Int.Neg #3)) #3)] esM[(#0)]
  := by
  apply StepStar.step
  · apply Step.reduce_1
    apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
    · apply Step.eval_fn <;> try rfl
      · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.eval_fn <;> try rfl
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
  apply StepStar.refl

/-- info: ((~Int.Div #300) #0) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]

example:
  Lambda.StepStar testState
    esM[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]
    esM[((~Int.Div #300) #0)]
  := by
  apply StepStar.step
  · apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
    · apply Step.reduce_2
      · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
      · apply Step.eval_fn <;> try rfl
        · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
  conv => lhs; reduce
  apply StepStar.step
  · apply Step.reduce_2
    · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
    · apply Step.eval_fn <;> try rfl
      · conv => lhs; reduce; unfold isCanonicalValue; reduce; unfold isCanonicalValue
  conv => lhs; reduce
  apply StepStar.refl

/-- info: ((~Int.Div x) #3) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 10 testState esM[((~Int.Div x) ((~Int.Add #2) #1))]

/-- info: ((~Int.Le #100) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) x)]

/--
info: ((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)
-/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]

/-- info: ((~Int.Div x) x) -/
#guard_msgs in
#eval format $ LExpr.eval (IDMeta:=Unit) 200 testState
                esM[((~Int.Div x) x)]


end EvalTest
---------------------------------------------------------------------
end LExpr
end Lambda
