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
-- Solve equaliy goals
macro "discharge_eq" : tactic => `(tactic |
  solve | simp[eql, eqModuloMeta, LExpr.eraseMetadata,
  LExpr.replaceMetadata, BEq.beq, LExpr.beq])

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
  -- Number of evaluation steps
  n : Nat := 100

def TestCase.new (σ : LState TestParams) (e e_out : LExpr TestParams.mono) (n := 100) : TestCase :=
  { σ, e, e_out, n }

def check (t:TestCase) := (Lambda.LExpr.eval t.n t.σ t.e) == t.e_out

/-- The two kinds of propositions we would like to test! -/
abbrev steps_well (t:TestCase):Prop :=
  Lambda.StepStar (Tbase:=TestParams)
    t.σ.config.factory (Scopes.toEnv t.σ.state) t.e t.e_out

abbrev stuck (t:TestCase):Prop :=
  ∀ eres, ¬ Lambda.Step (Tbase:=TestParams)
    t.σ.config.factory (Scopes.toEnv t.σ.state) t.e eres


-- For Unit metadata, replaceMetadata with (fun _ => ()) is the identity
private theorem replaceMetadata_unit_id :
    ∀ (e : LExpr TestParams.mono), e.replaceMetadata (fun _ => ()) = e := by
  intro e
  induction e with
  | const m c => simp [LExpr.replaceMetadata]
  | op m o ty => simp [LExpr.replaceMetadata]
  | bvar m i => simp [LExpr.replaceMetadata]
  | fvar m n ty => simp [LExpr.replaceMetadata]
  | abs m n ty e ih => simp [LExpr.replaceMetadata, ih]
  | quant m k n ty tr e ih_tr ih_e => simp [LExpr.replaceMetadata, ih_tr, ih_e]
  | app m e1 e2 ih1 ih2 => simp [LExpr.replaceMetadata, ih1, ih2]
  | ite m c t f ih_c ih_t ih_f => simp [LExpr.replaceMetadata, ih_c, ih_t, ih_f]
  | eq m e1 e2 ih1 ih2 => simp [LExpr.replaceMetadata, ih1, ih2]

-- For Unit metadata, eraseMetadata is the identity function
private theorem eraseMetadata_id_unit (e : LExpr TestParams.mono) : e.eraseMetadata = e :=
  replaceMetadata_unit_id e

-- For Unit metadata, eraseMetadata equality implies structural equality
theorem eraseMetadata_eq_of_unit {e1 e2 : LExpr TestParams.mono}
    (h : e1.eraseMetadata = e2.eraseMetadata) : e1 = e2 := by
  rw [eraseMetadata_id_unit e1, eraseMetadata_id_unit e2] at h; exact h

private theorem initState_wf : FactoryWF (LState.init : LState TestParams).config.factory := by
  constructor; intro lf hmem; simp [LState.init, EvalConfig.init] at hmem

-- Prove `steps_well t` via `eval_StepStar` using `t.n` evaluation steps.
macro "prove_steps_well" t:ident wf:ident : tactic =>
  `(tactic| (
    have h := eval_StepStar ($t).σ ($t).e ($t).e_out ($t).n $wf (by native_decide)
    obtain ⟨e', h_step, h_eM⟩ := h
    cases eraseMetadata_eq_of_unit h_eM; exact h_step))


-------------------------------- Tests ------------------------------

def test1 := TestCase.new
  ({Lambda.LState.init with state := [[("m", (mty[int → int], esM[_minit]))]] })
  (esM[λ (if (%0 == #1) then #10 else (m %0))])
  (esM[λ (if (%0 == #1) then #10 else (_minit %0))])

/-- info: true -/
#guard_msgs in
#eval (check test1)

example: steps_well test1 := by prove_steps_well test1 initState_wf


def test2 := TestCase.new
  { LState.init with state := [[("x", (mty[int], esM[#32]))]] }
  esM[((λ (if (%0 == #23) then #17 else #42)) (x : int))]
  esM[#42]

/-- info: true -/
#guard_msgs in
#eval (check test2)

example: steps_well test2 := by prove_steps_well test2 initState_wf


def test3 := TestCase.new
  ∅
  esM[(f #true)]
  esM[(f #true)]

/-- info: true -/
#guard_msgs in
#eval check test3

example: stuck test3 := by
  intros e H
  contradiction


def test4 := TestCase.new
  { LState.init with state :=
      [[("m", (none, esM[(λ (minit %0))]))], -- most recent scope
      [("m", (none, (.intConst () 12)))]] }
  esM[((λ (if (%0 == #23) then #17 else (m %0)) #24))]
  esM[(minit #24)]

/-- info: true -/
#guard_msgs in
#eval check test4

example: steps_well test4 := by prove_steps_well test4 initState_wf


def test5 := TestCase.new
  { LState.init with state := [[("m", (none, esM[minit]))]] }
  esM[((λ (if (%0 == #23) then #17 else (m %0))) #24)]
  esM[(minit #24)]

/-- info: true -/
#guard_msgs in
#eval check test5

example: steps_well test5 := by prove_steps_well test5 initState_wf


def test6 := TestCase.new
  ∅
  esM[if #true then x else y]
  esM[x]

/-- info: true -/
#guard_msgs in
#eval check test6

example: steps_well test6 := by prove_steps_well test6 initState_wf


-- Ill-formed `abs` is returned as-is in this Curry style...
def test7 := TestCase.new
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

-- Prove LFuncWF for each individual test function
private def testFuncs : Array (LFunc TestParams) :=
  #[{ name := "Int.Add",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      concreteEval := some (fun _e args => match args with
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
      concreteEval :=  some (fun _e args => match args with
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
      concreteEval :=  some (fun _e args => match args with
                              | [e1] =>
                                let e1i := LExpr.denoteInt e1
                                match e1i with
                                | some x => .some (.intConst e1.metadata (- x))
                                | _ => .none
                              | _ => .none) },

    { name := "IntAddAlias",
      attr := #[.inline],
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[int],
      body := some esM[((~Int.Add x) y)]
    },

    { name := "Int.Add3",
      inputs := [("x", mty[int]), ("y", mty[int]), ("z", mty[int])],
      output := mty[int],
      concreteEval := some (fun _e args => match args with
                        | [e1, e2, e3] =>
                          let e1i := LExpr.denoteInt e1
                          let e2i := LExpr.denoteInt e2
                          let e3i := LExpr.denoteInt e3
                          match e1i, e2i, e3i with
                          | some x, some y, some z =>
                            .some (.intConst e1.metadata (x + y + z))
                          | _, _, _ => .none
                        | _ => .none) }]

private def testBuiltIn : @Factory TestParams := .ofArray testFuncs

private def testState : LState TestParams :=
  { (LState.init : LState TestParams) with
    config := { (LState.init : LState TestParams).config with factory := testBuiltIn } }

-- For Unit metadata, List.map eraseMetadata is identity
private theorem list_eraseMetadata_id_unit :
    ∀ (l : List (LExpr TestParams.mono)), l.map LExpr.eraseMetadata = l := by
  intro l; induction l with
  | nil => rfl
  | cons h t ih => simp [List.map, eraseMetadata_id_unit, ih]

-- concreteEval_eraseMetadata is trivial when eraseMetadata is the identity
private theorem concreteEval_eraseMetadata_of_unit
    {f : LFunc TestParams} :
    ∀ ceval, f.concreteEval = some ceval →
      ∀ md1 md2 (args1 args2 : List (LExpr TestParams.mono)) res1,
        args1.map LExpr.eraseMetadata = args2.map LExpr.eraseMetadata →
        ceval md1 args1 = some res1 →
        ∃ res2, ceval md2 args2 = some res2 ∧
          LExpr.eraseMetadata res1 = LExpr.eraseMetadata res2 := by
  intro ceval hceval md1 md2 args1 args2 res1 hargs heval
  rw [list_eraseMetadata_id_unit, list_eraseMetadata_id_unit] at hargs
  subst hargs
  -- md1 = md2 = () since both are Unit
  have : md1 = md2 := Subsingleton.elim md1 md2
  subst this
  exact ⟨res1, heval, rfl⟩

-- Tactic to prove concreteEval_argmatch for concrete functions
macro "prove_ceval_argmatch" : tactic => `(tactic|
  (intro fn md args res h1 h2;
   first
   | (simp only [Strata.DL.Util.Func.mk.injEq] at h1
      obtain ⟨_, _, _, _, _, _, _, _, rfl, _⟩ := h1
      revert h2; match args with
      | [] => simp | [_] => simp | [_, _] => simp
      | [_, _, _] => simp | _ :: _ :: _ :: _ :: _ => simp)
   | simp at h1))

private theorem each_testFunc_wf : ∀ lf, lf ∈ testFuncs → LFuncWF lf := by
  intro lf hmem; simp [testFuncs] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl <;> exact {
    arg_nodup := by decide, body_freevars := by decide, body_or_concreteEval := by decide
    typeArgs_nodup := by decide, inputs_typevars_in_typeArgs := by decide
    output_typevars_in_typeArgs := by decide, precond_freevars := by decide
    concreteEval_eraseMetadata := concreteEval_eraseMetadata_of_unit
    concreteEval_argmatch := by prove_ceval_argmatch }

-- Well-formedness of testBuiltIn factory
private theorem testBuiltIn_wf : FactoryWF testBuiltIn := by
  constructor; intro lf hmem
  exact each_testFunc_wf lf (Factory.ofArray_mem hmem)

-- Well-formedness of testState's factory.
private theorem testState_wf : FactoryWF testState.config.factory :=
  testBuiltIn_wf

def test8 := TestCase.new
  testState
  esM[((~IntAddAlias #20) #30)]
  esM[(#50)]

/-- info: true -/
#guard_msgs in
#eval check test8

example: steps_well test8 := by prove_steps_well test8 testState_wf

def test9 := TestCase.new
  testState
  esM[((~IntAddAlias #20) x)]
  esM[((~Int.Add #20) x)]

/-- info: true -/
#guard_msgs in
#eval check test9

example: steps_well test9 := by prove_steps_well test9 testState_wf

-- A sanity check that confirms the parse tree of λλ x y
/-- info: true -/
#guard_msgs in
#eval esM[(λλ (~Int.Add %1) %0)] = esM[((λ(λ (~Int.Add %1))) %0)]


def test10 := TestCase.new
  LState.init
  esM[(( ((λ(λ ((~Int.Add %1) %0)))) ((λ ((~Int.Add %0) #100)) #5)) x)]
  esM[((~Int.Add ((~Int.Add #5) #100)) x)]

/-- info: true -/
#guard_msgs in
#eval check test10

-- The small step semantics of this example will stuck in the middle because
-- 'Int.Add %0 100' cannot be evaluated because the definition of Int.Add is
-- not available in LState.init .

example: steps_well test10 := by prove_steps_well test10 initState_wf


def test11 := TestCase.new
  testState
  esM[((~Int.Add #20) #30)]
  esM[#50]

/-- info: true -/
#guard_msgs in
#eval check test11

example: steps_well test11 := by prove_steps_well test11 testState_wf


def test12 := TestCase.new
  testState
  esM[((((λ(λ (~Int.Add %1) %0))) ((λ ((~Int.Add %0) #100)) #5)) x)]
  esM[((~Int.Add #105) x)]

/-- info: true -/
#guard_msgs in
#eval check test12

example: steps_well test12 := by prove_steps_well test12 testState_wf

/-- info: false -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState.config.factory esM[((~Int.Add #100) #200)]

/-- info: true -/
#guard_msgs in
#eval LExpr.isCanonicalValue testState.config.factory esM[(~Int.Add #100)]


def test13 := TestCase.new
  testState
  esM[( ((λ(λ (#f %1) %0) #20)) ((λ (~Int.Neg %0)) #5))]
  esM[((#f #20) #-5)]

/-- info: true -/
#guard_msgs in
#eval check test13

-- The small step semantics of this example will stuck in the middle because
-- '(#f 20) e' cannot be evaluated because the definition of #f is
-- not available.

example: steps_well test13 := by prove_steps_well test13 testState_wf


def test14 := TestCase.new
  testState
  esM[( ((λ(λ (~Int.Add %1) %0)) #20) ((λ (~Int.Neg %0)) x))]
  esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: true -/
#guard_msgs in
#eval check test14

example: steps_well test14 := by prove_steps_well test14 testState_wf

-- The result stops at (.. ((λ (~Int.Neg %0)) x)) because definition of
-- x is not available.
-- Partial reduction: stops before (~Int.Neg x) is evaluated (x unavailable).
-- This can't use prove_steps_well because no finite n produces this exact partial result.
example: steps_well { test14 with e_out := esM[((~Int.Add #20) ((λ (~Int.Neg %0)) x))] } := by
  unfold steps_well Scopes.toEnv test14
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_step; apply Step.reduce_1; inhabited_metadata; reduce_beta
  take_refl


def test15 := TestCase.new
  testState
  esM[((~Int.Add #20) (~Int.Neg x))]
  esM[((~Int.Add #20) (~Int.Neg x))]

/-- info: true -/
#guard_msgs in
#eval check test15

-- TODO: stuck test15 — (~Int.Neg x) can't be evaluated since x is unresolvable

def test16 := TestCase.new
  testState
  esM[((~Int.Add x) (~Int.Neg #30))]
  esM[((~Int.Add x) #-30)]

/-- info: true -/
#guard_msgs in
#eval check test16

example: steps_well test16 := by prove_steps_well test16 testState_wf

def test17 := TestCase.new
  testState
  esM[((λ %0) ((~Int.Add #20) #30))]
  esM[(#50)]

/-- info: true -/
#guard_msgs in
#eval check test17

example: steps_well test17 := by prove_steps_well test17 testState_wf

def test18 := TestCase.new
  testState
  esM[((~Int.Div #300) ((~Int.Add #2) #1))]
  esM[(#100)]

/-- info: true -/
#guard_msgs in
#eval check test18

example: steps_well test18 := by prove_steps_well test18 testState_wf

def test19 := TestCase.new
  testState
  esM[((~Int.Add #3) (~Int.Neg #3))]
  esM[(#0)]

/-- info: true -/
#guard_msgs in
#eval check test19


example: steps_well test19 := by prove_steps_well test19 testState_wf

def test20 := TestCase.new
  testState
  esM[((~Int.Add (~Int.Neg #3)) #3)]
  esM[(#0)]

/-- info: true -/
#guard_msgs in
#eval check test20

example: steps_well test20 := by prove_steps_well test20 testState_wf

def test21 := TestCase.new
  testState
  esM[((~Int.Div #300) ((~Int.Add #3) (~Int.Neg #3)))]
  esM[((~Int.Div #300) #0)]

/-- info: true -/
#guard_msgs in
#eval check test21

example: steps_well test21 := by prove_steps_well test21 testState_wf

def test22 := TestCase.new
  testState
  esM[((~Int.Div x) ((~Int.Add #2) #1))]
  esM[((~Int.Div x) #3)]

/-- info: true -/
#guard_msgs in
#eval check test22

example: steps_well test22 := by prove_steps_well test22 testState_wf

def test23 := TestCase.new
  testState
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) #1))) x)]
  esM[((~Int.Le #100) x)]

/-- info: true -/
#guard_msgs in
#eval check test23

example: steps_well test23 := by prove_steps_well test23 testState_wf

def test24 := TestCase.new
  testState
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]
  esM[((~Int.Le ((~Int.Div #300) ((~Int.Add #2) y))) x)]

/-- info: true -/
#guard_msgs in
#eval check test24

-- TODO: stuck test24 — Int.Le not in factory, y unresolvable

def test25 := TestCase.new
  testState
  esM[((~Int.Div x) x)]
  esM[((~Int.Div x) x) ]

/-- info: true -/
#guard_msgs in
#eval check test25

-- TODO: stuck test25 — x is unresolvable

-- Ternary function applied through a state variable.

private def testStateFV : LState TestParams :=
  { testState with state := [[("f", (none, esM[~Int.Add3]))]] }

private theorem testStateFV_wf : FactoryWF testStateFV.config.factory :=
  testState_wf

def test_ternary_fv := TestCase.new
  testStateFV
  esM[((((f : int → int → int → int) #10) #20) #30)]
  esM[#60]

/-- info: true -/
#guard_msgs in
#eval check test_ternary_fv

example: steps_well test_ternary_fv := by prove_steps_well test_ternary_fv testStateFV_wf

/-! ### Polymorphic function inlining: type substitution

When a polymorphic function is inlined via `expand_fn`, type variables in the
body are substituted with their concrete instantiations derived from the
operator's type annotation at the call site.
-/

-- polyEq<a>(x : a, y : a) : bool := ∀ (z : a), z == z
private def polyFuncs : Array (LFunc TestParams) :=
  #[{ name := "polyEq",
      typeArgs := ["a"],
      attr := #[.inline],
      inputs := [("x", mty[%a]), ("y", mty[%a])],
      output := mty[bool],
      body := some esM[∀ (%a): (%0 == %0)] }]

private def polyFactory : @Factory TestParams := .ofArray polyFuncs

private def polyState : LState TestParams :=
  { (LState.init : LState TestParams) with
    config := { (LState.init : LState TestParams).config with factory := polyFactory } }

private theorem polyState_wf : FactoryWF polyState.config.factory := by
  constructor; intro lf hmem
  have := Factory.ofArray_mem hmem
  simp [polyFuncs] at this
  rcases this with rfl <;> exact {
    arg_nodup := by decide, body_freevars := by decide, body_or_concreteEval := by decide
    typeArgs_nodup := by decide, inputs_typevars_in_typeArgs := by decide
    output_typevars_in_typeArgs := by decide, precond_freevars := by decide
    concreteEval_eraseMetadata := concreteEval_eraseMetadata_of_unit
    concreteEval_argmatch := by prove_ceval_argmatch }

-- polyEq<bool>(#true, #false): type substitution maps %a to bool in the body
def test_poly_tysubst := TestCase.new
  polyState
  esM[(((~polyEq : bool → bool → bool) #true) #false)]
  esM[∀ (bool): (%0 == %0)]

/-- info: true -/
#guard_msgs in
#eval check test_poly_tysubst

example: steps_well test_poly_tysubst := by prove_steps_well test_poly_tysubst polyState_wf

-- polyPair<a, b>(x : a, y : b) : bool := ∀ (z : a), ∀ (w : b), z == w
-- Tests that type substitution with distinct type parameters maps correctly:
-- %a → int and %b → bool (not swapped).
private def polyPairFuncs : Array (LFunc TestParams) :=
  #[{ name := "polyPair",
      typeArgs := ["a", "b"],
      attr := #[.inline],
      inputs := [("x", mty[%a]), ("y", mty[%b])],
      output := mty[bool],
      body := some esM[∀ (%a): ∀ (%b): (%1 == %0)] }]

private def polyPairFactory : @Factory TestParams := .ofArray polyPairFuncs

private def polyPairState : LState TestParams :=
  { (LState.init : LState TestParams) with
    config := { (LState.init : LState TestParams).config with factory := polyPairFactory } }

private theorem polyPairState_wf : FactoryWF polyPairState.config.factory := by
  constructor; intro lf hmem
  have := Factory.ofArray_mem hmem
  simp [polyPairFuncs] at this
  rcases this with rfl <;> exact {
    arg_nodup := by decide, body_freevars := by decide, body_or_concreteEval := by decide
    typeArgs_nodup := by decide, inputs_typevars_in_typeArgs := by decide
    output_typevars_in_typeArgs := by decide, precond_freevars := by decide
    concreteEval_eraseMetadata := concreteEval_eraseMetadata_of_unit
    concreteEval_argmatch := by prove_ceval_argmatch }

-- polyPair<int, bool>(#42, #true): %a maps to int, %b maps to bool
def test_poly_tysubst_distinct := TestCase.new
  polyPairState
  esM[(((~polyPair : int → bool → bool) #42) #true)]
  esM[∀ (int): ∀ (bool): (%1 == %0)]

/-- info: true -/
#guard_msgs in
#eval check test_poly_tysubst_distinct

example: steps_well test_poly_tysubst_distinct := by
  prove_steps_well test_poly_tysubst_distinct polyPairState_wf

---------------------------------------------------------------------
-- Tests for evalIfCanonical attribute (Issue #812)
-- When a function has `evalIfCanonical 0`, its concreteEval should fire
-- when argument 0 is a canonical value, even if other arguments are symbolic.

private def evalIfCanonicalFuncs : Array (LFunc TestParams) :=
  #[-- concreteEval negates the first int arg and returns (-x) == y.
    -- With evalIfCanonical 0, this fires even when arg 1 is symbolic.
    { name := "NegEq",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      attr := #[.evalIfCanonical 0],
      concreteEval := some (fun _m args => match args with
        | [e1, e2] =>
          match LExpr.denoteInt e1 with
          | some x => .some (.eq () (.intConst () (- x)) e2)
          | none => .none
        | _ => .none) },
    -- Same function but without evalIfCanonical — concreteEval should NOT fire
    -- when the second argument is symbolic.
    { name := "NegEqNoAttr",
      inputs := [("x", mty[int]), ("y", mty[int])],
      output := mty[bool],
      concreteEval := some (fun _m args => match args with
        | [e1, e2] =>
          match LExpr.denoteInt e1 with
          | some x => .some (.eq () (.intConst () (- x)) e2)
          | none => .none
        | _ => .none) }]

private def evalIfCanonicalFactory : @Factory TestParams := .ofArray evalIfCanonicalFuncs

private def evalIfCanonicalState : LState TestParams :=
  { (LState.init : LState TestParams) with
    config := { (LState.init : LState TestParams).config with
      factory := evalIfCanonicalFactory } }

private theorem each_evalIfCanonicalFunc_wf :
    ∀ lf, lf ∈ evalIfCanonicalFuncs → LFuncWF lf := by
  intro lf hmem; simp [evalIfCanonicalFuncs] at hmem
  rcases hmem with rfl | rfl <;> exact {
    arg_nodup := by decide, body_freevars := by decide, body_or_concreteEval := by decide
    typeArgs_nodup := by decide, inputs_typevars_in_typeArgs := by decide
    output_typevars_in_typeArgs := by decide, precond_freevars := by decide
    concreteEval_eraseMetadata := concreteEval_eraseMetadata_of_unit
    concreteEval_argmatch := by prove_ceval_argmatch }

private theorem evalIfCanonicalState_wf :
    FactoryWF evalIfCanonicalState.config.factory := by
  constructor; intro lf hmem
  exact each_evalIfCanonicalFunc_wf lf (Factory.ofArray_mem hmem)

-- Test: evalIfCanonical fires concreteEval when arg 0 is canonical but arg 1 is symbolic.
-- NegEq(#5, x) should reduce to (#-5 == x) — arg 0 is negated, arg 1 passes through.
def test_evalIfCanonical := TestCase.new
  evalIfCanonicalState
  esM[((~NegEq #5) x)]
  esM[(#-5 == x)]

/-- info: true -/
#guard_msgs in
#eval check test_evalIfCanonical

example : steps_well test_evalIfCanonical := by
  prove_steps_well test_evalIfCanonical evalIfCanonicalState_wf

-- Test: without evalIfCanonical, concreteEval does NOT fire when arg 1 is symbolic.
-- NegEqNoAttr(#5, x) stays as NegEqNoAttr(#5, x)
def test_no_evalIfCanonical := TestCase.new
  evalIfCanonicalState
  esM[((~NegEqNoAttr #5) x)]
  esM[((~NegEqNoAttr #5) x)]

/-- info: true -/
#guard_msgs in
#eval check test_no_evalIfCanonical

-- Test: evalIfCanonical with all args canonical also works.
-- NegEq(#5, #10) reduces to (#-5 == #10), which further simplifies to #false.
def test_evalIfCanonical_all_canonical := TestCase.new
  evalIfCanonicalState
  esM[((~NegEq #5) #10)]
  esM[#false]

/-- info: true -/
#guard_msgs in
#eval check test_evalIfCanonical_all_canonical

example : steps_well test_evalIfCanonical_all_canonical := by
  prove_steps_well test_evalIfCanonical_all_canonical evalIfCanonicalState_wf

end EvalTest
---------------------------------------------------------------------
end LExpr
end Lambda
