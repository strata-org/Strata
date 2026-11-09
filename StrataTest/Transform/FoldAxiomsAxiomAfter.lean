/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.EqualitySimplificationCorrect
public import Strata.Languages.Core.IntEvalProps
public import Strata.Languages.Core.ProgramProps
public import Strata.Transform.FoldAxiomsEntry
import all Strata.DL.Lambda.LExpr

/-! ## An unsatisfiable axiom after the procedure

The phase gives a procedure `q` only the axioms declared before it, as the verifier does
(`Program.declsBeforeProcedure`). So the axiom premises of
`foldAxioms_equalitySimplification_failsE` and `equalitySimplificationPhase_failsE` range
over those axioms only. On the program

```
procedure q(...) { ... }
axiom false;
```

no store makes every ground axiom of the program evaluate to `true`
(`axiomAfter_groundAxioms_unsat`), while the axiom premises of the two theorems hold, since
no axiom comes before `q` (`axiomAfter_prefix_premises`), and the prefix the theorems
choose is that empty one (`axiomAfter_prefix_nil`). -/

namespace Core.FoldAxioms.AxiomAfterTest

open Lambda Imperative

/-- `axiom f: false;` -/
public abbrev falseAx : Axiom := { name := "f", e := .boolConst () false }

/-- A procedure `q`, then `axiom f: false;`. -/
public abbrev axiomAfter (q : Procedure) (md md' : Imperative.MetaData Expression) : Program :=
  { decls := [.proc q md, .ax falseAx md'] }

/-- No store makes every ground axiom of `axiomAfter` evaluate to `true`. -/
public theorem axiomAfter_groundAxioms_unsat (Fs : Expression.Factory)
    (σ : SemanticStore Expression) (q : Procedure) (md md' : Imperative.MetaData Expression) :
    ¬ GroundAxiomsHold Fs (axiomAfter q md md') σ := by
  intro h
  have hff := h falseAx md' (by simp) (by simp [LExpr.hasBVar])
  rw [Core.eval_boolConst] at hff
  exact HasBool.ttVal_ne_ffVal Fs (Option.some.inj hff).symm

/-- In `axiomAfter`, no declaration comes before `q`, and `declsBeforeProcedure` agrees, so
    the axiom premises of the phase theorems hold in every store, for every folding
    context. -/
public theorem axiomAfter_prefix_premises (Fs : Expression.Factory)
    (σ₀ : SemanticStore Expression) (F : Lambda.Factory CoreLParams) (C : Simplify.Ctx)
    (q : Procedure) (md md' : Imperative.MetaData Expression) :
    (axiomAfter q md md').decls = [] ++ Decl.proc q md :: [.ax falseAx md'] ∧
      (axiomAfter q md md').declsBeforeProcedure q.header.name.name = [] ∧
      AxiomsHold Fs [] σ₀ ∧ AxiomsOps F [] ∧
      AxiomsOps F (([] : List Decl).map (foldDecl C)) ∧
      AxiomsTyped (([] : List Decl).map (foldDecl C)) :=
  ⟨rfl, Program.declsBeforeProcedure_eq rfl fun _ _ h => by simp at h, fun _ _ h => by simp at h,
    fun _ _ h => by simp at h, fun _ _ h => by simp at h, fun _ _ h => by simp at h⟩

/-- The prefix before `q` is `[]` in every decomposition of `axiomAfter`, so it is the
    prefix the phase theorems choose. -/
public theorem axiomAfter_prefix_nil (q : Procedure) (md md' : Imperative.MetaData Expression)
    {pre₀ post : List Decl} (h : (axiomAfter q md md').decls = pre₀ ++ Decl.proc q md :: post) :
    pre₀ = [] := by
  rcases pre₀ with _ | ⟨d, _ | ⟨d', rest⟩⟩ <;> simp_all

end Core.FoldAxioms.AxiomAfterTest

/-! The two phase theorems, the bridge to `declsBeforeProcedure` and this test depend only
on the standard axioms. -/

/--
info: 'Core.FoldAxioms.AxiomAfterTest.axiomAfter_groundAxioms_unsat'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.FoldAxioms.AxiomAfterTest.axiomAfter_groundAxioms_unsat

/--
info: 'Core.FoldAxioms.AxiomAfterTest.axiomAfter_prefix_premises'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.FoldAxioms.AxiomAfterTest.axiomAfter_prefix_premises

/--
info: 'Core.Program.declsBeforeProcedure_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.Program.declsBeforeProcedure_eq

/--
info: 'Core.EqualitySimplification.equalitySimplificationPhase_failsE'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.EqualitySimplification.equalitySimplificationPhase_failsE

/--
info: 'Core.EqualitySimplification.foldAxioms_equalitySimplification_failsE'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.EqualitySimplification.foldAxioms_equalitySimplification_failsE

/--
info: 'Core.FoldAxioms.AxiomAfterTest.axiomAfter_prefix_nil'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.FoldAxioms.AxiomAfterTest.axiomAfter_prefix_nil

/--
info: 'Core.FoldAxioms.axiomsHold_of_entry'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Core.FoldAxioms.axiomsHold_of_entry
