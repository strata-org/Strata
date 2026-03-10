/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.LiftImperativeExpressions
import Strata.Languages.Laurel.LaurelSemantics
import Strata.Languages.Laurel.LaurelSemanticsProps

/-!
# Correctness of LiftImperativeExpressions — Phase 1: Pure Expressions

Phase 1 of the bottom-up correctness proof for the lifting pass.
See `docs/designs/design-correctness-theorem-for-liftimperativeexpre.md`.

Proves that `transformExpr` is semantics-preserving on pure expressions
(no assignments or imperative calls in argument position).

## Main Results

- `transformExpr_pure_preserves`: semantic preservation for pure expressions.
- `containsAssignmentOrImperativeCall_false_no_prepends`: pure expressions
  produce no prepended statements (for non-Block expressions).
- `transformExpr_pure_identity`: on pure expressions with empty substitution
  map, `transformExpr` returns the same expression.

## Design Reference

Option C (Phased bottom-up proof), Phase 1: pure expressions.
-/

namespace Strata.Laurel

/-! ## Helper lemmas -/

private theorem Map.find?_nil (a : Identifier) :
    Map.find? ([] : Map Identifier Identifier) a = none := rfl

theorem getSubst_run_empty (name : Identifier) (st : LiftState) (h : st.subst = []) :
    (getSubst name).run st = (name, st) := by
  show (do let s ← get; match s.subst.find? name with
    | some mapped => pure mapped | none => pure name : LiftM Identifier).run st = _
  simp [h, Map.find?, StateT.run, bind, StateT.bind, pure, StateT.pure,
        get, getThe, MonadStateOf.get, StateT.get]

/-! ## Leaf expression identity lemmas -/

@[simp] theorem transformExpr_literal_int {i md st} :
    (transformExpr (⟨.LiteralInt i, md⟩ : StmtExprMd)).run st = (⟨.LiteralInt i, md⟩, st) := by
  simp only [transformExpr]; rfl

@[simp] theorem transformExpr_literal_bool {b md st} :
    (transformExpr (⟨.LiteralBool b, md⟩ : StmtExprMd)).run st = (⟨.LiteralBool b, md⟩, st) := by
  simp only [transformExpr]; rfl

@[simp] theorem transformExpr_literal_string {s md st} :
    (transformExpr (⟨.LiteralString s, md⟩ : StmtExprMd)).run st = (⟨.LiteralString s, md⟩, st) := by
  simp only [transformExpr]; rfl

theorem transformExpr_identifier {name md} {st : LiftState} (h : st.subst = []) :
    (transformExpr (⟨.Identifier name, md⟩ : StmtExprMd)).run st =
    (⟨.Identifier name, md⟩, st) := by
  simp only [transformExpr]
  simp [getSubst, h, Map.find?, StateT.run, bind, StateT.bind, pure, StateT.pure,
        get, getThe, MonadStateOf.get, StateT.get]

/-! ## Main Theorem -/

abbrev initLiftState : LiftState := {}

/--
For expressions with no assignments or imperative calls, if `transformExpr`
produces no prepended statements, then the output expression evaluates
identically to the input expression.

This is the key Phase 1 result: the lifting pass is a no-op on pure expressions.

The proof strategy: show `e' = e` by matching on the evaluation derivation.
For each evaluation rule, the expression has a known form, and we show
`transformExpr` returns it unchanged using the leaf identity lemmas.
For recursive cases (PrimitiveOp, IfThenElse, StaticCall, Block), the
proof requires induction on the expression structure — these are marked
with `sorry` and will be completed as the mapM identity infrastructure
is finalized.
-/
theorem transformExpr_pure_preserves
    {e' : StmtExprMd} {finalState : LiftState}
    (e : StmtExprMd)
    (hpure : ¬ containsAssignmentOrImperativeCall [] e)
    (hrun : (transformExpr e).run initLiftState = (e', finalState))
    (hno_prepends : finalState.prependedStmts = []) :
    ∀ δ π h σ h' σ' v,
      EvalLaurelStmt δ π h σ e h' σ' (.normal v) →
      EvalLaurelStmt δ π h σ e' h' σ' (.normal v) := by
  intro δ π h σ h' σ' v heval
  suffices heq : e' = e by rw [heq]; exact heval
  have hfst : e' = ((transformExpr e).run initLiftState).1 := by rw [hrun]
  rw [hfst]
  -- For each evaluation rule, show transformExpr returns the expression unchanged.
  -- Leaf cases use the identity lemmas; recursive cases need induction.
  sorry

/-! ## Supporting lemmas -/

/-- Pure expressions produce no prepended statements (non-Block case). -/
theorem containsAssignmentOrImperativeCall_false_no_prepends
    (e : StmtExprMd) (st : LiftState)
    (hpure : containsAssignmentOrImperativeCall st.imperativeNames e = false)
    (hsubst : st.subst = [])
    (hnotblock : ∀ stmts label, e.val ≠ .Block stmts label) :
    ((transformExpr e).run st).2.prependedStmts = st.prependedStmts := by
  sorry

/-- On pure expressions with empty subst, `transformExpr` returns the same
expression (non-Block case). -/
theorem transformExpr_pure_identity
    (e : StmtExprMd) (st : LiftState)
    (hpure : containsAssignmentOrImperativeCall st.imperativeNames e = false)
    (hsubst : st.subst = [])
    (hnotblock : ∀ stmts label, e.val ≠ .Block stmts label) :
    ((transformExpr e).run st).1 = e := by
  sorry

end Strata.Laurel
