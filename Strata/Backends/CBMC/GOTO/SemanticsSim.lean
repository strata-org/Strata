/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Semantics
import Strata.Backends.CBMC.GOTO.SemanticsProps
import Strata.Backends.CBMC.GOTO.SemanticsEval
import Strata.DL.Imperative.CmdSemantics

/-!
# Simulation Relation: Imperative Semantics ↔ GOTO Semantics

This file defines the state correspondence between Strata's Imperative dialect
semantics (`EvalCmd`, `EvalStmt`) and the GOTO operational semantics
(`StepInstr`, `ExecProg`), and proves key simulation lemmas.

## Architecture

The translation from Imperative to GOTO proceeds in two stages:
1. **Commands** (`Cmd.toGotoInstructions`): Each Imperative command becomes
   one or more GOTO instructions.
2. **Statements** (`Stmt.toGotoInstructions`): Control flow (blocks, ite, loops)
   becomes GOTO/LOCATION instruction patterns.

The simulation relation must show that for each Imperative evaluation step,
the corresponding GOTO instructions produce an equivalent state transition.

## State Correspondence

The Imperative semantics uses:
- `SemanticStore P` = `P.Ident → Option P.Expr` (maps identifiers to expressions)
- `SemanticEval P` = `SemanticStore P → P.Expr → Option P.Expr` (expression evaluator)

The GOTO semantics uses:
- `Store` = `String → Option Value` (maps symbol names to values)
- `ExprEval` = `Store → Expr → Option Value` (expression evaluator)

## Status

### Completed
- State correspondence definitions (`StoreCorr`, `EvalCorr`)
- Command-level simulation proofs for `assert`, `assume`
- Command-level simulation proofs for `init`, `set`, `havoc`
  (existential witness constructed; correspondence proved)

### TODO
- [ ] Statement-level simulation for `ite` and `loop`
- [ ] Connect to the concrete `concreteEval` evaluator
- [ ] End-to-end theorem: `EvalBlock` implies `ExecProg` on the translated program
- [ ] Handle variable renaming (the translation renames variables to
      `<proc>::<scope>::<name>` format)
-/

namespace CProverGOTO.Semantics

open CProverGOTO Imperative

/-! ## Value Correspondence -/

/-- Correspondence between Imperative expression values and GOTO values.
    Requires that boolean truth values map correctly. -/
class ValueCorr (P : PureExpr) [HasBool P] where
  /-- Convert an Imperative expression value to a GOTO value. -/
  toValue : P.Expr → Option Value
  /-- Convert a GOTO value back to an Imperative expression. -/
  fromValue : Value → Option P.Expr
  /-- `tt` maps to `vBool true`. -/
  tt_corr : toValue HasBool.tt = some (.vBool true)
  /-- `ff` maps to `vBool false`. -/
  ff_corr : toValue HasBool.ff = some (.vBool false)

/-! ## Store Correspondence -/

/-- Two stores correspond if they agree on all variables (up to value
    correspondence and name mapping).

    `nameMap` translates Imperative identifiers to GOTO symbol names
    (accounting for the renaming done by the translation pipeline). -/
def StoreCorr [DecidableEq P.Ident] [HasBool P] [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (σ_imp : SemanticStore P) (σ_goto : Store) : Prop :=
  ∀ id, match σ_imp id with
    | some expr => ∃ v, vc.toValue expr = some v ∧ σ_goto (nameMap id) = some v
    | none => σ_goto (nameMap id) = none

/-! ## Evaluator Correspondence -/

/-- Two evaluators correspond if they agree on all expressions (up to
    value correspondence), given corresponding stores. -/
def EvalCorr [DecidableEq P.Ident] [HasBool P] [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (toGotoExpr : P.Expr → Option Expr)
    (δ : SemanticEval P) (eval : ExprEval) : Prop :=
  ∀ σ_imp σ_goto e ge,
    StoreCorr nameMap σ_imp σ_goto →
    toGotoExpr e = some ge →
    match δ σ_imp e with
    | some v_imp => ∃ v_goto, vc.toValue v_imp = some v_goto ∧ eval σ_goto ge = some v_goto
    | none => True

/-! ## Command-Level Simulation: Assert and Assume -/

/-- If the Imperative evaluator says `e` is `tt`, and the evaluators correspond,
    then the GOTO evaluator says the translated expression is `vBool true`. -/
theorem sim_assert [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp : SemanticStore P} {σ_goto : Store}
    {e : P.Expr} {ge : Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp e = some HasBool.tt)
    (htrans : toGotoExpr e = some ge) :
    eval σ_goto ge = some (.vBool true) := by
  have h := hcorr_e σ_imp σ_goto e ge hcorr_s htrans
  rw [heval_imp] at h
  obtain ⟨v_goto, hv, heval⟩ := h
  rw [vc.tt_corr] at hv
  exact Option.some.inj hv ▸ heval

/-- Same as `sim_assert` — if the Imperative `assume` guard is true,
    the GOTO ASSUME guard is also true. -/
theorem sim_assume [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp : SemanticStore P} {σ_goto : Store}
    {e : P.Expr} {ge : Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp e = some HasBool.tt)
    (htrans : toGotoExpr e = some ge) :
    eval σ_goto ge = some (.vBool true) :=
  sim_assert hcorr_s hcorr_e heval_imp htrans

/-! ## Command-Level Simulation: Store-Modifying Commands -/

/-- Simulation for `set` command: ASSIGN in GOTO.

    If the Imperative `set x e` evaluates to `σ_imp'` via `UpdateState`,
    then updating the GOTO store at `nameMap x` with the corresponding
    value produces a corresponding store. -/
theorem sim_set [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hv_conv : ∃ vg, vc.toValue v = some vg)
    (hupdate : UpdateState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto' : Store,
      StoreCorr nameMap σ_imp' σ_goto' := by
  obtain ⟨vg, hvg⟩ := hv_conv
  exact ⟨σ_goto.update (nameMap x) vg, fun id => by
    cases hupdate with
    | update hold hnew hrest =>
      by_cases heq : x = id
      · subst heq
        rw [hnew]; exact ⟨vg, hvg, Store.update_same ..⟩
      · rw [hrest id heq]
        have hne : nameMap x ≠ nameMap id := fun h => heq (hname_inj h)
        rw [Store.update_other _ _ _ _ hne.symm]
        exact hcorr_s id⟩

/-- Simulation for `init` (unconstrained): DECL in GOTO.

    If the Imperative `init x ty none` evaluates to `σ_imp'` via
    `InitState` with an arbitrary value, then updating the GOTO store
    produces a corresponding store. -/
theorem sim_init_unconstrained [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hv_conv : ∃ vg, vc.toValue v = some vg)
    (hinit : InitState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto' : Store,
      StoreCorr nameMap σ_imp' σ_goto' := by
  obtain ⟨vg, hvg⟩ := hv_conv
  exact ⟨σ_goto.update (nameMap x) vg, fun id => by
    cases hinit with
    | init hnone hnew hrest =>
      by_cases heq : x = id
      · subst heq
        rw [hnew]; exact ⟨vg, hvg, Store.update_same ..⟩
      · rw [hrest id heq]
        have hne : nameMap x ≠ nameMap id := fun h => heq (hname_inj h)
        rw [Store.update_other _ _ _ _ hne.symm]
        exact hcorr_s id⟩

/-- Simulation for `init` command: DECL + ASSIGN in GOTO.

    If the Imperative `init x ty (some e)` evaluates to `σ_imp'` via
    `InitState`, then declaring and assigning in the GOTO store produces
    a corresponding store. -/
theorem sim_init [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hv_conv : ∃ vg, vc.toValue v = some vg)
    (hinit : InitState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto' : Store,
      StoreCorr nameMap σ_imp' σ_goto' :=
  sim_init_unconstrained hcorr_s hv_conv hinit hname_inj

/-- Simulation for `havoc` command: ASSIGN with nondet in GOTO.

    If the Imperative `havoc x` evaluates to `σ_imp'` via `UpdateState`
    with some arbitrary value `v`, then there exists a GOTO value and
    store that correspond. -/
theorem sim_havoc [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hv_conv : ∃ vg, vc.toValue v = some vg)
    (hupdate : UpdateState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto' : Store,
      StoreCorr nameMap σ_imp' σ_goto' := by
  obtain ⟨vg, hvg⟩ := hv_conv
  exact ⟨σ_goto.update (nameMap x) vg, fun id => by
    cases hupdate with
    | update hold hnew hrest =>
      by_cases heq : x = id
      · subst heq
        rw [hnew]; exact ⟨vg, hvg, Store.update_same ..⟩
      · rw [hrest id heq]
        have hne : nameMap x ≠ nameMap id := fun h => heq (hname_inj h)
        rw [Store.update_other _ _ _ _ hne.symm]
        exact hcorr_s id⟩

/-! ## Full Command Simulation -/

/-- The full command simulation: if `EvalCmd` steps from `σ_imp` to `σ_imp'`,
    and the stores correspond, then there exists a corresponding GOTO store.

    This combines the individual command simulations above. The proof
    dispatches on the `EvalCmd` constructor.

    The `hval_total` hypothesis requires that every Imperative expression
    value is convertible to a GOTO value. This is a reasonable assumption:
    the Imperative dialect and GOTO share the same value domain (booleans,
    integers, bitvectors, etc.), and the translation only handles types
    that have GOTO counterparts. -/
theorem sim_cmd [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {_toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {_eval : ExprEval}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {c : Cmd P}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (heval : EvalCmd P δ σ_imp c σ_imp')
    (hname_inj : Function.Injective nameMap)
    -- All expression values are convertible to GOTO values
    (hval_total : ∀ v : P.Expr, ∃ vg, vc.toValue v = some vg) :
    ∃ σ_goto' : Store, StoreCorr nameMap σ_imp' σ_goto' := by
  cases heval with
  | eval_init hev hinit _ =>
    exact sim_init hcorr_s (hval_total _) hinit hname_inj
  | eval_init_unconstrained hinit _ =>
    exact sim_init_unconstrained hcorr_s (hval_total _) hinit hname_inj
  | eval_set hev hup _ =>
    exact sim_set hcorr_s (hval_total _) hup hname_inj
  | eval_havoc hup _ =>
    exact sim_havoc hcorr_s (hval_total _) hup hname_inj
  | eval_assert _ _ => exact ⟨σ_goto, hcorr_s⟩
  | eval_assume _ _ => exact ⟨σ_goto, hcorr_s⟩
  | eval_cover _ => exact ⟨σ_goto, hcorr_s⟩

/-! ## Statement-Level Simulation Structure

The statement-level simulation follows the structure of
`Stmt.toGotoInstructions` in `ToCProverGOTO.lean`:

### Block
A block `block label body` becomes:
  LOCATION label_loc
  <body instructions>
  LOCATION end_block_label_loc

The simulation for blocks follows by induction on the statement list,
composing the command-level simulations.

### If-Then-Else
`ite cond thenb elseb` becomes:
  GOTO [!cond] else_loc
  <then instructions>
  GOTO end_loc
  LOCATION else_loc
  <else instructions>
  LOCATION end_loc

The simulation requires showing that:
- If `cond` is true in the Imperative semantics, the GOTO guard `!cond`
  is false, so the GOTO falls through to the then-branch.
- If `cond` is false, the GOTO guard `!cond` is true, so the GOTO jumps
  to the else-branch.

### Loop
`loop guard body` becomes:
  LOCATION loop_start
  GOTO [!guard] loop_end
  <body instructions>
  GOTO loop_start
  LOCATION loop_end

Note: The Imperative semantics does not currently define loop evaluation
rules (see the TODO in `StmtSemantics.lean`), so the loop simulation
cannot be completed until that is addressed.
-/

/-! ## If-Then-Else Simulation -/

/-- If the Imperative evaluator says `cond` is `tt`, and the GOTO translation
    negates it to `Not(ge)`, then the GOTO evaluator says `Not(ge)` is
    `vBool false`, so the GOTO falls through (does not jump). -/
theorem sim_ite_true_guard [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp : SemanticStore P} {σ_goto : Store}
    {cond : P.Expr} {ge : Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp cond = some HasBool.tt)
    (htrans : toGotoExpr cond = some ge)
    -- The GOTO evaluator respects negation
    (hnot : ∀ σ g, eval σ g = some (.vBool true) →
                    eval σ (Expr.not g) = some (.vBool false)) :
    eval σ_goto (Expr.not ge) = some (.vBool false) :=
  hnot _ _ (sim_assert hcorr_s hcorr_e heval_imp htrans)

/-- Dual: if `cond` is `ff`, then `Not(ge)` is `vBool true`, so the GOTO jumps. -/
theorem sim_ite_false_guard [DecidableEq P.Ident] [HasBool P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp : SemanticStore P} {σ_goto : Store}
    {cond : P.Expr} {ge : Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp cond = some HasBool.ff)
    (htrans : toGotoExpr cond = some ge)
    -- The GOTO evaluator respects negation
    (hnot : ∀ σ g, eval σ g = some (.vBool false) →
                    eval σ (Expr.not g) = some (.vBool true)) :
    eval σ_goto (Expr.not ge) = some (.vBool true) := by
  have h := hcorr_e σ_imp σ_goto cond ge hcorr_s htrans
  rw [heval_imp] at h
  obtain ⟨v_goto, hv, heval⟩ := h
  rw [vc.ff_corr] at hv
  exact hnot _ _ (Option.some.inj hv ▸ heval)

end CProverGOTO.Semantics
