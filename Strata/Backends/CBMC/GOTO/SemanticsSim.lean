/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Semantics
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

The correspondence requires:
1. A **value correspondence** between `P.Expr` (Imperative values) and
   `Value` (GOTO values)
2. A **store correspondence** between `SemanticStore P` and `Store`
3. An **evaluator correspondence** between `SemanticEval P` and `ExprEval`

## Status

### Completed
- State correspondence definitions (`StoreCorr`, `EvalCorr`)
- Command-level simulation lemmas for `init`, `set`, `havoc`, `assert`, `assume`
- Statement-level simulation structure (block, ite, loop patterns)

### TODO
- [ ] Prove the command-level simulation lemmas (currently `sorry`)
- [ ] Prove the statement-level simulation for `ite` and `loop`
- [ ] Connect to the concrete `concreteEval` evaluator
- [ ] End-to-end theorem: `EvalBlock` implies `ExecProg` on the translated program
- [ ] Handle variable renaming (the translation renames variables to
      `<proc>::<scope>::<name>` format)
-/

namespace CProverGOTO.Semantics

open CProverGOTO Imperative

/-! ## Value Correspondence -/

/-- Correspondence between Imperative expression values and GOTO values.
    This is parameterized by the pure expression type `P` because the
    Imperative dialect is generic over expression types. -/
class ValueCorr (P : PureExpr) where
  /-- Convert an Imperative expression value to a GOTO value. -/
  toValue : P.Expr → Option Value
  /-- Convert a GOTO value back to an Imperative expression. -/
  fromValue : Value → Option P.Expr

/-! ## Store Correspondence -/

/-- Two stores correspond if they agree on all variables (up to value
    correspondence and name mapping).

    `nameMap` translates Imperative identifiers to GOTO symbol names
    (accounting for the renaming done by the translation pipeline). -/
def StoreCorr [DecidableEq P.Ident] [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (σ_imp : SemanticStore P) (σ_goto : Store) : Prop :=
  ∀ id, match σ_imp id with
    | some expr => ∃ v, vc.toValue expr = some v ∧ σ_goto (nameMap id) = some v
    | none => σ_goto (nameMap id) = none

/-! ## Evaluator Correspondence -/

/-- Two evaluators correspond if they agree on all expressions (up to
    value correspondence), given corresponding stores. -/
def EvalCorr [DecidableEq P.Ident] [vc : ValueCorr P]
    (nameMap : P.Ident → String)
    (toGotoExpr : P.Expr → Option Expr)
    (δ : SemanticEval P) (eval : ExprEval) : Prop :=
  ∀ σ_imp σ_goto e ge,
    StoreCorr nameMap σ_imp σ_goto →
    toGotoExpr e = some ge →
    match δ σ_imp e with
    | some v_imp => ∃ v_goto, vc.toValue v_imp = some v_goto ∧ eval σ_goto ge = some v_goto
    | none => True  -- If Imperative eval fails, we don't constrain GOTO eval

/-! ## Command-Level Simulation -/

/-- Simulation for `init` command: DECL + ASSIGN in GOTO.

    If the Imperative `init x ty (some e)` evaluates to `σ'`, then
    executing the corresponding DECL and ASSIGN instructions in GOTO
    produces a corresponding store. -/
theorem sim_init [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {ty : P.Ty} {e : P.Expr} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp e = some v)
    (hinit : InitState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' := by
  sorry

/-- Simulation for `set` command: ASSIGN in GOTO. -/
theorem sim_set [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {toGotoExpr : P.Expr → Option Expr}
    {δ : SemanticEval P} {eval : ExprEval}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {e : P.Expr} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hcorr_e : EvalCorr nameMap toGotoExpr δ eval)
    (heval_imp : δ σ_imp e = some v)
    (hupdate : UpdateState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' := by
  sorry

/-- Simulation for `havoc` command: ASSIGN with nondet in GOTO. -/
theorem sim_havoc [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
    [vc : ValueCorr P]
    {nameMap : P.Ident → String}
    {σ_imp σ_imp' : SemanticStore P} {σ_goto : Store}
    {x : P.Ident} {v : P.Expr}
    (hcorr_s : StoreCorr nameMap σ_imp σ_goto)
    (hupdate : UpdateState P σ_imp x v σ_imp')
    (hname_inj : Function.Injective nameMap) :
    ∃ σ_goto', StoreCorr nameMap σ_imp' σ_goto' := by
  sorry

/-- Simulation for `assert` command: ASSERT instruction in GOTO.

    If the Imperative `assert` evaluates to true (the only case where
    `EvalCmd` has a derivation), then the GOTO ASSERT guard also evaluates
    to true. -/
theorem sim_assert [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
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
  sorry

/-- Simulation for `assume` command: ASSUME instruction in GOTO.

    Same structure as `sim_assert` — if the Imperative `assume` guard is
    true, the GOTO ASSUME guard is also true. -/
theorem sim_assume [DecidableEq P.Ident] [HasFvar P] [HasBool P] [HasNot P]
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
  sorry

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

The simulation requires showing that each loop iteration in the Imperative
semantics corresponds to one traversal of the GOTO loop body, and that
loop termination in the Imperative semantics corresponds to the GOTO
guard becoming false.

Note: The Imperative semantics does not currently define loop evaluation
rules (see the TODO in `StmtSemantics.lean`), so the loop simulation
cannot be completed until that is addressed.
-/

end CProverGOTO.Semantics
