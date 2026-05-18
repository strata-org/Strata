/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.Program
public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Util.Relations

public section

/-! # Small-step operational semantics for the CBMC GOTO language

This module defines a small-step operational semantics for the subset of
`CProverGOTO.Instruction` types emitted by `coreCFGToGotoTransform`:

  `LOCATION`, `DECL`, `ASSIGN`, `ASSERT`, `ASSUME`, `GOTO`, `END_FUNCTION`.

`FUNCTION_CALL` is intentionally not modeled at this milestone (the correctness
theorem is restricted to call-free programs). Other instruction types
(`SKIP`, `SET_RETURN_VALUE`, `DEAD`, `INCOMPLETE_GOTO`, threading, atomicity,
exceptions) are also out of scope.

The shape mirrors `Strata.DL.Imperative.CFGSemantics`:

* a configuration is either an in-flight `(pc, store, failed)` triple or a
  `terminal` configuration carrying the final store and failure flag;
* `StepGoto` is the single-step relation, parameterized by an expression
  evaluator `δ_goto` that interprets GOTO `Expr`s against an
  `Imperative.SemanticStore`;
* `StepGotoStar` is the reflexive-transitive closure, defined exactly like
  `StepCFGStar` via `ReflTrans`.

This separation keeps GOTO's evaluator independent of Core's: the
forward-simulation theorem will assume a hypothesis relating the two via
`Lambda.LExpr.toGotoExprCtx`. -/

namespace CProverGOTO

open Imperative

/-- Evaluator for GOTO expressions against an `Imperative.SemanticStore`.

The evaluator is parametric because the small-step relation is independent of
how a particular GOTO `Expr` is interpreted; the simulation proof bridges this
to Core's evaluator via a hypothesis.

Returns `none` when the expression is undefined in the given store; otherwise
returns the resulting `P.Expr` value. -/
@[expose] abbrev SemanticEvalGoto (P : PureExpr) :=
  SemanticStore P → Expr → Option P.Expr

/-- Boolean view of a GOTO evaluator: whether the expression is `tt` / `ff`. -/
@[expose] abbrev SemanticEvalGotoBool (P : PureExpr) [HasBool P] :=
  SemanticStore P → Expr → Option Bool

/-- A GOTO program execution configuration.

  * `running pc σ failed` — currently executing the instruction at index `pc`
    in the program's instruction array, with store `σ` and failure flag
    `failed`.
  * `terminal σ failed` — execution has reached an `END_FUNCTION` instruction.

The `failed` flag accumulates assertion failures (matching the convention used
by `Imperative.EvalCmd` and `Imperative.CFGConfig`). -/
inductive GotoConfig (P : PureExpr) : Type where
  | running : Nat → SemanticStore P → Bool → GotoConfig P
  | terminal : SemanticStore P → Bool → GotoConfig P

/-- Monotonically update the failure flag of a `GotoConfig`. -/
def GotoConfig.updateFailure : GotoConfig P → Bool → GotoConfig P
  | .running pc σ failed, b => .running pc σ (failed || b)
  | .terminal σ failed, b => .terminal σ (failed || b)

/-- Read instruction `pc` from a program's instruction array, if in range. -/
@[expose] def Program.instrAt (pgm : Program) (pc : Nat) : Option Instruction :=
  pgm.instructions[pc]?

/-- Small-step operational semantics for GOTO programs.

Parameters:

* `δ_goto : SemanticEvalGoto P` — evaluates GOTO `Expr`s in a given store.
* `δ_cmd  : SemanticEval P`     — evaluates `Cmd`-level expressions (used to
  state pre-conditions on `EvalCmd`).
* `EvalCmd : EvalCmdParam P (Cmd P)` — the existing imperative-command
  evaluation relation, reused unchanged for assignment-like steps.

The constructors cover only the instruction types emitted by
`coreCFGToGotoTransform`. Each constructor advances `pc` to the next
instruction unless control flow demands otherwise (`GOTO`, `END_FUNCTION`).

Notes on evaluator usage:

* `step_assign`/`step_decl` decompose the instruction's `Code` into the
  symbol and right-hand side, then existentially witness an
  `Imperative.UpdateState` / `InitState` describing the abstract effect.
  This keeps the relation independent of how GOTO `Expr`s are evaluated
  on the symbol/RHS sides — the bridge is a hypothesis of the simulation.

* `step_assert_*` and `step_assume_pass` use the boolean GOTO evaluator
  directly on `instr.guard`. -/
inductive StepGoto
    (P : PureExpr) [HasBool P] [HasNot P]
    (δ_goto : SemanticEvalGoto P)
    (δ_goto_bool : SemanticEvalGotoBool P) :
    Program → GotoConfig P → GotoConfig P → Prop where

  /-- A `LOCATION` instruction is semantically a skip: advance `pc`, leave
  the store and failure flag unchanged. -/
  | step_location :
    pgm.instrAt pc = some instr →
    instr.type = .LOCATION →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed)

  /-- A `DECL` instruction introduces a new variable, initialized to an
  unspecified value. The abstract `InitState` relation describes the
  resulting store. The plain DECL form maps to havoc-style initialization;
  any subsequent value assignment is materialized as a separate `ASSIGN`
  instruction (matching how `coreCFGToGotoTransform` lowers
  `Imperative.Cmd.init`). -/
  | step_decl :
    pgm.instrAt pc = some instr →
    instr.type = .DECL →
    InitState P σ x v σ' →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ' failed)

  /-- An `ASSIGN` instruction updates a previously-declared variable.
  `δ_goto σ rhs = some v` pins down the right-hand-side value, and
  `UpdateState` describes the store change. -/
  | step_assign :
    pgm.instrAt pc = some instr →
    instr.type = .ASSIGN →
    δ_goto σ rhs = some v →
    UpdateState P σ x v σ' →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ' failed)

  /-- `ASSERT` with a guard that holds: store and failure flag are
  unchanged, `pc` advances. -/
  | step_assert_pass :
    pgm.instrAt pc = some instr →
    instr.type = .ASSERT →
    δ_goto_bool σ instr.guard = some true →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed)

  /-- `ASSERT` with a guard that fails: store unchanged, failure flag set,
  `pc` still advances (matches `EvalCmd.eval_assert_fail`). -/
  | step_assert_fail :
    pgm.instrAt pc = some instr →
    instr.type = .ASSERT →
    δ_goto_bool σ instr.guard = some false →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ true)

  /-- `ASSUME` with a guard that holds: behaves like a skip on the store. -/
  | step_assume_pass :
    pgm.instrAt pc = some instr →
    instr.type = .ASSUME →
    δ_goto_bool σ instr.guard = some true →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed)

  /-- A `GOTO` instruction whose guard evaluates to `true` jumps to its
  target instruction. -/
  | step_goto_taken :
    pgm.instrAt pc = some instr →
    instr.type = .GOTO →
    instr.target = some target →
    δ_goto_bool σ instr.guard = some true →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running target σ failed)

  /-- A `GOTO` instruction whose guard evaluates to `false` falls through
  to the next instruction. -/
  | step_goto_fallthrough :
    pgm.instrAt pc = some instr →
    instr.type = .GOTO →
    δ_goto_bool σ instr.guard = some false →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.running (pc + 1) σ failed)

  /-- `END_FUNCTION` terminates execution. -/
  | step_end_function :
    pgm.instrAt pc = some instr →
    instr.type = .END_FUNCTION →
    StepGoto P δ_goto δ_goto_bool pgm
      (.running pc σ failed) (.terminal σ failed)

/-- Reflexive-transitive closure of `StepGoto`: an arbitrary number of
single GOTO steps. Mirrors the definition of `StepCFGStar`. -/
@[expose] def StepGotoStar
    (P : PureExpr) [HasBool P] [HasNot P]
    (δ_goto : SemanticEvalGoto P) (δ_goto_bool : SemanticEvalGotoBool P)
    (pgm : Program) : GotoConfig P → GotoConfig P → Prop :=
  ReflTrans (@StepGoto P _ _ δ_goto δ_goto_bool pgm)

/-! ## Well-formedness of the boolean GOTO evaluator

Mirrors `Imperative.WellFormedSemanticEvalBool`: the GOTO boolean evaluator
must agree with itself under negation, and the constant `Expr.true` must
evaluate to `true`. The latter is needed by the simulation proof when an
unconditional GOTO instruction (whose guard is literally `Expr.true`) must
be taken in the `condGoto` translation pattern. -/
def WellFormedSemanticEvalGotoBool {P : PureExpr} [HasBool P] [HasNot P]
    (δ_goto_bool : SemanticEvalGotoBool P) : Prop :=
  (∀ σ (e : Expr),
    (δ_goto_bool σ e = some true ↔ δ_goto_bool σ e.not = some false) ∧
    (δ_goto_bool σ e = some false ↔ δ_goto_bool σ e.not = some true)) ∧
  (∀ σ, δ_goto_bool σ Expr.true = some true)

end CProverGOTO
