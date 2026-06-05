/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.DL.Imperative.StmtSemantics

public section

---------------------------------------------------------------------

namespace Imperative

/-! ## Small-Step operational semantics for control-flow graphs

This module defines small-step operational semantics for the Imperative
dialect's control-flow graph representation.
-/

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of a store and a failure indication flag paired
with either:

- The next block to execute
- An indication that the program that has finished executing
-/
inductive CFGConfig (l : Type) (P : PureExpr): Type where
  /-- The label to execute next. -/
  | cont : l → SemanticStore P → Bool → CFGConfig l P
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : SemanticStore P → Bool → CFGConfig l P

/-- Monotonically update the `failure` flag in a `CFGConfig`. It will be set to
`true` if the provided Boolean is `true`. -/
def updateFailure : CFGConfig l P → Bool → CFGConfig l P
| .cont t σ failed, failed' => .cont t σ (failed || failed')
| .terminal σ failed, failed' => .terminal σ (failed || failed')

/-- Small-step operational semantics for deterministic basic blocks. Evaluates
commands sequentially, then transfers control based on the block's terminator.

This is a single recursive inductive that combines command evaluation with
transfer semantics. The `cmd` constructor evaluates one command and recurses
on the remaining commands. The terminal constructors handle the transfer once
all commands are exhausted.

Structuring it this way (rather than delegating to a separate `EvalCmds`
inductive) ensures that `EvalCmd` is referenced directly in a constructor,
which is required for Lean 4's kernel to accept this type as a nested
inductive in mutual blocks. -/
inductive EvalDetBlock
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [HasNot P] :
  SemanticStore P → DetBlock l CmdT P → CFGConfig l P → Prop where

  | cmd :
    EvalCmd δ σ c σ' failed →
    EvalDetBlock P EvalCmd extendEval σ' ⟨cs, transfer⟩ config →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ c :: cs, transfer ⟩ (updateFailure config failed)

  | goto_true :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ [], .condGoto c t e _ ⟩ (.cont t σ false)

  | goto_false :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ [], .condGoto c t e _ ⟩ (.cont e σ false)

  | terminal :
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ [], .finish _ ⟩ (.terminal σ false)

/--
Small-step operational semantics for non-deterministic basic blocks. Evaluates
commands sequentially, then transfers control nondeterministically.
-/
inductive EvalNondetBlock
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [HasNot P] :
  SemanticStore P → NondetBlock l CmdT P → CFGConfig l P → Prop where

  | cmd :
    EvalCmd δ σ c σ' failed →
    EvalNondetBlock P EvalCmd extendEval σ' ⟨cs, transfer⟩ config →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ c :: cs, transfer ⟩ (updateFailure config failed)

  | goto_none :
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ [], .goto [] _ ⟩ (.terminal σ false)

  | goto_some :
    lt ∈ ls →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ [], .goto ls _ ⟩ (.cont lt σ false)

/--
Operational semantics to step between two configurations of a control-flow
graph, evaluating a single block using the provided relation.
-/
inductive StepCFG
  {Blk l CmdT : Type}
  [BEq l]
  (P : PureExpr)
  (EvalBlock : SemanticStore P → Blk → CFGConfig l P → Prop) :
  CFG l Blk → CFGConfig l P → CFGConfig l P → Prop where
  | eval_next :
    List.lookup t cfg.blocks = .some b →
    EvalBlock σ b config →
    StepCFG P EvalBlock cfg (.cont t σ failed) (updateFailure config failed)

/--
Operational semantics to evaluate an arbitrary number of blocks in a
control-flow graph in sequence. The reflexive, transitive closure of `StepCFG`.
-/
def StepCFGStar
  {Blk l CmdT : Type}
  [BEq l]
  (P : PureExpr)
  (EvalBlock : SemanticStore P → Blk → CFGConfig l P → Prop)
  (cfg : CFG l Blk) :
  CFGConfig l P → CFGConfig l P → Prop :=
  ReflTrans (@StepCFG Blk l CmdT _ P EvalBlock cfg)
