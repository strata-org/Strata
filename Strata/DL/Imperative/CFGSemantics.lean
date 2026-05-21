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

inductive EvalCmds
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT) :
  SemanticEval P → SemanticStore P → List CmdT → SemanticStore P → Bool → Prop where
  | eval_cmds_none :
    EvalCmds P EvalCmd δ σ [] σ false
  | eval_cmds_some :
    EvalCmd δ σ c σ' failed →
    EvalCmds P EvalCmd δ σ' cs σ'' failed' →
    EvalCmds P EvalCmd δ σ (c :: cs) σ'' (failed || failed')

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

/-- Small-step operational semantics for deterministic basic blocks. Each case
first evaluates the commands in the block. A block ending in `.condGoto` results
in a configuration pointing to the true or false label, depending on the
evaluation of the condition. A block ending in `.finish` results in a terminal
configuration. -/
inductive EvalDetBlock
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [HasNot P] :
  SemanticStore P → DetBlock l CmdT P → CFGConfig l P → Prop where

  | step_goto_true :
    EvalCmds P EvalCmd δ σ cs σ' failed →
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .condGoto c t e _ ⟩ (.cont t σ' failed)

  | step_goto_false :
    EvalCmds P EvalCmd δ σ cs σ' failed →
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .condGoto c t e _ ⟩ (.cont e σ' failed)

  | step_terminal :
    EvalCmds P EvalCmd δ σ cs σ' failed →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .finish _ ⟩ (.terminal σ' failed)

/--
Small-step operational semantics for non-deterministic basic blocks. Each case
first evaluates the commands in the block. A block ending in `.goto` with no
labels results in a terminal configuration. A block ending in `.goto` with a
non-empty list of labels results in a configuration pointing to a
non-deterministic choice of one of the labels.
-/
inductive EvalNondetBlock
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [HasNot P] :
  SemanticStore P → NondetBlock l CmdT P → CFGConfig l P → Prop where

  | step_goto_none :
    EvalCmds P EvalCmd δ σ cs σ' failed →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ cs, .goto [] _ ⟩ (.terminal σ' failed)

  | step_goto_some :
    EvalCmds P EvalCmd δ σ cs σ' failed →
    lt ∈ ls →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ cs, .goto ls _ ⟩ (.cont lt σ' failed)

/--
Monotonically update the `failure` flag in a `CFGConfig`. It will be set to
`true` if the provided Boolean is `true`.
-/
def updateFailure : CFGConfig l P → Bool → CFGConfig l P
| .cont t σ failed, failed' => .cont t σ (failed || failed')
| .terminal σ failed, failed' => .terminal σ (failed || failed')

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
