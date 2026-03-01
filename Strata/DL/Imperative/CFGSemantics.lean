/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.DL.Imperative.BasicBlock
import Strata.DL.Imperative.Cmd
import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.StmtSemantics
import Strata.DL.Util.Relations

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
  SemanticEval P → SemanticStore P → List CmdT → SemanticStore P → Prop where
  | eval_cmds_none :
    EvalCmds P EvalCmd δ σ [] σ
  | eval_cmds_some :
    EvalCmd δ σ c σ' →
    EvalCmds P EvalCmd δ σ' cs σ'' →
    EvalCmds P EvalCmd δ σ (c :: cs) σ''

/--
Configuration for small-step semantics, representing the current execution
state. A configuration consists of either:
- The next block to execute
- An indication that the program that has finished executing
-/
inductive Config (l : Type) (P : PureExpr): Type where
  /-- The label to execute next. -/
  | cont : l → SemanticStore P → Config l P
  /-- A terminal configuration, indicating that execution has finished. -/
  | terminal : SemanticStore P → Config l P

/--
Small-step operational semantics for deterministic basic blocks. Each case first
evaluates the commands in the block. A block ending in `.cgoto` results in a
configuration pointing to the true or false label, depending on the evaluation
of the condition. A block ending in `.finish` results in a terminal
configuration.
-/
inductive EvalDetBlock
  {CmdT : Type}
  (P : PureExpr)
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  [HasNot P] :
  SemanticStore P → DetBlock l CmdT P → Config l P → Prop where

  | step_goto_true :
    EvalCmds P EvalCmd δ σ cs σ' →
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .cgoto c t e _ ⟩ (.cont t σ')

  | step_goto_false :
    EvalCmds P EvalCmd δ σ cs σ' →
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .cgoto c t e _ ⟩ (.cont e σ')

  | step_terminal :
    EvalCmds P EvalCmd δ σ cs σ' →
    EvalDetBlock P EvalCmd extendEval
      σ ⟨ cs, .finish _ ⟩ (.terminal σ')

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
  SemanticStore P → NondetBlock l CmdT P → Config l P → Prop where

  | step_goto_none :
    EvalCmds P EvalCmd δ σ cs σ' →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ cs, .goto [] _ ⟩ (.terminal σ')

  | step_goto_some :
    EvalCmds P EvalCmd δ σ cs σ' →
    lt ∈ ls →
    EvalNondetBlock P EvalCmd extendEval
      σ ⟨ cs, .goto ls _ ⟩ (.cont lt σ')

/--
Operational semantics to step between two configurations of a control-flow
graph, evaluating a single block using the provided relation.
-/
inductive StepCFG
  {Blk l CmdT : Type}
  [BEq l]
  (P : PureExpr)
  (EvalBlock : SemanticStore P → Blk → Config l P → Prop) :
  CFG l Blk → Config l P → Config l P → Prop where
  | eval_next :
    List.lookup t cfg.blocks = .some b →
    EvalBlock σ b config →
    StepCFG P EvalBlock cfg (.cont t σ) config

/--
Operational semantics to evaluate an arbitrary number of blocks in a
control-flow graph in sequence. The reflexive, transitive closure of `StepCFG`.
-/
def StepCFGStar
  {Blk l CmdT : Type}
  [BEq l]
  (P : PureExpr)
  (EvalBlock : SemanticStore P → Blk → Config l P → Prop)
  (cfg : CFG l Blk) :
  Config l P → Config l P → Prop :=
  ReflTrans (@StepCFG Blk l CmdT _ P EvalBlock cfg)
