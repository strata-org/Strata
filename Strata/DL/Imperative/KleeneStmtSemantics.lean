/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.KleeneStmt
public import Strata.DL.Imperative.StmtSemantics

---------------------------------------------------------------------

namespace Imperative

public section

/-! # Small-step semantics for non-deterministic statements

A configuration is either executing a `KleeneStmt`, sequencing two parts
(left config + right continuation), or terminated.
-/

/-- Configurations for small-step execution of `KleeneStmt`. -/
inductive KleeneConfig (P : PureExpr) (CmdT : Type) : Type where
  /-- Executing a single nondeterministic statement. -/
  | stmt : KleeneStmt P CmdT → Env P → KleeneConfig P CmdT
  /-- Sequencing: execute the left config, then continue with the right stmt. -/
  | seq : KleeneConfig P CmdT → KleeneStmt P CmdT → KleeneConfig P CmdT
  /-- Execution has finished. -/
  | terminal : Env P → KleeneConfig P CmdT

/-! ## Configuration accessors -/

@[expose] def KleeneConfig.getStore : KleeneConfig P CmdT → SemanticStore P
  | .stmt _ ρ => ρ.store
  | .seq inner _ => inner.getStore
  | .terminal ρ => ρ.store

@[expose] def KleeneConfig.getEval : KleeneConfig P CmdT → SemanticEval P
  | .stmt _ ρ => ρ.eval
  | .seq inner _ => inner.getEval
  | .terminal ρ => ρ.eval

@[expose] def KleeneConfig.getEnv : KleeneConfig P CmdT → Env P
  | .stmt _ ρ => ρ
  | .seq inner _ => inner.getEnv
  | .terminal ρ => ρ

/-! ## Single-step relation -/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]

/-- A single execution step for non-deterministic (Kleene) statements. -/
inductive StepKleene
  (EvalCmd : EvalCmdParam P CmdT) :
  KleeneConfig P CmdT → KleeneConfig P CmdT → Prop where

  /-- A command steps to terminal. -/
  | step_cmd :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    ----
    StepKleene EvalCmd
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure })

  /-- A seq statement enters a seq context. -/
  | step_seq :
    StepKleene EvalCmd
      (.stmt (.seq s1 s2) ρ)
      (.seq (.stmt s1 ρ) s2)

  /-- A choice nondeterministically picks the left branch. -/
  | step_choice_left :
    StepKleene EvalCmd
      (.stmt (.choice s1 s2) ρ)
      (.stmt s1 ρ)

  /-- A choice nondeterministically picks the right branch. -/
  | step_choice_right :
    StepKleene EvalCmd
      (.stmt (.choice s1 s2) ρ)
      (.stmt s2 ρ)

  /-- A loop can exit immediately (zero iterations). -/
  | step_loop_zero :
    StepKleene EvalCmd
      (.stmt (.loop s) ρ)
      (.terminal ρ)

  /-- A loop can execute one iteration then continue looping. -/
  | step_loop_step :
    StepKleene EvalCmd
      (.stmt (.loop s) ρ)
      (.seq (.stmt s ρ) (.loop s))

  /-- A seq context steps its inner config forward. -/
  | step_seq_inner :
    StepKleene EvalCmd inner inner' →
    ----
    StepKleene EvalCmd
      (.seq inner s2)
      (.seq inner' s2)

  /-- When the inner config of a seq reaches terminal, continue with the
      right statement. -/
  | step_seq_done :
    StepKleene EvalCmd
      (.seq (.terminal ρ') s2)
      (.stmt s2 ρ')

end

/-! ## Multi-step relation -/

/-- Multi-step execution for non-deterministic statements: the reflexive,
transitive closure of `StepKleene`. -/
abbrev StepKleeneStar (P : PureExpr) [HasBool P] [HasNot P]
    (EvalCmd : EvalCmdParam P CmdT) :
    KleeneConfig P CmdT → KleeneConfig P CmdT → Prop :=
  ReflTrans (StepKleene P EvalCmd)

end -- public section
end Imperative
