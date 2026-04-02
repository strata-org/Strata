/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.StmtSemanticsSmallStep

---------------------------------------------------------------------

namespace Imperative

public section

/-! # Small-step semantics for non-deterministic statements

A configuration is either executing a `NondetStmt`, sequencing two parts
(left config + right continuation), or terminated.
-/

/-- Configurations for small-step execution of `NondetStmt`. -/
inductive NondetConfig (P : PureExpr) (CmdT : Type) : Type where
  /-- Executing a single nondeterministic statement. -/
  | stmt : NondetStmt P CmdT → Env P → NondetConfig P CmdT
  /-- Sequencing: execute the left config, then continue with the right stmt. -/
  | seq : NondetConfig P CmdT → NondetStmt P CmdT → NondetConfig P CmdT
  /-- Execution has finished. -/
  | terminal : Env P → NondetConfig P CmdT

/-! ## Configuration accessors -/

@[expose] def NondetConfig.getStore : NondetConfig P CmdT → SemanticStore P
  | .stmt _ ρ => ρ.store
  | .seq inner _ => inner.getStore
  | .terminal ρ => ρ.store

@[expose] def NondetConfig.getEval : NondetConfig P CmdT → SemanticEval P
  | .stmt _ ρ => ρ.eval
  | .seq inner _ => inner.getEval
  | .terminal ρ => ρ.eval

@[expose] def NondetConfig.getEnv : NondetConfig P CmdT → Env P
  | .stmt _ ρ => ρ
  | .seq inner _ => inner.getEnv
  | .terminal ρ => ρ

/-! ## Single-step relation -/

section

variable {CmdT : Type} (P : PureExpr) [HasBool P] [HasNot P]

inductive StepNondet
  (EvalCmd : EvalCmdParam P CmdT) :
  NondetConfig P CmdT → NondetConfig P CmdT → Prop where

  /-- A command steps to terminal. -/
  | step_cmd :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    ----
    StepNondet EvalCmd
      (.stmt (.cmd c) ρ)
      (.terminal { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure })

  /-- A seq statement enters a seq context. -/
  | step_seq :
    StepNondet EvalCmd
      (.stmt (.seq s1 s2) ρ)
      (.seq (.stmt s1 ρ) s2)

  /-- A choice nondeterministically picks the left branch. -/
  | step_choice_left :
    StepNondet EvalCmd
      (.stmt (.choice s1 s2) ρ)
      (.stmt s1 ρ)

  /-- A choice nondeterministically picks the right branch. -/
  | step_choice_right :
    StepNondet EvalCmd
      (.stmt (.choice s1 s2) ρ)
      (.stmt s2 ρ)

  /-- A loop can exit immediately (zero iterations). -/
  | step_loop_zero :
    StepNondet EvalCmd
      (.stmt (.loop s) ρ)
      (.terminal ρ)

  /-- A loop can execute one iteration then continue looping. -/
  | step_loop_step :
    StepNondet EvalCmd
      (.stmt (.loop s) ρ)
      (.seq (.stmt s ρ) (.loop s))

  /-- A seq context steps its inner config forward. -/
  | step_seq_inner :
    StepNondet EvalCmd inner inner' →
    ----
    StepNondet EvalCmd
      (.seq inner s2)
      (.seq inner' s2)

  /-- When the inner config of a seq reaches terminal, continue with the
      right statement. -/
  | step_seq_done :
    StepNondet EvalCmd
      (.seq (.terminal ρ') s2)
      (.stmt s2 ρ')

end

/-! ## Multi-step relation -/

abbrev StepNondetStar (P : PureExpr) [HasBool P] [HasNot P]
    (EvalCmd : EvalCmdParam P CmdT) :
    NondetConfig P CmdT → NondetConfig P CmdT → Prop :=
  ReflTrans (StepNondet P EvalCmd)

end -- public section
end Imperative
