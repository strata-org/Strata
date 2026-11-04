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

universe u

/-! # Small-step semantics for non-deterministic statements

A configuration is either executing a `KleeneStmt`, sequencing two parts
(left config + right continuation), a block context, or terminated.
-/

/-- Configurations for small-step execution of `KleeneStmt`. -/
inductive KleeneConfig (P : PureExpr.{u}) (CmdT : Type) : Type u where
  /-- Executing a single nondeterministic statement. -/
  | stmt : KleeneStmt P CmdT → Env P → KleeneConfig P CmdT
  /-- Sequencing: execute the left config, then continue with the right stmt. -/
  | seq : KleeneConfig P CmdT → KleeneStmt P CmdT → KleeneConfig P CmdT
  /-- Execution has finished. -/
  | terminal : Env P → KleeneConfig P CmdT
  /-- A block context for scoping. The `SemanticStore P` is the parent store;
      on exit, variables init'd inside are projected away. -/
  | block : SemanticStore P → KleeneConfig P CmdT → KleeneConfig P CmdT

/-! ## Configuration accessors -/

@[expose] def KleeneConfig.getStore : KleeneConfig P CmdT → SemanticStore P
  | .stmt _ ρ => ρ.store
  | .seq inner _ => inner.getStore
  | .terminal ρ => ρ.store
  | .block _ inner => inner.getStore

@[expose] def KleeneConfig.getEnv : KleeneConfig P CmdT → Env P
  | .stmt _ ρ => ρ
  | .seq inner _ => inner.getEnv
  | .terminal ρ => ρ
  | .block _ inner => inner.getEnv

/-! ## Single-step relation -/

section

variable {CmdT : Type} {EventT : Type _} (P : PureExpr) [HasBool P] [HasBoolOps P]

/-- A single event-trace execution step for non-deterministic (Kleene) statements. -/
inductive StepKleeneE
  (EvalCmd : EvalCmdParamE P CmdT EventT) :
  KleeneConfig P CmdT → List EventT → KleeneConfig P CmdT → Prop where

  /-- A command steps to terminal, emitting its events. -/
  | step_cmd :
    EvalCmd ρ.factory ρ.store c σ' emitted →
    ----
    StepKleeneE EvalCmd
      (.stmt (.cmd c) ρ) emitted
      (.terminal { ρ with store := σ' })

  /-- A seq statement enters a seq context. -/
  | step_seq :
    StepKleeneE EvalCmd
      (.stmt (.seq s1 s2) ρ) []
      (.seq (.stmt s1 ρ) s2)

  /-- A choice nondeterministically picks the left branch. -/
  | step_choice_left :
    StepKleeneE EvalCmd
      (.stmt (.choice s1 s2) ρ) []
      (.stmt s1 ρ)

  /-- A choice nondeterministically picks the right branch. -/
  | step_choice_right :
    StepKleeneE EvalCmd
      (.stmt (.choice s1 s2) ρ) []
      (.stmt s2 ρ)

  /-- A loop can exit immediately (zero iterations). -/
  | step_loop_zero :
    StepKleeneE EvalCmd
      (.stmt (.loop s) ρ) []
      (.terminal ρ)

  /-- A loop can execute one iteration then continue looping. -/
  | step_loop_step :
    StepKleeneE EvalCmd
      (.stmt (.loop s) ρ) []
      (.seq (.block ρ.store (.stmt s ρ)) (.loop s))

  /-- A block statement enters a block context, saving the parent store. -/
  | step_block :
    StepKleeneE EvalCmd
      (.stmt (.block s) ρ) []
      (.block ρ.store (.stmt s ρ))

  /-- A seq context steps its inner config forward, propagating its events. -/
  | step_seq_inner :
    StepKleeneE EvalCmd inner emitted inner' →
    ----
    StepKleeneE EvalCmd
      (.seq inner s2) emitted
      (.seq inner' s2)

  /-- When a seq's inner config reaches terminal, continue with the right statement. -/
  | step_seq_done :
    StepKleeneE EvalCmd
      (.seq (.terminal ρ') s2) []
      (.stmt s2 ρ')

  /-- A block context steps its inner config forward, propagating its events. -/
  | step_block_body :
    StepKleeneE EvalCmd inner emitted inner' →
    ----
    StepKleeneE EvalCmd
      (.block σ_parent inner) emitted
      (.block σ_parent inner')

  /-- When a block's inner config reaches terminal, project the store. -/
  | step_block_done :
    StepKleeneE EvalCmd
      (.block σ_parent (.terminal ρ')) []
      (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

end

/-- Event-trace multi-step execution for non-deterministic statements: the
reflexive, transitive closure of `StepKleeneE`, concatenating each step's
event list chronologically. -/
abbrev StepKleeneStarE (P : PureExpr) [HasBool P] [HasBoolOps P]
    (EvalCmd : EvalCmdParamE P CmdT EventT) :
    KleeneConfig P CmdT → List EventT → KleeneConfig P CmdT → Prop :=
  ReflTransTrace (StepKleeneE P EvalCmd)

end -- public section
end Imperative
