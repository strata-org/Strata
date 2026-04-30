/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

/-!
# Exit Semantics: Per-Transition Named Lemmas

Thin wrappers over `StepStmt` constructors that give each exit-related
transition a descriptive name, so downstream proofs can cite the
transition by intent rather than by constructor tag.

See `docs/design/exit-semantics/spec.md` §4.1 and §4.2.
-/

namespace Imperative

section ExitProperties

variable {P : PureExpr} {CmdT : Type} {EvalCmd : EvalCmdParam P CmdT}
  {extendEval : ExtendEval P}
  [HasBool P] [HasNot P]

/-- An `exit` statement steps to `.exiting` carrying the same environment.
    Realizes spec §4.1 row 1. -/
public theorem exit_preserves_env (label : Option String) (md : MetaData P) (ρ : Env P) :
    StepStmt P EvalCmd extendEval
      (.stmt (.exit label md) ρ)
      (.exiting label ρ) :=
  .step_exit

/-- When a `seq` configuration's inner part has become `.exiting`,
    the remaining statements do not execute — the seq as a whole
    steps directly to `.exiting`.
    Realizes spec §4.1 row 2. -/
public theorem exit_skips_remaining (label : Option String) (ρ' : Env P)
    (ss : List (Stmt P CmdT)) :
    StepStmt P EvalCmd extendEval
      (.seq (.exiting label ρ') ss)
      (.exiting label ρ') :=
  .step_seq_exit

/-- A labeled block whose body has reached `.exiting (some L)`
    where `L` matches the block's label steps to `.terminal`,
    consuming the exit.
    Realizes spec §4.1 row 3. -/
public theorem matching_block_consumes (L : String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block (.some L) (.exiting (.some L) ρ'))
      (.terminal ρ') :=
  .step_block_exit_match rfl

/-- A labeled block whose body has reached `.exiting (some M)`
    where the block's label does not equal `some M`
    propagates the exit unchanged.
    Realizes spec §4.1 row 4. -/
public theorem nonmatching_exit_propagates
    (blockLabel : Option String) (M : String) (ρ' : Env P)
    (Hne : blockLabel ≠ .some M) :
    StepStmt P EvalCmd extendEval
      (.block blockLabel (.exiting (.some M) ρ'))
      (.exiting (.some M) ρ') :=
  .step_block_exit_mismatch Hne

/-- A block whose body has reached `.terminal`
    steps to `.terminal`.
    Realizes spec §4.1 row 5. -/
public theorem normal_block_completion (label : Option String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block label (.terminal ρ'))
      (.terminal ρ') :=
  .step_block_done

/-- A block whose body has reached `.exiting none`
    steps to `.terminal`. An unlabeled exit is consumed by any
    enclosing block regardless of the block's own label.
    Realizes spec §4.1 row 6. -/
public theorem unlabeled_exit_consumed (label : Option String) (ρ' : Env P) :
    StepStmt P EvalCmd extendEval
      (.block label (.exiting .none ρ'))
      (.terminal ρ') :=
  .step_block_exit_none

/-- A block context propagates inner steps.
    Realizes spec §4.1 row 7. -/
public theorem block_body_steps (label : Option String)
    (inner inner' : Config P CmdT)
    (H : StepStmt P EvalCmd extendEval inner inner') :
    StepStmt P EvalCmd extendEval
      (.block label inner)
      (.block label inner') :=
  .step_block_body H

/-! ### Multi-step companions

Reflexive-transitive closure variants used when composing with
downstream proofs that track `StepStmtStar` rather than single steps.
-/

/-- `.stmt (.exit label md) ρ  →*  .exiting label ρ` -/
public theorem exit_eval (label : Option String) (md : MetaData P) (ρ : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.stmt (.exit label md) ρ)
      (.exiting label ρ) :=
  .step _ _ _ .step_exit (.refl _)

/-- `.block (some L) (.exiting (some L) ρ')  →*  .terminal ρ'` -/
public theorem matching_block_eval (L : String) (ρ' : Env P) :
    StepStmtStar P EvalCmd extendEval
      (.block (.some L) (.exiting (.some L) ρ'))
      (.terminal ρ') :=
  .step _ _ _ (.step_block_exit_match rfl) (.refl _)

end ExitProperties

end Imperative
