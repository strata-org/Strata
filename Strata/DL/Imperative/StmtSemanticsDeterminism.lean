/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.StmtSemantics
import all Strata.DL.Imperative.Cmd
import all Strata.Util.Relations

namespace Imperative

public section

/-! # Syntactic determinism of the reference small-step semantics

This module is self-contained metatheory of `StepStmtE` — the
reference small-step semantics over `Config P (Cmd P)`.  It involves no
interpreter, no monad, and no fuel.

There are exactly four syntactic sources of nondeterminism in the reference
semantics, all of them a `.nondet` in the program text:

* an `.ite` whose guard is `.nondet` (rules `StepStmtE.step_ite_nondet_true`
  and `StepStmtE.step_ite_nondet_false`);
* a `.loop` whose guard is `.nondet` (rules `StepStmtE.step_loop_nondet_enter`
  and `StepStmtE.step_loop_nondet_exit`);
* an `.init` whose right-hand side is `.nondet` (rule
  `EvalCmdE.eval_init_unconstrained`);
* a `.set` whose right-hand side is `.nondet` (rule `EvalCmdE.eval_set_nondet`).

`StmtDeterministic` rules out all four, recursively, and `Config.deterministic`
lifts it to a whole configuration.  `StepDetE` is the sub-relation of `StepStmtE`
made of the *deterministic* rules.  Lemmas about these definitions are in
`StmtSemanticsDeterminismProps.lean`: the semantics preserves `Config.deterministic`
(`StepStmtE.preserves_deterministic`), and every step out of a deterministic
configuration is a `StepDetE` step (`StepStmtE.toStepDetE`).

Downstream this is the bridge that lets a monad-generic completeness result be
instantiated at monads whose `choose` refuses nondeterminism: on a
deterministic program the choice-resolution obligation is vacuous, because a
`StepDetE` derivation never consults a choice.
-/

variable {P : PureExpr}

/-! ## The syntactic determinism predicate -/

/-- A right-hand side / guard is deterministic when it is `.det`, not `.nondet`. -/
@[expose] def ExprOrNondet.isDet : ExprOrNondet P → Bool
  | .det _ => true
  | .nondet => false

/-- A base command is deterministic when it has no `.nondet` `init`/`set`
right-hand side.  `assert`, `assume` and `cover` are store-neutral event
emitters and are always deterministic. -/
@[expose] def CmdDeterministic : Cmd P → Bool
  | .init _ _ e _ => ExprOrNondet.isDet e
  | .set _ e _ => ExprOrNondet.isDet e
  | .assert _ _ _ => true
  | .assume _ _ _ => true
  | .cover _ _ _ => true

mutual
/-- No nondeterministic rule of the reference semantics is reachable from `s`:
its base commands are deterministic, and no `.ite`/`.loop` guard anywhere
inside it is `.nondet`. -/
@[expose] def StmtDeterministic {P : PureExpr} (s : Stmt P (Cmd P)) : Bool :=
  match s with
  | .cmd c => CmdDeterministic c
  | .block _ b _ => StmtsDeterministic b
  | .ite cond t e _ =>
      ExprOrNondet.isDet cond && StmtsDeterministic t && StmtsDeterministic e
  | .loop g _ _ body _ => ExprOrNondet.isDet g && StmtsDeterministic body
  | .exit _ _ => true
  | .typeDecl _ _ => true

/-- `StmtDeterministic` for every statement of a list. -/
@[expose] def StmtsDeterministic {P : PureExpr} (ss : List (Stmt P (Cmd P))) : Bool :=
  match ss with
  | [] => true
  | s :: rest => StmtDeterministic s && StmtsDeterministic rest
end

/-- `StmtDeterministic` lifted to a configuration: every statement still to be
executed — in the active position, in the pending tail of every enclosing
`.seq`, and inside every enclosing `.block` — is deterministic.  Terminal and
exiting configurations have no statements left, hence are deterministic. -/
@[expose] def Config.deterministic : Config P (Cmd P) → Bool
  | .stmt s _ => StmtDeterministic s
  | .stmts ss _ => StmtsDeterministic ss
  | .terminal _ => true
  | .exiting _ _ => true
  | .block _ _ inner => Config.deterministic inner
  | .seq inner ss => Config.deterministic inner && StmtsDeterministic ss

/-! ## `StepDetE`, the deterministic-rules-only semantics

`StepDetE` has exactly the rules of `StepStmtE` that resolve no choice. -/

section

variable (P : PureExpr) [HasBool P] [HasBoolOps P]

/-- The sub-relation of `StepStmtE` consisting of the rules that resolve no
nondeterministic choice. -/
inductive StepDetE
    {EventT : Type _}
    (EvalCmd : EvalCmdParamE P (Cmd P) EventT) :
    Config P (Cmd P) → List EventT → Config P (Cmd P) → Prop where
  /-- Execute one deterministic base command. -/
  | step_cmd :
      CmdDeterministic cmd = true →
      EvalCmd ρ.factory ρ.store cmd σ' emitted →
      StepDetE EvalCmd
        (.stmt (.cmd cmd) ρ) emitted
        (.terminal { ρ with store := σ' })

  /-- Enter a labeled block. -/
  | step_block :
      StepDetE EvalCmd
        (.stmt (.block label ss md) ρ) []
        (.block (.some label) ρ.store (.stmts ss ρ))

  /-- Take the then-branch of an `ite` whose guard evaluates to true. -/
  | step_ite_true :
      P.eval ρ.factory ρ.store c = .some (HasBool.ttVal ρ.factory) →
      StepDetE EvalCmd
        (.stmt (.ite (.det c) tss ess md) ρ) []
        (.block .none ρ.store (.stmts tss ρ))

  /-- Take the else-branch of an `ite` whose guard evaluates to false. -/
  | step_ite_false :
      P.eval ρ.factory ρ.store c = .some (HasBool.ffVal ρ.factory) →
      StepDetE EvalCmd
        (.stmt (.ite (.det c) tss ess md) ρ) []
        (.block .none ρ.store (.stmts ess ρ))

  /-- Enter a loop body whose guard evaluates to true. -/
  | step_loop_enter :
      P.eval ρ.factory ρ.store g = .some (HasBool.ttVal ρ.factory) →
      StepDetE EvalCmd
        (.stmt (.loop (.det g) m inv body md) ρ) []
        (.seq
          (.block .none ρ.store (.stmts body ρ))
          [.loop (.det g) m inv body md])

  /-- Exit a loop whose guard evaluates to false. -/
  | step_loop_exit :
      P.eval ρ.factory ρ.store g = .some (HasBool.ffVal ρ.factory) →
      StepDetE EvalCmd
        (.stmt (.loop (.det g) m inv body md) ρ) [] (.terminal ρ)

  /-- An exit statement produces an exiting configuration. -/
  | step_exit :
      StepDetE EvalCmd
        (.stmt (.exit label md) ρ) [] (.exiting label ρ)

  /-- A type declaration is a runtime no-op. -/
  | step_typeDecl :
      StepDetE EvalCmd
        (.stmt (.typeDecl tc md) ρ) [] (.terminal ρ)

  /-- The empty statement list is terminal. -/
  | step_stmts_nil :
      StepDetE EvalCmd (.stmts [] ρ) [] (.terminal ρ)

  /-- Enter a sequence context on a non-empty statement list. -/
  | step_stmts_cons :
      StepDetE EvalCmd
        (.stmts (s :: ss) ρ) [] (.seq (.stmt s ρ) ss)

  /-- Lift one inner sequence step. -/
  | step_seq_inner :
      StepDetE EvalCmd inner emitted inner' →
      StepDetE EvalCmd (.seq inner ss) emitted (.seq inner' ss)

  /-- Continue with the pending statements once the sequence head terminates. -/
  | step_seq_done :
      StepDetE EvalCmd
        (.seq (.terminal ρ') ss) [] (.stmts ss ρ')

  /-- Propagate an exit out of a sequence, skipping the pending statements. -/
  | step_seq_exit :
      StepDetE EvalCmd
        (.seq (.exiting label ρ') ss) [] (.exiting label ρ')

  /-- Lift one inner block step. -/
  | step_block_body :
      StepDetE EvalCmd inner emitted inner' →
      StepDetE EvalCmd
        (.block label σ_parent inner) emitted
        (.block label σ_parent inner')

  /-- Leave a block whose body terminated, projecting the store. -/
  | step_block_done :
      StepDetE EvalCmd
        (.block label σ_parent (.terminal ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- A block consumes an exit carrying its own label. -/
  | step_block_exit_match :
      label = .some l →
      StepDetE EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.terminal { ρ' with store := projectStore σ_parent ρ'.store })

  /-- A block propagates an exit carrying a different label. -/
  | step_block_exit_mismatch :
      label ≠ .some l →
      StepDetE EvalCmd
        (.block label σ_parent (.exiting l ρ')) []
        (.exiting l { ρ' with store := projectStore σ_parent ρ'.store })

/-- Traced reflexive-transitive closure of `StepDetE`. -/
abbrev StepDetStarE
    {EventT : Type _}
    (EvalCmd : EvalCmdParamE P (Cmd P) EventT) :
    Config P (Cmd P) → List EventT → Config P (Cmd P) → Prop :=
  ReflTransTrace (StepDetE P EvalCmd)

variable {P}

end

end -- public section

end Imperative
