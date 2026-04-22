/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.StmtSemantics

namespace Imperative

public section

def runStep [BEq P.Expr] [HasBool P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  (c: Config P CmdT) : Config P CmdT :=
  match c with
  | .terminal _ => c
  | .exiting _ _ => c

  -- step_cmd: cannot execute relational EvalCmd; leave unchanged
  | .stmt (.cmd _) _ => c

  -- step_block
  | .stmt (.block label ss _) ρ => .block label (.stmts ss ρ)

  -- step_ite_true / step_ite_false / step_ite_nondet (default to true)
  | .stmt (.ite cond tss ess _) ρ =>
    match cond with
    | .nondet => .stmts tss ρ
    | .det e =>
      match ρ.eval ρ.store e with
      | some v =>
        if v == HasBool.tt then .stmts tss ρ
        else .stmts ess ρ
      | none => c  -- stuck: guard didn't evaluate

  -- step_loop_enter / step_loop_exit / step_loop_nondet (default to exit)
  | .stmt s@(.loop guard measure inv body md) ρ =>
    match guard with
    | .nondet => .terminal ρ
    | .det g =>
      match ρ.eval ρ.store g with
      | some v =>
        if v == HasBool.tt then .stmts (body ++ [s]) ρ
        else .terminal ρ
      | none => c  -- stuck: guard didn't evaluate

  -- step_exit
  | .stmt (.exit label _) ρ => .exiting label ρ

  -- step_funcDecl
  | .stmt (.funcDecl decl _) ρ =>
    .terminal { ρ with eval := extendEval ρ.eval ρ.store decl }

  -- step_typeDecl
  | .stmt (.typeDecl _ _) ρ => .terminal ρ

  -- step_stmts_nil
  | .stmts [] ρ => .terminal ρ

  -- step_stmts_cons
  | .stmts (s :: ss) ρ => .seq (.stmt s ρ) ss

  -- step_seq: step inner, or handle terminal/exiting
  | .seq inner ss =>
    match inner with
    | .terminal ρ' => .stmts ss ρ'          -- step_seq_done
    | .exiting label ρ' => .exiting label ρ' -- step_seq_exit
    | _ => .seq (runStep EvalCmd extendEval inner) ss  -- step_seq_inner

  -- step_block_body / step_block_done / step_block_exit_*
  | .block label inner =>
    match inner with
    | .terminal ρ' => .terminal ρ'           -- step_block_done
    | .exiting .none ρ' => .terminal ρ'      -- step_block_exit_none
    | .exiting (.some l) ρ' =>
      if l == label then .terminal ρ'        -- step_block_exit_match
      else .exiting (.some l) ρ'             -- step_block_exit_mismatch
    | _ => .block label (runStep EvalCmd extendEval inner)  -- step_block_body

def runStepStar [BEq P.Expr] [HasBool P]
  (EvalCmd : EvalCmdParam P CmdT)
  (extendEval : ExtendEval P)
  (fuel: Nat)
  (c: Config P CmdT) : Config P CmdT :=
  match c with
  | .terminal _ => c
  | _ =>
    match fuel with
    | 0 => c
    | fuel + 1 => runStepStar EvalCmd extendEval fuel (runStep EvalCmd extendEval c)
