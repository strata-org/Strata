/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.Stmt
import Strata.Util.Tactics

---------------------------------------------------------------------

namespace Imperative

public section

/-- Type of a function that extends the semantic evaluator with a new function definition. -/
@[expose] abbrev ExtendEval (P : PureExpr) := SemanticEval P → SemanticStore P → PureFunc P → SemanticEval P

mutual

/--
An inductively-defined operational semantics that depends on
environment lookup and evaluation functions for expressions.

Note that `EvalStmt` is parameterized by commands `Cmd` as well as their
evaluation relation `EvalCmd`, and by `extendEval` which specifies how
`funcDecl` statements extend the evaluator.

The expression evaluator `δ` is threaded as state to support `funcDecl`,
which extends the evaluator with new function definitions. Commands do not
modify the evaluator, only `funcDecl` statements do.
-/
inductive EvalStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → Stmt P Cmd → SemanticStore P → SemanticEval P → Prop where
  | cmd_sem :
    EvalCmd δ σ c σ' →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    -- For example, if we require definedness on a block, then we won't be able to evaluate
    -- a block containing init x; havoc x, because it will require x to exist prior to the block
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (Stmt.cmd c) σ' δ

  | block_sem :
    EvalBlock P Cmd EvalCmd extendEval δ σ b σ' δ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.block _ b md) σ' δ'

  | ite_true_sem :
    δ σ c = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ t σ' δ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e md) σ' δ'

  | ite_false_sem :
    δ σ c = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ e σ' δ' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.ite c t e md) σ' δ'

  | funcDecl_sem [HasSubstFvar P] [HasVarsPure P P.Expr] :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.funcDecl decl md) σ
      (extendEval δ σ decl)

  | typeDecl_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ (.typeDecl tc md) σ δ

  -- (TODO): Define semantics of `exit`.

  /-- Loop: guard is false, skip. Measure and invariants are specification-only. -/
  | loop_false_sem :
    δ σ g = .some HasBool.ff →
    WellFormedSemanticEvalBool δ →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.loop g meas invs body md) σ δ

  /-- Loop: guard is true, execute body, then loop again. -/
  | loop_true_sem :
    δ σ g = .some HasBool.tt →
    WellFormedSemanticEvalBool δ →
    EvalBlock P Cmd EvalCmd extendEval δ σ body σ' δ' →
    EvalStmt P Cmd EvalCmd extendEval δ' σ' (.loop g meas invs body md) σ'' δ'' →
    ----
    EvalStmt P Cmd EvalCmd extendEval δ σ (.loop g meas invs body md) σ'' δ''

inductive EvalBlock (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  (extendEval : ExtendEval P)
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
    SemanticEval P → SemanticStore P → List (Stmt P Cmd) → SemanticStore P → SemanticEval P → Prop where
  | stmts_none_sem :
    EvalBlock P _ _ _ δ σ [] σ δ
  | stmts_some_sem :
    EvalStmt P Cmd EvalCmd extendEval δ σ s σ' δ' →
    EvalBlock P Cmd EvalCmd extendEval δ' σ' ss σ'' δ'' →
    EvalBlock P Cmd EvalCmd extendEval δ σ (s :: ss) σ'' δ''

end

theorem eval_stmts_singleton
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ [cmd] σ' δ' ↔
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ cmd σ' δ' := by
  constructor <;> intro Heval
  · cases Heval with | stmts_some_sem Heval Hempty =>
      cases Hempty; exact Heval
  · exact EvalBlock.stmts_some_sem Heval EvalBlock.stmts_none_sem

theorem eval_stmts_concat
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ cmds1 σ' δ' →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ' σ' cmds2 σ'' δ'' →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ (cmds1 ++ cmds2) σ'' δ'' := by
  intro Heval1 Heval2
  induction cmds1 generalizing cmds2 σ δ
  · simp only [List.nil_append]
    cases Heval1; exact Heval2
  · rename_i cmd cmds ind
    cases Heval1
    apply EvalBlock.stmts_some_sem (by assumption)
    apply ind (by assumption) (by assumption)

theorem EvalCmdDefMonotone [HasFvar P] [HasBool P] [HasNot P] :
  isDefined σ v →
  EvalCmd P δ σ c σ' →
  isDefined σ' v := by
  intros Hdef Heval
  cases Heval <;> try exact Hdef
  next _ Hup => exact InitStateDefMonotone Hdef Hup  -- eval_init
  next Hup => exact InitStateDefMonotone Hdef Hup    -- eval_init_unconstrained
  next _ Hup => exact UpdateStateDefMonotone Hdef Hup
  next Hup => exact UpdateStateDefMonotone Hdef Hup

theorem EvalBlockEmpty {P : PureExpr} {Cmd : Type} {EvalCmd : EvalCmdParam P Cmd}
  {extendEval : ExtendEval P}
  { σ σ': SemanticStore P } { δ δ' : SemanticEval P }
  [DecidableEq P.Ident]
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasVal P] [HasBool P] [HasNot P] :
  EvalBlock P Cmd EvalCmd extendEval δ σ ([]: (List (Stmt P Cmd))) σ' δ' → σ = σ' ∧ δ = δ' := by
  intros H; cases H <;> simp

mutual
theorem EvalStmtDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  [HasSubstFvar P] [HasVarsPure P P.Expr]
  :
  isDefined σ v →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ s σ' δ' →
  isDefined σ' v := by
  intros Hdef Heval
  match Heval with
  | .cmd_sem Hcmd _ => exact EvalCmdDefMonotone Hdef Hcmd
  | .block_sem Hblock => exact EvalBlockDefMonotone Hdef Hblock
  | .ite_true_sem _ _ Hblock => exact EvalBlockDefMonotone Hdef Hblock
  | .ite_false_sem _ _ Hblock => exact EvalBlockDefMonotone Hdef Hblock
  | .funcDecl_sem => exact Hdef
  | .typeDecl_sem => exact Hdef
  | .loop_false_sem _ _ => exact Hdef
  | .loop_true_sem _ _ Hbody Hloop =>
    exact EvalStmtDefMonotone (EvalBlockDefMonotone Hdef Hbody) Hloop

theorem EvalBlockDefMonotone
  [DecidableEq P.Ident]
  [HasVal P] [HasFvar P] [HasBool P] [HasBoolVal P] [HasNot P]
  [HasSubstFvar P] [HasVarsPure P P.Expr]
  :
  isDefined σ v →
  EvalBlock P (Cmd P) (EvalCmd P) extendEval δ σ ss σ' δ' →
  isDefined σ' v := by
  intros Hdef Heval
  match Heval with
  | .stmts_none_sem => exact Hdef
  | .stmts_some_sem Heval1 Heval2 =>
    exact EvalBlockDefMonotone (EvalStmtDefMonotone Hdef Heval1) Heval2
end

end -- public section
