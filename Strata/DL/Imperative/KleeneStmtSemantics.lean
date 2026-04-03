/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.KleeneStmt
public import Strata.DL.Imperative.Stmt

---------------------------------------------------------------------

namespace Imperative

public section

mutual

/-- An inductively-defined operational semantics for Kleene
statements that depends on environment lookup and evaluation functions for
expressions.  **NOTE:** This will probably be replaced with a small-step
semantics.
Note: Kleene statements don't track evaluator changes since
commands preserve the evaluator (only funcDecl statements modify it). -/
inductive EvalKleeneStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasBool P] [HasNot P] :
  SemanticEval P → SemanticStore P → KleeneStmt P Cmd → SemanticStore P → Prop where
  | cmd_sem :
    EvalCmd δ σ c σ' →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalKleeneStmt P Cmd EvalCmd δ σ (KleeneStmt.cmd c) σ'

  | seq_sem :
    EvalKleeneStmt P Cmd EvalCmd δ σ s1 σ' →
    EvalKleeneStmt P Cmd EvalCmd δ σ' s2 σ'' →
    ----
    EvalKleeneStmt P Cmd EvalCmd δ σ (.seq s1 s2) σ''

  | choice_left_sem :
    WellFormedSemanticEvalBool δ →
    EvalKleeneStmt P Cmd EvalCmd δ σ s1 σ' →
    ----
    EvalKleeneStmt P Cmd EvalCmd δ σ (.choice s1 s2) σ'

  | choice_right_sem :
    WellFormedSemanticEvalBool δ →
    EvalKleeneStmt P Cmd EvalCmd δ σ s2 σ' →
    ----
    EvalKleeneStmt P Cmd EvalCmd δ σ (.choice s1 s2) σ'

  /-
  | loop_sem :
    EvalKleeneStmt P δ σ₀ σ s σ' →
    EvalKleeneStmt P δ σ₀ σ' (.loop s) σ'' →
    ----
    EvalKleeneStmt P δ σ₀ σ (.loop s) σ''
    -/

end

end -- public section
