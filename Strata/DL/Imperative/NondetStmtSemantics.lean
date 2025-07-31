/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Imperative.CmdSemantics
import Strata.DL.Imperative.NondetStmt

---------------------------------------------------------------------

namespace Imperative

mutual

/-- An inductively-defined operational semantics for non-deterministic
statements that depends on environment lookup and evaluation functions
for expressions.  -/
inductive EvalNondetStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasBool P] [HasBoolNeg P] :
  SemanticEval P → SemanticEvalBool P → SemanticStore P → SemanticStore P →
    NondetStmt P Cmd → SemanticStore P → Prop where
  | cmd_sem :
    EvalCmd δ δP σ₀ σ c σ' →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    isDefinedOver (HasVarsImp.modifiedVars) σ c →
    ----
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ (NondetStmt.cmd c) σ'

  | seq_sem :
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ s1 σ' →
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ' s2 σ'' →
    ----
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ (.seq s1 s2) σ''

  | choice_left_sem :
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ s1 σ' →
    WellFormedSemanticEvalBool δ δP →
    ----
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ (.choice s1 s2) σ'

  | choice_right_sem :
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ s2 σ' →
    WellFormedSemanticEvalBool δ δP →
    ----
    EvalNondetStmt P Cmd EvalCmd δ δP σ₀ σ (.choice s1 s2) σ'

  /-
  | loop_sem :
    EvalNondetStmt P δ δP σ₀ σ s σ' →
    EvalNondetStmt P δ δP σ₀ σ' (.loop s) σ'' →
    ----
    EvalNondetStmt P δ δP σ₀ σ (.loop s) σ''
    -/

end
