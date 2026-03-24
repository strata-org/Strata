/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.NondetStmt
public import Strata.DL.Imperative.StmtSemantics

---------------------------------------------------------------------

namespace Imperative

public section

mutual

/-- An inductively-defined operational semantics for non-deterministic
statements that depends on environment lookup and evaluation functions for
expressions.  **NOTE:** This will probably be replaced with a small-step
semantics.
Note: Nondeterministic statements don't track evaluator changes since
commands preserve the evaluator (only funcDecl statements modify it).

The `Env` bundles the store, evaluator, and cumulative failure flag.
Commands may update the store and set the failure flag via
`ρ.hasFailure || hasAssertFailure`. -/
inductive EvalNondetStmt (P : PureExpr) (Cmd : Type) (EvalCmd : EvalCmdParam P Cmd)
  [HasVarsImp P (List (Stmt P Cmd))] [HasVarsImp P Cmd] [HasFvar P] [HasBool P] [HasNot P] :
  Env P → NondetStmt P Cmd → Env P → Prop where
  | cmd_sem :
    EvalCmd ρ.eval ρ.store c σ' hasAssertFailure →
    -- We only require definedness on the statement level so that the requirement is fine-grained
    isDefinedOver (HasVarsImp.modifiedVars) ρ.store c →
    ----
    EvalNondetStmt P Cmd EvalCmd
      ρ (NondetStmt.cmd c) { ρ with store := σ', hasFailure := ρ.hasFailure || hasAssertFailure }

  | seq_sem :
    EvalNondetStmt P Cmd EvalCmd ρ s1 ρ' →
    EvalNondetStmt P Cmd EvalCmd ρ' s2 ρ'' →
    ----
    EvalNondetStmt P Cmd EvalCmd ρ (.seq s1 s2) ρ''

  | choice_left_sem :
    WellFormedSemanticEvalBool ρ.eval →
    EvalNondetStmt P Cmd EvalCmd ρ s1 ρ' →
    ----
    EvalNondetStmt P Cmd EvalCmd ρ (.choice s1 s2) ρ'

  | choice_right_sem :
    WellFormedSemanticEvalBool ρ.eval →
    EvalNondetStmt P Cmd EvalCmd ρ s2 ρ' →
    ----
    EvalNondetStmt P Cmd EvalCmd ρ (.choice s1 s2) ρ'

  /-
  | loop_sem :
    EvalNondetStmt P ρ₀ ρ s ρ' →
    EvalNondetStmt P ρ₀ ρ' (.loop s) ρ'' →
    ----
    EvalNondetStmt P ρ₀ ρ (.loop s) ρ''
    -/

end

end -- public section
