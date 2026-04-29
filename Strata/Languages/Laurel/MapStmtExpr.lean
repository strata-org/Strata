/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
import Strata.Util.Tactics

/-!
# Generic Bottom-Up AST Traversal

Provides `mapStmtExprM`, a generic bottom-up monadic traversal of `StmtExprMd`.
Children are recursively traversed first, then the user-supplied function `f` is
applied to the result. Passes that only need custom logic for a few constructors
can pattern-match in `f` and fall through for the rest.

Also provides `mapProcedureBodiesM` and `mapProgramM` to eliminate the
`Body`/`Procedure`/`Program` boilerplate shared by nearly every pass.
-/

namespace Strata.Laurel

public section

/--
Bottom-up monadic traversal of `StmtExprMd`. Recurses into all `StmtExprMd`
children first, then applies `f` to the rebuilt node.
-/
def mapStmtExprM [Monad m] (f : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd := do
  let source := expr.source
  -- `.attach` wraps each element with a proof of membership, which the
  -- termination checker uses to show the recursive call is on a smaller value.
  let rebuilt ← match _h : expr.val with
  | .IfThenElse cond th el =>
    pure ⟨.IfThenElse (← mapStmtExprM f cond) (← mapStmtExprM f th)
      (← el.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Block stmts label =>
    pure ⟨.Block (← stmts.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e) label, source⟩
  | .LocalVariable name ty init =>
    pure ⟨.LocalVariable name ty (← init.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprM f cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← mapStmtExprM f body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Assign targets value =>
    pure ⟨.Assign (← targets.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e) (← mapStmtExprM f value), source⟩
  | .FieldSelect target fieldName =>
    pure ⟨.FieldSelect (← mapStmtExprM f target) fieldName, source⟩
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← mapStmtExprM f target) fieldName (← mapStmtExprM f newValue), source⟩
  | .StaticCall callee args =>
    pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .PrimitiveOp op args =>
    pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← mapStmtExprM f lhs) (← mapStmtExprM f rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← mapStmtExprM f target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← mapStmtExprM f target) ty, source⟩
  | .InstanceCall target callee args =>
    pure ⟨.InstanceCall (← mapStmtExprM f target) callee
      (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← mapStmtExprM f body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← mapStmtExprM f name), source⟩
  | .Old value =>
    pure ⟨.Old (← mapStmtExprM f value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← mapStmtExprM f value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← mapStmtExprM f cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← mapStmtExprM f cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← mapStmtExprM f value) (← mapStmtExprM f proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← mapStmtExprM f func), source⟩
  -- Leaves: no StmtExprMd children.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise all passes will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Identifier _ | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  f rebuilt
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals omega

/-- Pure bottom-up traversal of `StmtExprMd`. -/
def mapStmtExpr (f : StmtExprMd → StmtExprMd) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprM (m := Id) f expr)

/-- Apply a monadic transformation to all procedure bodies. -/
def mapProcedureBodiesM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  match proc.body with
  | .Transparent b => return { proc with body := .Transparent (← f b) }
  | .Opaque posts impl mods =>
    return { proc with body := .Opaque (← posts.mapM (·.mapM f)) (← impl.mapM f) (← mods.mapM f) }
  | .Abstract posts => return { proc with body := .Abstract (← posts.mapM (·.mapM f)) }
  | .External => return proc

/-- Apply a monadic transformation to all `StmtExprMd` nodes in a procedure
    (preconditions, decreases, body, and invokeOn). -/
def mapProcedureM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  let proc ← mapProcedureBodiesM f proc
  return { proc with
    preconditions := ← proc.preconditions.mapM (·.mapM f)
    decreases := ← proc.decreases.mapM f
    invokeOn := ← proc.invokeOn.mapM f }

/-- Apply a monadic transformation to procedure bodies in a program.
    Does **not** traverse preconditions, decreases, or invokeOn — use
    `mapProcedureM` directly if those are needed. -/
def mapProgramM [Monad m] (f : StmtExprMd → m StmtExprMd) (program : Program) : m Program := do
  return { program with staticProcedures := ← program.staticProcedures.mapM (mapProcedureBodiesM f) }

/-- Apply a pure transformation to all `StmtExprMd` nodes in a program. -/
def mapProgram (f : StmtExprMd → StmtExprMd) (program : Program) : Program :=
  mapProgramM (m := Id) f program

end -- public section
end Strata.Laurel
