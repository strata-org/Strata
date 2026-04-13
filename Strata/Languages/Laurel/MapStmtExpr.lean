/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel

/-!
# Generic Top-Down AST Traversal

Provides `mapStmtExprM`, a generic top-down monadic traversal of `StmtExprMd`.
The user-supplied function `f` is applied first, then the result's children are
recursively traversed. Passes that only need custom logic for a few constructors
can pattern-match in `f` and fall through to the default recursion for the rest.

Also provides `mapProcedureBodiesM` and `mapProgramM` to eliminate the
`Body`/`Procedure`/`Program` boilerplate shared by nearly every pass.
-/

namespace Strata.Laurel

public section

/--
Top-down monadic traversal of `StmtExprMd`. Applies `f` to the node first,
then recurses into all `StmtExprMd` children of the result.
-/
partial def mapStmtExprM [Monad m] (f : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd := do
  let expr ← f expr
  let md := expr.md
  match expr with
  | WithMetadata.mk val _ =>
  match val with
  | .IfThenElse cond th el =>
    return ⟨.IfThenElse (← mapStmtExprM f cond) (← mapStmtExprM f th) (← el.mapM (mapStmtExprM f)), md⟩
  | .Block stmts label =>
    return ⟨.Block (← stmts.mapM (mapStmtExprM f)) label, md⟩
  | .LocalVariable name ty init =>
    return ⟨.LocalVariable name ty (← init.mapM (mapStmtExprM f)), md⟩
  | .While cond invs dec body =>
    return ⟨.While (← mapStmtExprM f cond) (← invs.mapM (mapStmtExprM f))
      (← dec.mapM (mapStmtExprM f)) (← mapStmtExprM f body), md⟩
  | .Return v =>
    return ⟨.Return (← v.mapM (mapStmtExprM f)), md⟩
  | .Assign targets value =>
    return ⟨.Assign (← targets.mapM (mapStmtExprM f)) (← mapStmtExprM f value), md⟩
  | .FieldSelect target fieldName =>
    return ⟨.FieldSelect (← mapStmtExprM f target) fieldName, md⟩
  | .PureFieldUpdate target fieldName newValue =>
    return ⟨.PureFieldUpdate (← mapStmtExprM f target) fieldName (← mapStmtExprM f newValue), md⟩
  | .StaticCall callee args =>
    return ⟨.StaticCall callee (← args.mapM (mapStmtExprM f)), md⟩
  | .PrimitiveOp op args =>
    return ⟨.PrimitiveOp op (← args.mapM (mapStmtExprM f)), md⟩
  | .ReferenceEquals lhs rhs =>
    return ⟨.ReferenceEquals (← mapStmtExprM f lhs) (← mapStmtExprM f rhs), md⟩
  | .AsType target ty =>
    return ⟨.AsType (← mapStmtExprM f target) ty, md⟩
  | .IsType target ty =>
    return ⟨.IsType (← mapStmtExprM f target) ty, md⟩
  | .InstanceCall target callee args =>
    return ⟨.InstanceCall (← mapStmtExprM f target) callee (← args.mapM (mapStmtExprM f)), md⟩
  | .Forall param trigger body =>
    return ⟨.Forall param (← trigger.mapM (mapStmtExprM f)) (← mapStmtExprM f body), md⟩
  | .Exists param trigger body =>
    return ⟨.Exists param (← trigger.mapM (mapStmtExprM f)) (← mapStmtExprM f body), md⟩
  | .Assigned name =>
    return ⟨.Assigned (← mapStmtExprM f name), md⟩
  | .Old value =>
    return ⟨.Old (← mapStmtExprM f value), md⟩
  | .Fresh value =>
    return ⟨.Fresh (← mapStmtExprM f value), md⟩
  | .Assert cond =>
    return ⟨.Assert (← mapStmtExprM f cond), md⟩
  | .Assume cond =>
    return ⟨.Assume (← mapStmtExprM f cond), md⟩
  | .ProveBy value proof =>
    return ⟨.ProveBy (← mapStmtExprM f value) (← mapStmtExprM f proof), md⟩
  | .ContractOf ty func =>
    return ⟨.ContractOf ty (← mapStmtExprM f func), md⟩
  -- Leaves: no StmtExprMd children.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise all passes will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _
  | .Identifier _ | .New _ | .This | .Abstract | .All | .Hole .. => return expr

/-- Pure top-down traversal of `StmtExprMd`. -/
def mapStmtExpr (f : StmtExprMd → StmtExprMd) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprM (m := Id) f expr)

/-- Apply a monadic transformation to all procedure bodies. -/
def mapProcedureBodiesM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  match proc.body with
  | .Transparent b => return { proc with body := .Transparent (← f b) }
  | .Opaque posts impl mods =>
    return { proc with body := .Opaque (← posts.mapM f) (← impl.mapM f) (← mods.mapM f) }
  | .Abstract posts => return { proc with body := .Abstract (← posts.mapM f) }
  | .External => return proc

/-- Apply a monadic transformation to all `StmtExprMd` nodes in a procedure
    (preconditions, decreases, body, and invokeOn). -/
def mapProcedureM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  let proc ← mapProcedureBodiesM f proc
  return { proc with
    preconditions := ← proc.preconditions.mapM f
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
