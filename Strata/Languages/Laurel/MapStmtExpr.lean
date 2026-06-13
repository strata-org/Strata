/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
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

/-- Shared termination tactic for `mapStmtExpr*` traversals. The argument is
    the variable representing the expression being recursed on. -/
local syntax "map_stmt_expr_decreasing" ident : tactic
macro_rules
  | `(tactic| map_stmt_expr_decreasing $x:ident) =>
    `(tactic| (
      all_goals simp_wf
      all_goals (try have := AstNode.sizeOf_val_lt $x)
      all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
      all_goals (try term_by_mem)
      all_goals (revert $x; intro x; cases x; simp_all; omega)))

public section

/--
Bottom-up monadic traversal with a pre-filter. Before recursing into a node's
children, `pre` is called. If `pre` returns `some result`, that result is used
directly (children are NOT recursed into). If `pre` returns `none`, normal
bottom-up recursion proceeds and `post` is applied after children are rebuilt.
-/
def mapStmtExprPrePostM [Monad m] (pre : StmtExprMd → m (Option StmtExprMd))
    (post : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd := do
  match ← pre expr with
  | some result => return result
  | none =>
  let source := expr.source
  let rebuilt ← match _h : expr.val with
  | .IfThenElse cond th el =>
    pure ⟨.IfThenElse (← mapStmtExprPrePostM pre post cond) (← mapStmtExprPrePostM pre post th)
      (← el.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e), source⟩
  | .Block stmts label =>
    pure ⟨.Block (← stmts.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e) label, source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprPrePostM pre post cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e)
      (← mapStmtExprPrePostM pre post body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e), source⟩
  | .Assign targets value =>
    let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprPrePostM pre post target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← mapStmtExprPrePostM pre post value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← mapStmtExprPrePostM pre post target) fieldName), source⟩
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← mapStmtExprPrePostM pre post target) fieldName (← mapStmtExprPrePostM pre post newValue), source⟩
  | .StaticCall callee args =>
    pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e), source⟩
  | .PrimitiveOp op args skipProofs =>
    pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e) skipProofs, source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← mapStmtExprPrePostM pre post lhs) (← mapStmtExprPrePostM pre post rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← mapStmtExprPrePostM pre post target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← mapStmtExprPrePostM pre post target) ty, source⟩
  | .InstanceCall target callee args =>
    pure ⟨.InstanceCall (← mapStmtExprPrePostM pre post target) callee
      (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e), source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e)
      (← mapStmtExprPrePostM pre post body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← mapStmtExprPrePostM pre post name), source⟩
  | .Old value =>
    pure ⟨.Old (← mapStmtExprPrePostM pre post value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← mapStmtExprPrePostM pre post value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← mapStmtExprPrePostM pre post cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← mapStmtExprPrePostM pre post cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← mapStmtExprPrePostM pre post value) (← mapStmtExprPrePostM pre post proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← mapStmtExprPrePostM pre post func), source⟩
  -- Leaves: no StmtExprMd children.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise all passes will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  post rebuilt
termination_by sizeOf expr
decreasing_by map_stmt_expr_decreasing expr

/--
Bottom-up monadic traversal of `StmtExprMd`. Recurses into all `StmtExprMd`
children first, then applies `f` to the rebuilt node.
-/
def mapStmtExprM [Monad m] (f : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd :=
  mapStmtExprPrePostM (fun _ => pure none) f expr

/-- Pure bottom-up traversal of `StmtExprMd`. -/
def mapStmtExpr (f : StmtExprMd → StmtExprMd) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprM (m := Id) f expr)

/--
Bottom-up monadic traversal where `post` returns a list of statements.
- For `Block` nodes: each child is processed and the resulting lists are
  flattened into the block's statement list.
- For all other nodes: if `post` returns a single element, that element is
  used directly. If it returns multiple elements, they are wrapped in a new
  `Block none`.

`pre` works the same as in `mapStmtExprPrePostM`: returning `some` skips
recursion into children.
-/
def mapStmtExprFlattenM [Monad m] (pre : StmtExprMd → m (Option (List StmtExprMd)))
    (post : StmtExprMd → m (List StmtExprMd)) (expr : StmtExprMd) : m StmtExprMd := do
  let collapse (results : List StmtExprMd) (src : Option FileRange) : StmtExprMd :=
    match results with
    | [single] => single
    | many => ⟨.Block many none, src⟩
  let rec go (e : StmtExprMd) : m StmtExprMd := do
    match ← pre e with
    | some results => return collapse results e.source
    | none =>
    let source := e.source
    let rebuilt ← match _h : e.val with
    | .IfThenElse cond th el =>
      pure ⟨.IfThenElse (← go cond) (← go th)
        (← el.attach.mapM fun ⟨x, _⟩ => go x), source⟩
    | .Block stmts label =>
      let flatStmts ← stmts.attach.flatMapM fun ⟨x, _⟩ => do
        match ← pre x with
        | some results => return results
        | none =>
        let r ← go x
        post r
      pure ⟨.Block flatStmts label, source⟩
    | .While cond invs dec body =>
      pure ⟨.While (← go cond)
        (← invs.attach.mapM fun ⟨x, _⟩ => go x)
        (← dec.attach.mapM fun ⟨x, _⟩ => go x)
        (← go body), source⟩
    | .Return v =>
      pure ⟨.Return (← v.attach.mapM fun ⟨x, _⟩ => go x), source⟩
    | .Assign targets value =>
      let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
        let ⟨vv, vs⟩ := v
        match vv with
        | .Field target fieldName =>
          pure ⟨Variable.Field (← go target) fieldName, vs⟩
        | .Local _ | .Declare _ => pure v
      pure ⟨.Assign targets' (← go value), source⟩
    | .Var (.Field target fieldName) =>
      pure ⟨.Var (.Field (← go target) fieldName), source⟩
    | .PureFieldUpdate target fieldName newValue =>
      pure ⟨.PureFieldUpdate (← go target) fieldName (← go newValue), source⟩
    | .StaticCall callee args =>
      pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨x, _⟩ => go x), source⟩
    | .PrimitiveOp op args skipProofs =>
      pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨x, _⟩ => go x) skipProofs, source⟩
    | .ReferenceEquals lhs rhs =>
      pure ⟨.ReferenceEquals (← go lhs) (← go rhs), source⟩
    | .AsType target ty =>
      pure ⟨.AsType (← go target) ty, source⟩
    | .IsType target ty =>
      pure ⟨.IsType (← go target) ty, source⟩
    | .InstanceCall target callee args =>
      pure ⟨.InstanceCall (← go target) callee
        (← args.attach.mapM fun ⟨x, _⟩ => go x), source⟩
    | .Quantifier mode param trigger body =>
      pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨x, _⟩ => go x)
        (← go body), source⟩
    | .Assigned name => pure ⟨.Assigned (← go name), source⟩
    | .Old value => pure ⟨.Old (← go value), source⟩
    | .Fresh value => pure ⟨.Fresh (← go value), source⟩
    | .Assert cond =>
      pure ⟨.Assert { cond with condition := ← go cond.condition }, source⟩
    | .Assume cond => pure ⟨.Assume (← go cond), source⟩
    | .ProveBy value proof =>
      pure ⟨.ProveBy (← go value) (← go proof), source⟩
    | .ContractOf ty func => pure ⟨.ContractOf ty (← go func), source⟩
    | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
    | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure e
    let results ← post rebuilt
    return collapse results source
  termination_by sizeOf e
  decreasing_by map_stmt_expr_decreasing e
  go expr

/-- Apply a monadic transformation to all procedure bodies. -/
def mapProcedureBodiesM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  match proc.body with
  | .Transparent b => return { proc with body := .Transparent (← f b) }
  | .Opaque posts impl mods =>
    return { proc with body := .Opaque (← posts.mapM (·.mapM f)) (← impl.mapM f) (← mods.mapM f) }
  | .Abstract posts => return { proc with body := .Abstract (← posts.mapM (·.mapM f)) }
  | .External => return proc

/-- Apply a monadic transformation to all `StmtExprMd` nodes in a procedure
    (preconditions, decreases, body, invokeOn, and axioms). -/
def mapProcedureM [Monad m] (f : StmtExprMd → m StmtExprMd) (proc : Procedure) : m Procedure := do
  let proc ← mapProcedureBodiesM f proc
  return { proc with
    preconditions := ← proc.preconditions.mapM (·.mapM f)
    decreases := ← proc.decreases.mapM f
    invokeOn := ← proc.invokeOn.mapM f
    axioms := ← proc.axioms.mapM f }

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
