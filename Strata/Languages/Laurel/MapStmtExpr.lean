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

/-- Shared termination tactic for the `mapStmtExpr*` traversals. The argument is
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
Bottom-up monadic traversal that also tells `f` whether the node's *result is
used* (`resultUsed`): `true` when the node sits in a value position (an operand,
a condition, an assignment RHS, the value of a used block, …) and `false` when
its result is discarded (a non-final statement of a block, a `while` body, …).

`resultUsed` is an inherited (top-down) attribute, threaded into the recursive
calls per constructor:
- value-consuming positions (call/operator args, conditions, `Assign` RHS,
  field targets, `Return`/`Assert`/`Assume`/quantifier/… operands) → `true`;
- a `Block`'s statements → `false`, except the last, which inherits the block's
  own `resultUsed` (the block evaluates to its last statement);
- `IfThenElse` branches inherit the conditional's `resultUsed`; its condition is
  always used;
- a `While` body → `false`.

The top-level `resultUsed` defaults to `false` (a procedure body is a statement).
-/
def mapStmtExprUsedM [Monad m] (f : Bool → StmtExprMd → m StmtExprMd)
    (resultUsed : Bool) (expr : StmtExprMd) : m StmtExprMd := do
  let source := expr.source
  -- `.attach` wraps each element with a proof of membership, which the
  -- termination checker uses to show the recursive call is on a smaller value.
  let rebuilt ← match _h : expr.val with
  | .IfThenElse cond th el =>
    pure ⟨.IfThenElse (← mapStmtExprUsedM f true cond) (← mapStmtExprUsedM f resultUsed th)
      (← el.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f resultUsed e), source⟩
  | .Block stmts label =>
    -- Only the last statement is in value position (and only if the block is).
    let stmts' ← stmts.attach.mapIdxM fun i ⟨e, _⟩ =>
      mapStmtExprUsedM f (resultUsed && i + 1 == stmts.length) e
    pure ⟨.Block stmts' label, source⟩
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprUsedM f true cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
      (← mapStmtExprUsedM f false body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e), source⟩
  | .Assign targets value =>
    let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprUsedM f true target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← mapStmtExprUsedM f true value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← mapStmtExprUsedM f true target) fieldName), source⟩
  | .IncrDecr mode op ⟨.Field tgt fieldName, vs⟩ =>
    pure ⟨.IncrDecr mode op ⟨.Field (← mapStmtExprUsedM f true tgt) fieldName, vs⟩, source⟩
  | .IncrDecr _ _ ⟨.Local _, _⟩ | .IncrDecr _ _ ⟨.Declare _, _⟩ => pure expr
  | .PureFieldUpdate target fieldName newValue =>
    pure ⟨.PureFieldUpdate (← mapStmtExprUsedM f true target) fieldName (← mapStmtExprUsedM f true newValue), source⟩
  | .StaticCall callee args =>
    pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e), source⟩
  | .PrimitiveOp op args skipProof =>
    pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e) skipProof, source⟩
  | .ReferenceEquals lhs rhs =>
    pure ⟨.ReferenceEquals (← mapStmtExprUsedM f true lhs) (← mapStmtExprUsedM f true rhs), source⟩
  | .AsType target ty =>
    pure ⟨.AsType (← mapStmtExprUsedM f true target) ty, source⟩
  | .IsType target ty =>
    pure ⟨.IsType (← mapStmtExprUsedM f true target) ty, source⟩
  | .InstanceCall target callee args =>
    pure ⟨.InstanceCall (← mapStmtExprUsedM f true target) callee
      (← args.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e), source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
      (← mapStmtExprUsedM f true body), source⟩
  | .Assigned name =>
    pure ⟨.Assigned (← mapStmtExprUsedM f true name), source⟩
  | .Old value =>
    pure ⟨.Old (← mapStmtExprUsedM f true value), source⟩
  | .Fresh value =>
    pure ⟨.Fresh (← mapStmtExprUsedM f true value), source⟩
  | .Assert cond =>
    pure ⟨.Assert { cond with condition := ← mapStmtExprUsedM f true cond.condition }, source⟩
  | .Assume cond =>
    pure ⟨.Assume (← mapStmtExprUsedM f true cond), source⟩
  | .ProveBy value proof =>
    pure ⟨.ProveBy (← mapStmtExprUsedM f true value) (← mapStmtExprUsedM f true proof), source⟩
  | .ContractOf ty func =>
    pure ⟨.ContractOf ty (← mapStmtExprUsedM f true func), source⟩
  -- Leaves: no StmtExprMd children.
  -- ⚠ If a new StmtExpr constructor with StmtExprMd children is added,
  -- it must get its own arm above; otherwise all passes will silently
  -- skip recursion into those children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  f resultUsed rebuilt
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

/--
Bottom-up monadic traversal of `StmtExprMd`. Recurses into all `StmtExprMd`
children first, then applies `f` to the rebuilt node. A `resultUsed`-agnostic
wrapper over `mapStmtExprUsedM`.
-/
def mapStmtExprM [Monad m] (f : StmtExprMd → m StmtExprMd) (expr : StmtExprMd) : m StmtExprMd :=
  mapStmtExprUsedM (fun _ e => f e) false expr

/-- Pure bottom-up traversal of `StmtExprMd`. -/
def mapStmtExpr (f : StmtExprMd → StmtExprMd) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprM (m := Id) f expr)

/--
Bottom-up monadic traversal where `post` returns a list of statements, and both
callbacks are told whether the node's *result is used* (`resultUsed`, threaded
exactly as in `mapStmtExprUsedM`).
- For `Block` nodes: each child is processed and the resulting lists are
  flattened into the block's statement list. Only the last statement is in value
  position (and only if the block itself is).
- For all other nodes: if `post` returns a single element, that element is used
  directly. If it returns multiple elements, they are wrapped in a new
  `Block none` (whose value is its last element) — so returning
  `[stmt, …, value]` in a *used* position yields a value-block, while the same
  list flattens into siblings in statement position.

`pre` works like in `mapStmtExprPrePostM`: returning `some` skips recursion.
-/
def mapStmtExprFlattenM [Monad m] (pre : Bool → StmtExprMd → m (Option (List StmtExprMd)))
    (post : Bool → StmtExprMd → m (List StmtExprMd)) (resultUsed : Bool) (expr : StmtExprMd) : m StmtExprMd := do
  let collapse (results : List StmtExprMd) (src : Option FileRange) : StmtExprMd :=
    match results with
    | [single] => single
    | many => ⟨.Block many none, src⟩
  -- `go` returns the (post-expanded) statement list for `e`. Value-position
  -- children collapse that list into a single node (a value-block when it has
  -- multiple statements); `Block` children keep their lists and splice them.
  let rec go (used : Bool) (e : StmtExprMd) : m (List StmtExprMd) := do
    match ← pre used e with
    | some results => return results
    | none =>
    let source := e.source
    let rebuilt ← match _h : e.val with
    | .IfThenElse cond th el =>
      pure ⟨.IfThenElse (collapse (← go true cond) cond.source) (collapse (← go used th) th.source)
        (← el.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go used x) x.source)), source⟩
    | .Block stmts label =>
      let nested ← stmts.attach.mapIdxM fun i ⟨x, _⟩ => go (used && i + 1 == stmts.length) x
      pure ⟨.Block nested.flatten label, source⟩
    | .While cond invs dec body =>
      pure ⟨.While (collapse (← go true cond) cond.source)
        (← invs.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source))
        (← dec.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source))
        (collapse (← go false body) body.source), source⟩
    | .Return v =>
      pure ⟨.Return (← v.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source)), source⟩
    | .Assign targets value =>
      let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
        let ⟨vv, vs⟩ := v
        match vv with
        | .Field target fieldName =>
          pure ⟨Variable.Field (collapse (← go true target) target.source) fieldName, vs⟩
        | .Local _ | .Declare _ => pure v
      pure ⟨.Assign targets' (collapse (← go true value) value.source), source⟩
    | .Var (.Field target fieldName) =>
      pure ⟨.Var (.Field (collapse (← go true target) target.source) fieldName), source⟩
    | .IncrDecr mode op ⟨.Field tgt fieldName, vs⟩ =>
      pure ⟨.IncrDecr mode op ⟨.Field (collapse (← go true tgt) tgt.source) fieldName, vs⟩, source⟩
    | .IncrDecr _ _ ⟨.Local _, _⟩ | .IncrDecr _ _ ⟨.Declare _, _⟩ => pure e
    | .PureFieldUpdate target fieldName newValue =>
      pure ⟨.PureFieldUpdate (collapse (← go true target) target.source) fieldName
        (collapse (← go true newValue) newValue.source), source⟩
    | .StaticCall callee args =>
      pure ⟨.StaticCall callee (← args.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source)), source⟩
    | .PrimitiveOp op args skipProofs =>
      pure ⟨.PrimitiveOp op (← args.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source)) skipProofs, source⟩
    | .ReferenceEquals lhs rhs =>
      pure ⟨.ReferenceEquals (collapse (← go true lhs) lhs.source) (collapse (← go true rhs) rhs.source), source⟩
    | .AsType target ty =>
      pure ⟨.AsType (collapse (← go true target) target.source) ty, source⟩
    | .IsType target ty =>
      pure ⟨.IsType (collapse (← go true target) target.source) ty, source⟩
    | .InstanceCall target callee args =>
      pure ⟨.InstanceCall (collapse (← go true target) target.source) callee
        (← args.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source)), source⟩
    | .Quantifier mode param trigger body =>
      pure ⟨.Quantifier mode param (← trigger.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source))
        (collapse (← go true body) body.source), source⟩
    | .Assigned name => pure ⟨.Assigned (collapse (← go true name) name.source), source⟩
    | .Old value => pure ⟨.Old (collapse (← go true value) value.source), source⟩
    | .Fresh value => pure ⟨.Fresh (collapse (← go true value) value.source), source⟩
    | .Assert cond =>
      pure ⟨.Assert { cond with condition := collapse (← go true cond.condition) cond.condition.source }, source⟩
    | .Assume cond => pure ⟨.Assume (collapse (← go true cond) cond.source), source⟩
    | .ProveBy value proof =>
      pure ⟨.ProveBy (collapse (← go true value) value.source) (collapse (← go true proof) proof.source), source⟩
    | .ContractOf ty func => pure ⟨.ContractOf ty (collapse (← go true func) func.source), source⟩
    | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
    | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure e
    post used rebuilt
  termination_by sizeOf e
  decreasing_by map_stmt_expr_decreasing e
  return collapse (← go resultUsed expr) expr.source

/-- Pure `resultUsed`-aware bottom-up traversal (see `mapStmtExprUsedM`). -/
def mapStmtExprUsed (f : Bool → StmtExprMd → StmtExprMd) (resultUsed : Bool) (expr : StmtExprMd) : StmtExprMd :=
  (mapStmtExprUsedM (m := Id) f resultUsed expr)

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
