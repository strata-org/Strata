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

/-- Generic bottom-up traversal/rewrite of `HighType`: recurse into every
    component type first, then apply `f` to the rebuilt node. Constructors with
    no component types are passed to `f` unchanged. Analogous to `mapStmtExpr`
    but for types — a pass that only rewrites a few type constructors can
    pattern-match in `f` and fall through for the rest. -/
partial def HighType.mapType (f : HighType → HighType) : HighType → HighType
  | .TSet e => f (.TSet ⟨HighType.mapType f e.val, e.source⟩)
  | .TMap k v =>
    f (.TMap ⟨HighType.mapType f k.val, k.source⟩ ⟨HighType.mapType f v.val, v.source⟩)
  | .Applied base args =>
    f (.Applied ⟨HighType.mapType f base.val, base.source⟩
       (args.map fun a => ⟨HighType.mapType f a.val, a.source⟩))
  | .Intersection tys =>
    f (.Intersection (tys.map fun t => ⟨HighType.mapType f t.val, t.source⟩))
  | .MultiValuedExpr tys =>
    f (.MultiValuedExpr (tys.map fun t => ⟨HighType.mapType f t.val, t.source⟩))
  | ty => f ty

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
  | .While cond invs dec body postTest =>
    pure ⟨.While (← mapStmtExprUsedM f true cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprUsedM f true e)
      (← mapStmtExprUsedM f false body) postTest, source⟩
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
  -- `.CompoundAssign` carries an `rhs` that must be traversed even for Local/Declare targets.
  | .CompoundAssign op ⟨.Field tgt fieldName, vs⟩ rhs =>
    pure ⟨.CompoundAssign op ⟨.Field (← mapStmtExprUsedM f true tgt) fieldName, vs⟩ (← mapStmtExprUsedM f true rhs), source⟩
  | .CompoundAssign op target rhs =>
    pure ⟨.CompoundAssign op target (← mapStmtExprUsedM f true rhs), source⟩
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
  | .Assert cond summary =>
    pure ⟨.Assert (← mapStmtExprUsedM f true cond) summary, source⟩
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
    | .While cond invs dec body postTest =>
      pure ⟨.While (collapse (← go true cond) cond.source)
        (← invs.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source))
        (← dec.attach.mapM fun ⟨x, _⟩ => do pure (collapse (← go true x) x.source))
        (collapse (← go false body) body.source) postTest, source⟩
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
    -- `.CompoundAssign` carries an `rhs` that must be traversed even for Local/Declare targets.
    | .CompoundAssign op ⟨.Field tgt fieldName, vs⟩ rhs =>
      pure ⟨.CompoundAssign op ⟨.Field (collapse (← go true tgt) tgt.source) fieldName, vs⟩
        (collapse (← go true rhs) rhs.source), source⟩
    | .CompoundAssign op target rhs =>
      pure ⟨.CompoundAssign op target (collapse (← go true rhs) rhs.source), source⟩
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
    | .Assert cond summary =>
      pure ⟨.Assert (collapse (← go true cond) cond.source) summary, source⟩
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

/-
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
  | .While cond invs dec body postTest =>
    pure ⟨.While (← mapStmtExprPrePostM pre post cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprPrePostM pre post e)
      (← mapStmtExprPrePostM pre post body) postTest, source⟩
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
  | .IncrDecr mode op target => match target with
    | ⟨.Field tgt fieldName, vs⟩ => pure ⟨.IncrDecr mode op ⟨.Field (← mapStmtExprPrePostM pre post tgt) fieldName, vs⟩, source⟩
    | ⟨.Local _, _⟩
    | ⟨.Declare _, _⟩ => pure expr
  -- `.CompoundAssign` carries an `rhs` that must be traversed even for Local/Declare targets.
  | .CompoundAssign op ⟨.Field tgt fieldName, vs⟩ rhs =>
    pure ⟨.CompoundAssign op ⟨.Field (← mapStmtExprPrePostM pre post tgt) fieldName, vs⟩
      (← mapStmtExprPrePostM pre post rhs), source⟩
  | .CompoundAssign op target rhs =>
    pure ⟨.CompoundAssign op target (← mapStmtExprPrePostM pre post rhs), source⟩

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
  | .Assert cond summary =>
    pure ⟨.Assert (← mapStmtExprPrePostM pre post cond) summary, source⟩
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

/-! ## Read-only traversals

`foldStmtExprM` visits every `StmtExprMd` node (pre-order: a node is visited
before its children, children left-to-right) without rebuilding the tree, so the
caller can accumulate information in a monad. It is the read-only counterpart of
`mapStmtExprM`, implemented on top of `mapStmtExprPrePostM` so the child
enumeration lives in exactly one place.

Analysis passes that care about only a handful of constructors should
pattern-match those in their visitor and ignore the rest, instead of hand-rolling
a full structural recursion — which is pure boilerplate for the irrelevant
constructors and silently skips children if a new constructor is added. -/

/-- Visit every `StmtExprMd` node (pre-order), running `f` for its effect.

    Unlike a fold built on `mapStmtExprPrePostM`, this walks the tree directly
    without rebuilding it — no `StmtExprMd` nodes are reconstructed, so a
    read-only traversal allocates nothing beyond `f`'s own effects. The child
    enumeration mirrors `mapStmtExprPrePostM`; if a new `StmtExpr` constructor
    with `StmtExprMd` children is added, it needs an arm here as well. -/
def foldStmtExprM [Monad m] (f : StmtExprMd → m Unit) (expr : StmtExprMd) : m Unit := do
  f expr
  match _h : expr.val with
  | .IfThenElse cond th el =>
    foldStmtExprM f cond; foldStmtExprM f th
    el.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .Block stmts _ =>
    stmts.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .While cond invs dec body _ =>
    foldStmtExprM f cond
    invs.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
    dec.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
    foldStmtExprM f body
  | .Return v =>
    v.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .Assign targets value =>
    targets.attach.forM fun ⟨v, _⟩ =>
      match v with
      | ⟨.Field target _, _⟩ => foldStmtExprM f target
      | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ()
    foldStmtExprM f value
  | .Var (.Field target _) =>
    foldStmtExprM f target
  | .IncrDecr _ _ target => match target with
    | ⟨.Field tgt _, _⟩ => foldStmtExprM f tgt
    | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ()
  | .CompoundAssign _ target rhs =>
    (match target with
     | ⟨.Field tgt _, _⟩ => foldStmtExprM f tgt
     | ⟨.Local _, _⟩ | ⟨.Declare _, _⟩ => pure ())
    foldStmtExprM f rhs
  | .PureFieldUpdate target _ newValue =>
    foldStmtExprM f target; foldStmtExprM f newValue
  | .StaticCall _ args =>
    args.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .PrimitiveOp _ args _ =>
    args.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .ReferenceEquals lhs rhs =>
    foldStmtExprM f lhs; foldStmtExprM f rhs
  | .AsType target _ =>
    foldStmtExprM f target
  | .IsType target _ =>
    foldStmtExprM f target
  | .InstanceCall target _ args =>
    foldStmtExprM f target
    args.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
  | .Quantifier _ _ trigger body =>
    trigger.attach.forM fun ⟨e, _⟩ => foldStmtExprM f e
    foldStmtExprM f body
  | .Assigned name =>
    foldStmtExprM f name
  | .Old value =>
    foldStmtExprM f value
  | .Fresh value =>
    foldStmtExprM f value
  | .Assert cond _ =>
    foldStmtExprM f cond
  | .Assume cond =>
    foldStmtExprM f cond
  | .ProveBy value proof =>
    foldStmtExprM f value; foldStmtExprM f proof
  | .ContractOf _ func =>
    foldStmtExprM f func
  -- Leaves: no StmtExprMd children.
  | .Exit _ | .LiteralInt _ | .LiteralBool _ | .LiteralString _ | .LiteralDecimal _ | .LiteralBv _ _
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure ()
termination_by sizeOf expr
decreasing_by map_stmt_expr_decreasing expr

/-- Pure accumulation over every node (pre-order, parent before children). -/
def foldStmtExpr {β : Type} (f : StmtExprMd → β → β) (init : β) (expr : StmtExprMd) : β :=
  (foldStmtExprM (m := StateM β) (fun e => modify (f e)) expr).run init |>.snd

/-- `true` iff `p` holds for at least one node in the tree. -/
def anyStmtExpr (p : StmtExprMd → Bool) (expr : StmtExprMd) : Bool :=
  foldStmtExpr (fun e acc => acc || p e) false expr

/-- Collect, in pre-order, the concatenation of `f` applied to every node. -/
def collectStmtExprList {β : Type} (f : StmtExprMd → List β) (expr : StmtExprMd) : List β :=
  foldStmtExpr (fun e acc => acc ++ f e) [] expr

/-- Apply a monadic transformation to all procedure bodies. -/
@[expose]
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

/-- Apply a monadic transformation to every procedure in a program — both
    top-level static procedures and the instance procedures of composite types.
    The single place that knows where procedures live in a `Program`, so passes
    don't each re-enumerate `staticProcedures` and composite `instanceProcedures`. -/
def mapProgramProceduresM [Monad m] (f : Procedure → m Procedure) (program : Program) : m Program := do
  let staticProcedures ← program.staticProcedures.mapM f
  let types ← program.types.mapM fun td =>
    match td with
    | .Composite ct => return .Composite { ct with instanceProcedures := ← ct.instanceProcedures.mapM f }
    | other => pure other
  return { program with staticProcedures := staticProcedures, types := types }

/-- Pure variant of `mapProgramProceduresM`. -/
def mapProgramProcedures (f : Procedure → Procedure) (program : Program) : Program :=
  mapProgramProceduresM (m := Id) f program

/-- Apply a monadic transformation to procedure bodies in a program.
    Does **not** traverse preconditions, decreases, or invokeOn — use
    `mapProcedureM` directly if those are needed. -/
def mapProgramM [Monad m] (f : StmtExprMd → m StmtExprMd) (program : Program) : m Program := do
  return { program with staticProcedures := ← program.staticProcedures.mapM (mapProcedureBodiesM f) }

/-- Apply a pure transformation to all `StmtExprMd` nodes in a program. -/
def mapProgram (f : StmtExprMd → StmtExprMd) (program : Program) : Program :=
  mapProgramM (m := Id) f program

/-! ## Type-annotation traversals

`mapStmtExprHighTypesM` and friends apply a `HighType → HighType` rewrite to
*every* type annotation reachable from a node / procedure / program, reusing
`mapStmtExprM` for the structural recursion. This is the single source of truth
for "rewrite all type references", so passes don't have to enumerate the
type-carrying constructors by hand (and silently miss one). The supplied `f` is
responsible for recursing into compound types (`TSet`/`TMap`/`Applied`/…). -/

/-- Rewrite the declared type carried by a `Variable` (only `Declare` carries one). -/
def mapVariableHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (v : Variable) : m Variable := do
  match v with
  | .Declare param => pure (.Declare { param with type := ← f param.type })
  | .Local _ | .Field _ _ => pure v

/--
Apply `f` to every `HighType` annotation carried *directly* by a single
`StmtExpr` node: local declarations (in `Var`, `Assign` targets, and `IncrDecr`
targets), quantifier binders, `AsType`/`IsType` type arguments, and typed
`Hole`s. Does **not** recurse into child expressions — compose with
`mapStmtExprM` (see `mapStmtExprHighTypesM`) for a whole-tree traversal.
-/
def mapNodeHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (expr : StmtExprMd) : m StmtExprMd := do
  let source := expr.source
  match expr.val with
  | .Var v => pure ⟨.Var (← mapVariableHighTypesM f v), source⟩
  | .Assign targets value =>
    let targets' ← targets.mapM (fun t => do pure (⟨← mapVariableHighTypesM f t.val, t.source⟩ : VariableMd))
    pure ⟨.Assign targets' value, source⟩
  | .IncrDecr mode op target =>
    pure ⟨.IncrDecr mode op ⟨← mapVariableHighTypesM f target.val, target.source⟩, source⟩
  | .CompoundAssign op target rhs =>
    pure ⟨.CompoundAssign op ⟨← mapVariableHighTypesM f target.val, target.source⟩ rhs, source⟩
  | .Quantifier mode param trigger body =>
    pure ⟨.Quantifier mode { param with type := ← f param.type } trigger body, source⟩
  | .AsType target ty => pure ⟨.AsType target (← f ty), source⟩
  | .IsType target ty => pure ⟨.IsType target (← f ty), source⟩
  | .Hole det (some ty) => pure ⟨.Hole det (some (← f ty)), source⟩
  | _ => pure expr

/-- Apply `f` to every `HighType` annotation appearing anywhere in a `StmtExprMd`. -/
def mapStmtExprHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (expr : StmtExprMd) : m StmtExprMd :=
  mapStmtExprM (mapNodeHighTypesM f) expr

/-- Pure version of `mapStmtExprHighTypesM`. -/
def mapStmtExprHighTypes (f : HighTypeMd → HighTypeMd) (expr : StmtExprMd) : StmtExprMd :=
  mapStmtExprHighTypesM (m := Id) f expr

/-- Apply `f` to every `HighType` annotation in a procedure: parameter types,
    body, preconditions, decreases measure, and auto-invocation trigger. -/
def mapProcedureHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (proc : Procedure) : m Procedure := do
  let mapExpr := mapStmtExprHighTypesM f
  let mapParam (p : Parameter) : m Parameter := do pure { p with type := ← f p.type }
  let body' ← match proc.body with
    | .Transparent b => pure (.Transparent (← mapExpr b))
    | .Opaque ps impl mods =>
      pure (.Opaque (← ps.mapM (·.mapM mapExpr)) (← impl.mapM mapExpr) (← mods.mapM mapExpr))
    | .Abstract ps => pure (.Abstract (← ps.mapM (·.mapM mapExpr)))
    | .External => pure .External
  return { proc with
    inputs := ← proc.inputs.mapM mapParam
    outputs := ← proc.outputs.mapM mapParam
    body := body'
    preconditions := ← proc.preconditions.mapM (·.mapM mapExpr)
    decreases := ← proc.decreases.mapM mapExpr
    invokeOn := ← proc.invokeOn.mapM mapExpr }

/-- Apply `f` to every `HighType` annotation in a type definition: composite
    fields and instance procedures, constrained base/constraint/witness,
    datatype constructor argument types, and alias targets. -/
def mapTypeDefinitionHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (td : TypeDefinition) : m TypeDefinition := do
  match td with
  | .Composite ct =>
    pure (.Composite { ct with
      fields := ← ct.fields.mapM (fun fld => do pure { fld with type := ← f fld.type })
      instanceProcedures := ← ct.instanceProcedures.mapM (mapProcedureHighTypesM f) })
  | .Constrained ct =>
    pure (.Constrained { ct with
      base := ← f ct.base
      constraint := ← mapStmtExprHighTypesM f ct.constraint
      witness := ← mapStmtExprHighTypesM f ct.witness })
  | .Datatype dt =>
    pure (.Datatype { dt with
      constructors := ← dt.constructors.mapM (fun ctor => do
        pure { ctor with args := ← ctor.args.mapM (fun p => do pure { p with type := ← f p.type }) }) })
  | .Alias ta => pure (.Alias { ta with target := ← f ta.target })

/-- Apply `f` to a constant's declared type and (optional) initializer. -/
def mapConstantHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (c : Constant) : m Constant := do
  pure { c with type := ← f c.type, initializer := ← c.initializer.mapM (mapStmtExprHighTypesM f) }

/-- Apply `f` to every `HighType` annotation anywhere in a program: procedures,
    static fields, type definitions, and constants. -/
def mapProgramHighTypesM [Monad m] (f : HighTypeMd → m HighTypeMd) (program : Program) : m Program := do
  return { program with
    staticProcedures := ← program.staticProcedures.mapM (mapProcedureHighTypesM f)
    staticFields := ← program.staticFields.mapM (fun fld => do pure { fld with type := ← f fld.type })
    types := ← program.types.mapM (mapTypeDefinitionHighTypesM f)
    constants := ← program.constants.mapM (mapConstantHighTypesM f) }

/-- Pure version of `mapProgramHighTypesM`. -/
def mapProgramHighTypes (f : HighTypeMd → HighTypeMd) (program : Program) : Program :=
  mapProgramHighTypesM (m := Id) f program

end -- public section
end Strata.Laurel
