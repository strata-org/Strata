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
  | .While cond invs dec body =>
    pure ⟨.While (← mapStmtExprM f cond)
      (← invs.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← dec.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e)
      (← mapStmtExprM f body), source⟩
  | .Return v =>
    pure ⟨.Return (← v.attach.mapM fun ⟨e, _⟩ => mapStmtExprM f e), source⟩
  | .Assign targets value =>
    let targets' ← targets.attach.mapM fun ⟨v, _⟩ => do
      let ⟨vv, vs⟩ := v
      match vv with
      | .Field target fieldName =>
        pure ⟨Variable.Field (← mapStmtExprM f target) fieldName, vs⟩
      | .Local _ | .Declare _ => pure v
    pure ⟨.Assign targets' (← mapStmtExprM f value), source⟩
  | .Var (.Field target fieldName) =>
    pure ⟨.Var (.Field (← mapStmtExprM f target) fieldName), source⟩
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
  | .Var (.Local _) | .Var (.Declare _) | .New _ | .This | .Abstract | .All | .Hole .. => pure expr
  f rebuilt
termination_by sizeOf expr
decreasing_by
  all_goals simp_wf
  all_goals (try have := AstNode.sizeOf_val_lt expr)
  all_goals (try have := Condition.sizeOf_condition_lt ‹_›)
  all_goals (try term_by_mem)
  all_goals (cases expr; simp_all; omega)

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

/-! ## Build-time traversal-coverage check

`mapStmtExprM` is the single point through which every pass recurses into the
AST, so the one structural invariant the passes rely on is that it descends into
*every* `StmtExprMd` child of *every* constructor. The match above is exhaustive
(no wildcard), so adding a constructor already forces a decision there — but a
constructor that *carries* children could still be parked in the leaf arm
(`pure expr`) and compile, silently skipping recursion. That is the bug class
this check rules out at build time.

For each constructor we build a representative with a sentinel literal in every
`StmtExprMd` child position and run it through `mapStmtExprM` in a counting
monad. If the traversal reaches fewer sentinels than were placed — because the
constructor is treated as a leaf, or an arm forgets a child — the `#eval` below
throws and `lake build` fails.

Maintenance: a new constructor makes `covCtorKey` non-exhaustive (a compile
error), and the completeness assertion fails until a probe with a fresh key is
added to `covProbes`. Keep the placed-sentinel count in each probe in sync with
the number of `StmtExprMd` children. The check uses `mapStmtExprM` itself, so it
is a coverage test of the traversal, not an independent re-implementation of it.
-/

private def covSentinelText : String := "§MAP_STMT_EXPR_COVERAGE_SENTINEL§"
private def covId (s : String) : Identifier := ⟨s, none, none⟩
private def covS : StmtExprMd := ⟨.LiteralString covSentinelText, none⟩
private def covMd (e : StmtExpr) : StmtExprMd := ⟨e, none⟩
private def covVmd (v : Variable) : VariableMd := ⟨v, none⟩
private def covTy : HighTypeMd := ⟨.TInt, none⟩
private def covParam : Parameter := { name := covId "p", type := ⟨.TInt, none⟩ }
private def covCond : Condition := { condition := covS, summary := none }

/-- A distinct key per `StmtExpr` constructor. Exhaustive (no wildcard): a new
    constructor forces an entry here, and then the completeness assertion in the
    `#eval` below forces a matching probe in `covProbes`. -/
private def covCtorKey : StmtExpr → Nat
  | .IfThenElse ..    => 0
  | .Block ..         => 1
  | .While ..         => 2
  | .Exit ..          => 3
  | .Return ..        => 4
  | .LiteralInt ..    => 5
  | .LiteralBool ..   => 6
  | .LiteralString .. => 7
  | .LiteralDecimal .. => 8
  | .Var ..           => 9
  | .Assign ..        => 10
  | .PureFieldUpdate .. => 11
  | .StaticCall ..    => 12
  | .PrimitiveOp ..   => 13
  | .New ..           => 14
  | .This             => 15
  | .ReferenceEquals .. => 16
  | .AsType ..        => 17
  | .IsType ..        => 18
  | .InstanceCall ..  => 19
  | .Quantifier ..    => 20
  | .Assigned ..      => 21
  | .Old ..           => 22
  | .Fresh ..         => 23
  | .Assert ..        => 24
  | .Assume ..        => 25
  | .ProveBy ..       => 26
  | .ContractOf ..    => 27
  | .Abstract         => 28
  | .All              => 29
  | .Hole ..          => 30

/-- The total number of `StmtExpr` constructors. Bump this when adding one. -/
private def covCtorCount : Nat := 31

/-- One representative per constructor, paired with the number of sentinels it
    places in `StmtExprMd` child positions. -/
private def covProbes : List (StmtExprMd × Nat) := [
  (covMd (.IfThenElse covS covS (some covS)), 3),
  (covMd (.Block [covS, covS] none), 2),
  (covMd (.While covS [covS] (some covS) covS), 4),
  (covMd (.Exit "blk"), 0),
  (covMd (.Return (some covS)), 1),
  (covMd (.LiteralInt 0), 0),
  (covMd (.LiteralBool true), 0),
  (covMd (.LiteralString "x"), 0),
  (covMd (.LiteralDecimal ⟨0, 0⟩), 0),
  (covMd (.Var (.Field covS (covId "f"))), 1),
  (covMd (.Assign [covVmd (.Field covS (covId "f"))] covS), 2),
  (covMd (.PureFieldUpdate covS (covId "f") covS), 2),
  (covMd (.StaticCall (covId "c") [covS, covS]), 2),
  (covMd (.PrimitiveOp .Add [covS, covS]), 2),
  (covMd (.New (covId "r")), 0),
  (covMd .This, 0),
  (covMd (.ReferenceEquals covS covS), 2),
  (covMd (.AsType covS covTy), 1),
  (covMd (.IsType covS covTy), 1),
  (covMd (.InstanceCall covS (covId "c") [covS, covS]), 3),
  (covMd (.Quantifier .Forall covParam (some covS) covS), 2),
  (covMd (.Assigned covS), 1),
  (covMd (.Old covS), 1),
  (covMd (.Fresh covS), 1),
  (covMd (.Assert covCond), 1),
  (covMd (.Assume covS), 1),
  (covMd (.ProveBy covS covS), 2),
  (covMd (.ContractOf .Reads covS), 1),
  (covMd .Abstract, 0),
  (covMd .All, 0),
  (covMd (.Hole true none), 0)
]

/-- How many sentinels `mapStmtExprM` actually reaches when traversing `e`. -/
private def covReached (e : StmtExprMd) : Nat :=
  (mapStmtExprM (m := StateM Nat)
    (fun n => do
      match n.val with
      | .LiteralString s => if s == covSentinelText then modify (· + 1)
      | _ => pure ()
      pure n) e |>.run 0).2

-- Completeness: every constructor has exactly one probe. A new constructor makes
-- `covCtorKey` non-exhaustive (compile error) and then fails this check until a
-- probe with a fresh key and the right child count is added to `covProbes`.
-- Coverage: `mapStmtExprM` reaches every sentinel placed in a child position. A
-- constructor with children that is parked in the leaf arm (or an arm that drops
-- a child) reaches fewer sentinels than were placed and fails here. Both checks
-- run when this module is elaborated, so a violation fails `lake build`.
#eval (do
  let keys := covProbes.map (fun p => covCtorKey p.1.val)
  unless keys.eraseDups.length == covCtorCount do
    throw <| IO.userError
      s!"mapStmtExprM coverage: probes cover {keys.eraseDups.length} distinct \
         constructors, expected {covCtorCount}; add a probe for the new constructor."
  for (node, placed) in covProbes do
    let reached := covReached node
    unless reached == placed do
      throw <| IO.userError
        s!"mapStmtExprM coverage: constructor with covCtorKey {covCtorKey node.val} has \
           {placed} StmtExpr child slot(s) but the traversal reached {reached}; give it a \
           recursing arm in mapStmtExprM rather than leaving it in the leaf arm."
  : IO Unit)

end Strata.Laurel
