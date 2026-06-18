/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Util.Tactics
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelTypes

namespace Strata
namespace Laurel

public section

/-
Lift heap reads and allocations out of expression positions so that, after this
pass, every field read (`obj#field`) and allocation (`new T`) sits as the sole
right-hand side of an assignment. This is the direct-emission counterpart to the
explicit `HeapParameterization` pass: instead of encoding field operations as
`$heap` map operations, we leave them as first-class Laurel nodes in a canonical
position that the translator lowers directly to `heapRead`/`heapAlloc`.

Detection is at the Laurel level: a heap read is exactly `.Var (.Field …)` and an
allocation is exactly `.New`, before any encoding. This makes detection complete
— position-independent and with no false negatives.

Per-position policy:
- Assignment RHS (embedded, nested, call arguments): lift into a preceding
  `var $t := …`. A read/allocation that is *already* the sole RHS is left as-is.
- `if`-guard, branch bodies, statement-call args, body `assert`/`assume`: lift
  (these have a statement slot and the guard is evaluated once).
- `while`-guard: cannot hoist out (re-evaluated each iteration), so duplicate the
  guard reads before the loop and on the back-edge (loop rotation).
- Specs (procedure pre/postconditions, loop invariants): NOT transformed. Field
  reads there denote reads against the ambient heap and pass through unchanged.

Example:
  x := self#balance + amount
becomes
  var $h_0 := self#balance;
  x := $h_0 + amount
-/

structure HeapLiftState where
  /-- Statements to prepend, in program order. -/
  prepended : List StmtExprMd := []
  /-- Counter for fresh temp names. -/
  counter : Nat := 0
  /-- Type environment, used to type the lifted temporaries. -/
  model : SemanticModel

@[expose] abbrev HeapLiftM := StateM HeapLiftState

private def freshHeapTemp : HeapLiftM Identifier := do
  let n := (← get).counter
  modify fun s => { s with counter := n + 1 }
  return s!"$h_{n}"

private def prepend (stmt : StmtExprMd) : HeapLiftM Unit :=
  modify fun s => { s with prepended := s.prepended ++ [stmt] }

private def takePrepends : HeapLiftM (List StmtExprMd) := do
  let stmts := (← get).prepended
  modify fun s => { s with prepended := [] }
  return stmts

private def computeType (expr : StmtExprMd) : HeapLiftM HighTypeMd := do
  return computeExprType (← get).model expr

/-- Type of a field read `target#fieldName`, looked up from the field's
declaration in `target`'s composite type. This is robust to nested reads:
`computeExprType` keys a field read on `fieldName`'s own resolution, which a
single resolution pass leaves `Unknown` when the target is itself a field
access (e.g. `(a#next)#balance`). Looking the field up via the target's already
-known composite type avoids that. Falls back to `computeExprType` when the
target's type is not a composite. -/
private def fieldReadType (target : StmtExprMd) (fieldName : Identifier)
    (source : Option FileRange) : HeapLiftM HighTypeMd := do
  let model := (← get).model
  let fallback : HighTypeMd := computeExprType model ⟨.Var (.Field target fieldName), source⟩
  match (computeExprType model target).val with
  | .UserDefined typeName =>
    match model.get? typeName with
    | some (.compositeType ct) =>
      match ct.fields.find? (·.name.text == fieldName.text) with
      | some fld => return fld.type
      | none => return fallback
    | _ => return fallback
  | _ => return fallback

/-- Convert a lifted declaration `var $t := v` into a reassignment `$t := v`,
for use on a loop back-edge where the temp is already in scope. -/
private def declToReassign (stmt : StmtExprMd) : StmtExprMd :=
  match stmt with
  | ⟨.Assign [⟨.Declare ⟨name, _⟩, dsrc⟩] v, src⟩ => ⟨.Assign [⟨.Local name, dsrc⟩] v, src⟩
  | _ => stmt

mutual
/--
Transform an expression, lifting every embedded field read and allocation into a
preceding `var $t := …` (pushed onto `prepended`) and replacing it with a
reference to the fresh temp.
-/
def transformHeapExpr (expr : StmtExprMd) : HeapLiftM StmtExprMd := do
  match expr with
  | AstNode.mk val source =>
  match val with
  | .Var (.Field target fieldName) =>
      -- Lift any reads inside the object expression first, then bind this read.
      -- Type the read from the ORIGINAL target (whose type is computable) before
      -- lifting replaces it with a fresh temp not yet known to the model.
      let ty ← fieldReadType target fieldName source
      let target' ← transformHeapExpr target
      let t ← freshHeapTemp
      prepend ⟨.Assign [⟨.Declare ⟨t, ty⟩, source⟩] ⟨.Var (.Field target' fieldName), source⟩, source⟩
      return ⟨.Var (.Local t), source⟩
  | .New name =>
      let t ← freshHeapTemp
      let ty : HighTypeMd := ⟨.UserDefined name, source⟩
      prepend ⟨.Assign [⟨.Declare ⟨t, ty⟩, source⟩] expr, source⟩
      return ⟨.Var (.Local t), source⟩
  | .PrimitiveOp op args skip =>
      let args' ← args.attach.mapM (fun ⟨a, _⟩ => transformHeapExpr a)
      return ⟨.PrimitiveOp op args' skip, source⟩
  | .StaticCall callee args =>
      let args' ← args.attach.mapM (fun ⟨a, _⟩ => transformHeapExpr a)
      return ⟨.StaticCall callee args', source⟩
  | .ReferenceEquals lhs rhs =>
      return ⟨.ReferenceEquals (← transformHeapExpr lhs) (← transformHeapExpr rhs), source⟩
  | _ =>
      -- Literals, locals, and other leaves carry no embedded heap operations.
      return expr
  termination_by (sizeOf expr, 0)
  decreasing_by
    all_goals (simp_all; try term_by_mem)

/--
Transform a statement, lifting heap operations out of its sub-expressions.
Returns a list because a statement may expand into preceding lifted reads.
-/
def transformHeapStmt (stmt : StmtExprMd) : HeapLiftM (List StmtExprMd) := do
  match stmt with
  | AstNode.mk val source =>
  match val with
  | .Block stmts label =>
      let stmts' ← stmts.attach.mapM (fun ⟨s, _⟩ => transformHeapStmt s)
      return [⟨.Block stmts'.flatten label, source⟩]

  | .Assign targets value =>
      match targets with
      | [⟨.Field obj fieldName, tsrc⟩] =>
          -- Field-target write: lift reads in the object and in the value.
          let obj' ← transformHeapExpr obj
          let value' ← transformHeapExpr value
          let prepends ← takePrepends
          return prepends ++ [⟨.Assign [⟨.Field obj' fieldName, tsrc⟩] value', source⟩]
      | [target] =>
          -- Single non-field target. If the RHS is already a canonical heap
          -- read or allocation, keep it in place (only lift sub-expressions);
          -- otherwise lift any embedded reads out of the value.
          match value with
          | ⟨.Var (.Field obj fieldName), vsrc⟩ =>
              let obj' ← transformHeapExpr obj
              let prepends ← takePrepends
              return prepends ++ [⟨.Assign [target] ⟨.Var (.Field obj' fieldName), vsrc⟩, source⟩]
          | ⟨.New _, _⟩ =>
              return [stmt]
          | _ =>
              let value' ← transformHeapExpr value
              let prepends ← takePrepends
              return prepends ++ [⟨.Assign [target] value', source⟩]
      | _ =>
          -- Multi-target (call RHS): lift reads in the call arguments.
          let value' ← transformHeapExpr value
          let prepends ← takePrepends
          return prepends ++ [⟨.Assign targets value', source⟩]

  | .IfThenElse cond thenBranch elseBranch =>
      -- The guard is evaluated once, so lifted reads go before the `if`.
      let cond' ← transformHeapExpr cond
      let condPrepends ← takePrepends
      let thenStmts ← transformHeapStmt thenBranch
      let elseStmts ← match elseBranch with
        | some e => some <$> (do return (⟨.Block (← transformHeapStmt e) none, source⟩ : StmtExprMd))
        | none => pure none
      return condPrepends ++
        [⟨.IfThenElse cond' ⟨.Block thenStmts none, source⟩ elseStmts, source⟩]

  | .While cond invariants dec body =>
      -- The guard re-evaluates each iteration, so duplicate its lifted reads
      -- before the loop and on the back-edge. Invariants/measure are spec
      -- contexts and pass through unchanged.
      let cond' ← transformHeapExpr cond
      let guardDecls ← takePrepends
      let guardReassigns := guardDecls.map declToReassign
      let bodyStmts ← transformHeapStmt body
      let newBody : StmtExprMd := ⟨.Block (bodyStmts ++ guardReassigns) none, source⟩
      return guardDecls ++ [⟨.While cond' invariants dec newBody, source⟩]

  | .Assert c =>
      let cond' ← transformHeapExpr c.condition
      let prepends ← takePrepends
      return prepends ++ [⟨.Assert { c with condition := cond' }, source⟩]

  | .Assume c =>
      let cond' ← transformHeapExpr c
      let prepends ← takePrepends
      return prepends ++ [⟨.Assume cond', source⟩]

  | .StaticCall callee args =>
      let args' ← args.attach.mapM (fun ⟨a, _⟩ => transformHeapExpr a)
      let prepends ← takePrepends
      return prepends ++ [⟨.StaticCall callee args', source⟩]

  | .Return (some retExpr) =>
      let ret' ← transformHeapExpr retExpr
      let prepends ← takePrepends
      return prepends ++ [⟨.Return (some ret'), source⟩]

  | _ =>
      return [stmt]
  termination_by (sizeOf stmt, 1)
  decreasing_by
    all_goals (simp_all; try term_by_mem)
end

private def transformBody (body : StmtExprMd) : HeapLiftM StmtExprMd := do
  let stmts ← transformHeapStmt body
  match stmts with
  | [single] => return single
  | multiple => return ⟨.Block multiple none, body.source⟩

private def transformProcedure (proc : Procedure) : HeapLiftM Procedure := do
  modify fun s => { s with prepended := [], counter := 0 }
  match proc.body with
  | .Transparent bodyExpr =>
      return { proc with body := .Transparent (← transformBody bodyExpr) }
  | .Opaque postconds impl modif =>
      let impl' ← impl.mapM transformBody
      return { proc with body := .Opaque postconds impl' modif }
  | .Abstract _ | .External =>
      return proc

/--
Lift heap reads and allocations into canonical assignment position across a
program. Specs are left untouched.
-/
def liftHeapExpressions (model : SemanticModel) (program : Program) : Program :=
  let initState : HeapLiftState := { model := model }
  let (procs, _) := (program.staticProcedures.mapM transformProcedure).run initState
  { program with staticProcedures := procs }

end -- public section

/-- Pipeline pass: lift heap reads/allocations into canonical position.
Intended to run only in implicit heap mode (wired in a later step). -/
public def liftHeapExpressionsPass : LaurelPass where
  name := "LiftHeapExpressions"
  documentation := "Lifts field reads and allocations out of expression positions so each sits as the sole RHS of an assignment, ready for direct lowering to heapRead/heapAlloc. Used in implicit heap mode."
  run := fun p m => (liftHeapExpressions m p, [], {})

end Laurel
