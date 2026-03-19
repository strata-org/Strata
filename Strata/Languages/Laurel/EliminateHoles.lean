/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Laurel
public import Strata.Languages.Laurel.LaurelFormat

/-!
# Deterministic Hole Elimination

Replace each deterministic typed `.Hole` with a call to a freshly generated
uninterpreted function whose parameters mirror the enclosing callable's inputs.

This pass assumes `inferHoleTypes` has already annotated every `Hole` with a
type. It works uniformly for both procedures and functions.

After this pass the program contains only non-deterministic `Hole` nodes.
-/

namespace Strata
namespace Laurel

public section

private def emptyMd : Imperative.MetaData Core.Expression := #[]
private def bare (v : StmtExpr) : StmtExprMd := ⟨v, emptyMd⟩

structure ElimHoleState where
  counter : Nat := 0
  currentInputs : List Parameter := []
  generatedFunctions : List Procedure := []

private abbrev ElimHoleM := StateM ElimHoleState

/-- Generate a fresh uninterpreted function for a typed hole and return a call to it. -/
private def mkHoleCall (holeType : HighTypeMd) : ElimHoleM StmtExprMd := do
  let s ← get
  let n := s.counter
  modify fun s => { s with counter := n + 1 }
  let holeName : Identifier := s!"$hole_{n}"
  let inputs := s.currentInputs
  let holeProc : Procedure := {
    name := holeName
    inputs := inputs
    outputs := [{ name := "$result", type := holeType }]
    preconditions := []
    determinism := .deterministic none
    decreases := none
    isFunctional := true
    body := .Opaque [] none []
    md := emptyMd
  }
  modify fun s => { s with generatedFunctions := s.generatedFunctions ++ [holeProc] }
  return bare (.StaticCall holeName (inputs.map (fun p => bare (.Identifier p.name))))

mutual
/--
Replace every deterministic `.Hole` in an expression with a call to a
fresh uninterpreted function.
-/
private def elimExpr (expr : StmtExprMd) : ElimHoleM StmtExprMd := do
  match expr with
  | WithMetadata.mk val md =>
  match val with
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Top, md⟩
  | .Hole false _ => return expr
  | .PrimitiveOp op args => return ⟨.PrimitiveOp op (← args.mapM elimExpr), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM elimExpr), md⟩
  | .InstanceCall target callee args =>
      return ⟨.InstanceCall (← elimExpr target) callee (← args.mapM elimExpr), md⟩
  | .ReferenceEquals lhs rhs => return ⟨.ReferenceEquals (← elimExpr lhs) (← elimExpr rhs), md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← elimExpr e)) | none => pure none
      return ⟨.IfThenElse (← elimExpr cond) (← elimExpr th) el', md⟩
  | .Block stmts label => return ⟨.Block (← elimStmtList stmts) label, md⟩
  | .Assign targets value => return ⟨.Assign targets (← elimExpr value), md⟩
  | .LocalVariable name ty init =>
      match init with
      | some initExpr => return ⟨.LocalVariable name ty (some (← elimExpr initExpr)), md⟩
      | none => return expr
  | .Old v => return ⟨.Old (← elimExpr v), md⟩
  | .Fresh v => return ⟨.Fresh (← elimExpr v), md⟩
  | .Assigned n => return ⟨.Assigned (← elimExpr n), md⟩
  | .ProveBy v p => return ⟨.ProveBy (← elimExpr v) (← elimExpr p), md⟩
  | .ContractOf ty f => return ⟨.ContractOf ty (← elimExpr f), md⟩
  | .Forall p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← elimExpr t)) | none => pure none
      return ⟨.Forall p trigger' (← elimExpr b), md⟩
  | .Exists p trigger b =>
      let trigger' ← match trigger with | some t => pure (some (← elimExpr t)) | none => pure none
      return ⟨.Exists p trigger' (← elimExpr b), md⟩
  | _ => return expr

private def elimStmt (stmt : StmtExprMd) : ElimHoleM StmtExprMd := do
  match stmt with
  | WithMetadata.mk val md =>
  match val with
  | .LocalVariable name ty (some initExpr) =>
      return ⟨.LocalVariable name ty (some (← elimExpr initExpr)), md⟩
  | .Assign targets value => return ⟨.Assign targets (← elimExpr value), md⟩
  | .Block stmts label => return ⟨.Block (← elimStmtList stmts) label, md⟩
  | .IfThenElse cond th el =>
      let el' ← match el with | some e => pure (some (← elimStmt e)) | none => pure none
      return ⟨.IfThenElse (← elimExpr cond) (← elimStmt th) el', md⟩
  | .While cond invs dec body =>
      let dec' ← match dec with | some d => pure (some (← elimExpr d)) | none => pure none
      return ⟨.While (← elimExpr cond) (← invs.mapM elimExpr) dec' (← elimStmt body), md⟩
  | .Assert cond => return ⟨.Assert (← elimExpr cond), md⟩
  | .Assume cond => return ⟨.Assume (← elimExpr cond), md⟩
  | .StaticCall callee args => return ⟨.StaticCall callee (← args.mapM elimExpr), md⟩
  | .Return (some retExpr) => return ⟨.Return (some (← elimExpr retExpr)), md⟩
  | .Hole true (some ty) => mkHoleCall ty
  | .Hole true none => mkHoleCall ⟨.Top, md⟩
  | .Hole false _ => return stmt -- Non-deterministic holes are kept
  | _ => return stmt

private def elimStmtList (stmts : List StmtExprMd) : ElimHoleM (List StmtExprMd) :=
  stmts.mapM elimStmt
end

private def elimProcedure (proc : Procedure) : ElimHoleM Procedure := do
  modify fun s => { s with currentInputs := proc.inputs }
  match proc.body with
  | .Transparent bodyExpr => return { proc with body := .Transparent (← elimStmt bodyExpr) }
  | .Opaque postconds (some impl) modif =>
      return { proc with body := .Opaque postconds (some (← elimStmt impl)) modif }
  | _ => return proc

/--
Replace every deterministic `.Hole` in the program with a call to a freshly
generated uninterpreted function. Works uniformly for both procedures and
functions.
After this pass the program contains only non-deterministic `Hole` nodes.

Assumes `inferHoleTypes` has already annotated holes with types.
-/
def eliminateHoles (program : Program) : Program :=
  let initState : ElimHoleState := {}
  let (procs, finalState) := (program.staticProcedures.mapM elimProcedure).run initState
  { program with staticProcedures := finalState.generatedFunctions ++ procs }

end -- public section
end Laurel
