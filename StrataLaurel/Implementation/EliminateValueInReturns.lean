/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.LaurelAST
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import Strata.Util.Tactics

/-!
# Eliminate Values In Returns

Rewrites `return expr` into `outParam := expr; return` for imperative
(non-functional) procedures that have an output parameter.

The pass is a Laurel-to-Laurel rewrite that runs before Core translation.
It only applies to static procedures, hence LiftInstanceProcedures must
be executed before it.
-/

namespace Strata.Laurel

/-- Check whether a statement tree contains any valued return. -/
def hasValuedReturn (stmt : StmtExprMd) : Bool :=
  anyStmtExpr (fun e => match e.val with
    | .Return (_ :: _) => true
    | _ => false) stmt

private def returnTempName (i : Nat) : Identifier := mkId s!"$retVal_{i}"

/-- Apply value-return elimination to a single procedure. Rewrites `return expr`
    into `outParam := expr; return`, and `return e1, …, en` into one assignment per
    declared output followed by a valueless return.

    A multi-output return writes its values into temporaries first, so the writes are
    simultaneous: `return q, p` on outputs `(p, q)` must not read the
    already-overwritten `p`. -/
def eliminateValueReturnsInProc (proc : Procedure) : Procedure :=
  match proc.outputs with
  | [] => proc
  | outputs =>
    let pre (_: Bool) (stmt : StmtExprMd) : Id (Option (List StmtExprMd)) :=
      let src := stmt.source
      let ret : StmtExprMd := { val := .Return [], source := src }
      let assignTo (target : Identifier) (value : StmtExprMd) : StmtExprMd :=
        { val := .Assign [{ val := .Local target, source := src }] value, source := src }
      match stmt.val with
      | .Return [] => none
      | .Return [value] =>
        match outputs with
        | [outParam] => some [assignTo outParam.name value, ret]
        | _ => none
      | .Return values =>
        if values.length != outputs.length then none
        else
          let temps := (values.zipIdx).map fun (value, i) =>
            ({ val := .Assign
                 [{ val := .Declare ⟨returnTempName i, none⟩, source := src }] value,
               source := src } : StmtExprMd)
          let assigns := (outputs.zipIdx).map fun (out, i) =>
            assignTo out.name { val := .Var (.Local (returnTempName i)), source := src }
          some [{ val := .Block (temps ++ assigns ++ [ret]) none [] none, source := src }]
      | _ => none
    let post (_: Bool) (stmt : StmtExprMd) : Id (List StmtExprMd) := pure [stmt]
    let rewrite := mapStmtExprFlattenM (m := Id) pre post true
    match proc.body with
    | .Transparent body =>
      { proc with body := .Transparent (rewrite body) }
    | .Opaque postconds (some impl) modif =>
      { proc with body := .Opaque postconds (some (rewrite impl)) modif }
    | _ => proc

public section

/-- Transform a program by eliminating value returns in all imperative procedures. -/
def eliminateValueInReturnsTransform (program : Program) : Program :=
  mapProgramProcedures eliminateValueReturnsInProc program

end -- public section

/-- Pipeline pass: eliminate value returns. -/
public def eliminateValueInReturnsPass : LaurelPass where
  name := "EliminateValueInReturns"
  creates := [NodeKind.StmtExpr.Assign, NodeKind.StmtExpr.Block, NodeKind.StmtExpr.Return]
  removes := [NodeKind.StmtExpr.Return.value.some]
  unsupported := [NodeKind.CompositeType.instanceProcedures.cons]
  documentation := "Rewrites `return expr` into `outParam := expr; return` for imperative procedures that have an output parameter, and `return e1, …, en` into one assignment per declared output. This decouples the return-value assignment from the final Core translation, which no longer needs to know about output parameters when translating returns. A multi-output return parks its values in temporaries first, so the writes are simultaneous rather than sequential."
  needsResolves := true
  run := fun _ p _m => (eliminateValueInReturnsTransform p, [], {})

end Laurel
