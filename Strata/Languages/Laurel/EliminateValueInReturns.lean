/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
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

/-- Rewrite a single `Return (some value)` node into the list
    `[Assign outParam value, Return none]`.
    When used with `mapStmtExprFlattenM`, these statements are flattened
    into the enclosing block rather than wrapped in a nested block. -/
private def eliminateValueReturnNode (outParam : Identifier) (stmt : StmtExprMd) : Id (List StmtExprMd) :=
  match stmt.val with
  | .Return (some value) =>
    -- Synthesized nodes use default metadata since no diagnostics should be reported on them
    let target : VariableMd := { val := .Local outParam, source := stmt.source }
    let assign : StmtExprMd := { val := .Assign [target] value, source := stmt.source }
    let ret : StmtExprMd := { val := .Return none, source := stmt.source }
    [assign, ret]
  | _ => [stmt]

/-- Check whether a statement tree contains any `Return (some _)`. -/
def hasValuedReturn (stmt : StmtExprMd) : Bool :=
  match _h : stmt.val with
  | .Return (some _) => true
  | .Block stmts _ => stmts.attach.any fun ⟨s, _⟩ => hasValuedReturn s
  | .IfThenElse _ thenBr (some elseBr) =>
    hasValuedReturn thenBr || hasValuedReturn elseBr
  | .IfThenElse _ thenBr none => hasValuedReturn thenBr
  | .While _ _ _ body _ => hasValuedReturn body
  | _ => false
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (try have := AstNode.sizeOf_val_lt stmt)
    all_goals (try term_by_mem)
    all_goals omega

/-- Apply value-return elimination to a single procedure. Rewrites `return expr`
    into `outParam := expr; return` for any procedure with exactly one output
    parameter.
    Emits an error if a valued return is used with zero or multiple output parameters. -/
def eliminateValueReturnsInProc (proc : Procedure) : Procedure :=
  match proc.outputs with
  | [outParam] =>
    let pre (_: Bool) (stmt : StmtExprMd) : Id (Option (List StmtExprMd)) :=
      match stmt.val with
      | .Return (some value) =>
        let target : VariableMd := { val := .Local outParam.name, source := stmt.source }
        let assign : StmtExprMd := { val := .Assign [target] value, source := stmt.source }
        let ret : StmtExprMd := { val := .Return none, source := stmt.source }
        some [assign, ret]
      | _ => none
    let post (_: Bool) (stmt : StmtExprMd) : Id (List StmtExprMd) := pure [stmt]
    let rewrite := mapStmtExprFlattenM (m := Id) pre post true
    match proc.body with
    | .Transparent body =>
      { proc with body := .Transparent (rewrite body) }
    | .Opaque postconds (some impl) modif =>
      { proc with body := .Opaque postconds (some (rewrite impl)) modif }
    | _ => proc
  | _ =>
  -- Procedures without any out param (void) or with multiple output
  -- cannot have return statements. This raises a Resolution error
  -- (see `Check.return` in Resolution.lean)
    proc

public section

/-- Transform a program by eliminating value returns in all imperative procedures. -/
def eliminateValueInReturnsTransform (program : Program) : Program  :=
  { program with staticProcedures := program.staticProcedures.map eliminateValueReturnsInProc }

end -- public section

/-- Pipeline pass: eliminate value returns. -/
public def eliminateValueInReturnsPass : LoweringPass where
  name := "EliminateValueInReturns"
  documentation := "Rewrites `return expr` into `outParam := expr; return` for imperative procedures that have an output parameter. This decouples the return-value assignment from the final Core translation, which no longer needs to know about output parameters when translating returns."
  run := fun p _m _ => (eliminateValueInReturnsTransform p, [], {})

end Laurel
