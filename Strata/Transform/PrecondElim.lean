/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.DL.Lambda.Preconditions

/-! # Partial Function Precondition Elimination

This transformation eliminates partial function preconditions by inserting
explicit `assert` statements wherever a function with a precondition is called.

For procedure bodies: each command's expressions are scanned for calls to
partial functions, and `assert` statements are inserted before the command.

For procedure contracts: a separate well-formedness checking procedure is
generated that asserts preconditions hold, assuming earlier contract clauses.

For function declarations: a well-formedness checking procedure is generated
that asserts preconditions of any partial function calls within the function's
own preconditions and body.

After transformation, the returned Factory has all preconditions stripped,
so downstream VCG sees only total functions.
-/

namespace Core
namespace PrecondElim

open Lambda

/-! ## Naming conventions -/

/-- Suffix for generated well-formedness procedures. Change here to rename everywhere. -/
def wfSuffix : String := "$$wf"

def wfProcName (name : String) : String := s!"{name}{wfSuffix}"

/-! ## Collecting assertions from expressions -/

/--
Given a Factory and an expression, collect all partial function call
precondition obligations and return them as `assert` statements.
-/
def collectAsserts (F : @Lambda.Factory CoreLParams) (e : Expression.Expr) (labelPrefix : String)
    : List Statement :=
  let wfObs := Lambda.collectWFObligations F e
  wfObs.mapIdx fun idx ob =>
    Statement.assert s!"{labelPrefix}_calls_{ob.funcName}_{idx}" ob.obligation

/--
Collect assertions for all expressions in a command.
-/
def collectCmdAsserts (F : @Lambda.Factory CoreLParams) (cmd : Imperative.Cmd Expression)
    : List Statement :=
  match cmd with
  | .init _ _ e _ => collectAsserts F e "init"
  | .set x e _ => collectAsserts F e s!"set_{x.name}"
  | .assert l e _ => collectAsserts F e s!"assert_{l}"
  | .assume l e _ => collectAsserts F e s!"assume_{l}"
  | .cover l e _ => collectAsserts F e s!"cover_{l}"
  | .havoc _ _ => []

/--
Collect assertions for call arguments.
-/
def collectCallAsserts (F : @Lambda.Factory CoreLParams) (pname : String) (args : List Expression.Expr)
    : List Statement :=
  args.flatMap fun arg =>
    collectAsserts F arg s!"call_{pname}_arg"

/-! ## Contract well-formedness procedures -/

/--
Generate a well-formedness checking procedure for a procedure's contract.

For each precondition (in order):
  - Assert WF of partial function calls in the precondition
  - Assume the precondition (for use by subsequent clauses)

For each postcondition (in order):
  - Assert WF of partial function calls in the postcondition
  - Assume the postcondition
-/
def mkContractWFProc (F : @Lambda.Factory CoreLParams) (proc : Procedure) : Option Decl :=
  let precondAsserts := proc.spec.preconditions.flatMap fun (label, check) =>
    let asserts := collectAsserts F check.expr s!"{proc.header.name.name}_pre_{label}"
    let assume := Statement.assume label check.expr
    asserts ++ [assume]
  let postcondAsserts := proc.spec.postconditions.flatMap fun (label, check) =>
    let asserts := collectAsserts F check.expr s!"{proc.header.name.name}_post_{label}"
    let assume := Statement.assume label check.expr
    asserts ++ [assume]
  let body := precondAsserts ++ postcondAsserts
  if body.any (fun s => match s with | .assert _ _ _ => true | _ => false) then
    some <| .proc {
      header := { proc.header with name := CoreIdent.unres (wfProcName proc.header.name.name) }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := body
    }
  else
    none

/-! ## Function well-formedness procedures -/

/--
Generate a well-formedness checking procedure for a function declaration.

For each precondition (in order):
  - Assert WF of partial function calls in the precondition
  - Assume the precondition

For the body (if present):
  - Assume all preconditions
  - Assert WF of partial function calls in the body
-/
def mkFuncWFProc (F : @Lambda.Factory CoreLParams) (func : Function) : Option Decl :=
  let funcName := func.name.name
  let (precondStmts, _) := func.preconditions.foldl (fun (stmts, idx) precond =>
    let asserts := collectAsserts F precond s!"{funcName}_precond"
    let assume := Statement.assume s!"precond_{funcName}_{idx}" precond
    (stmts ++ asserts ++ [assume], idx + 1)) ([], 0)
  let bodyStmts := match func.body with
    | none => []
    | some body => collectAsserts F body s!"{funcName}_body"
  let allStmts := precondStmts ++ bodyStmts
  if allStmts.any (fun s => match s with | .assert _ _ _ => true | _ => false) then
    some <| .proc {
      header := {
        name := CoreIdent.unres (wfProcName funcName)
        typeArgs := func.typeArgs
        inputs := func.inputs
        outputs := []
      }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := allStmts
    }
  else
    none

/-! ## Statement transformation -/

mutual
def transformStmts (F : @Lambda.Factory CoreLParams) (ss : List Statement)
    : List Statement :=
  match ss with
  | [] => []
  | s :: rest => transformStmt F s ++ transformStmts F rest
  termination_by Imperative.Block.sizeOf ss
  decreasing_by all_goals (simp_wf; omega)

def transformStmt (F : @Lambda.Factory CoreLParams) (s : Statement)
    : List Statement :=
  match s with
  | .cmd (.cmd c) =>
    collectCmdAsserts F c ++ [.cmd (.cmd c)]
  | .cmd (.call lhs pname args md) =>
    collectCallAsserts F pname args ++ [.call lhs pname args md]
  | .block lbl b md =>
    [.block lbl (transformStmts F b) md]
  | .ite c thenb elseb md =>
    [.ite c (transformStmts F thenb) (transformStmts F elseb) md]
  | .loop guard measure invariant body md =>
    let invAsserts := match invariant with
      | some inv => collectAsserts F inv "loop_invariant"
      | none => []
    let guardAsserts := collectAsserts F guard "loop_guard"
    guardAsserts ++ invAsserts ++ [.loop guard measure invariant (transformStmts F body) md]
  | .goto lbl md =>
    [.goto lbl md]
  -- TODO: Generate well-formedness checks for funcDecl preconditions
  -- (similar to mkFuncWFProc but as blocks preceding the funcDecl statement)
  | .funcDecl decl md =>
    let decl' := { decl with preconditions := [] }
    [.funcDecl decl' md]
  termination_by s.sizeOf
  decreasing_by all_goals (simp_wf; try omega)
end

/-! ## Factory stripping -/

def stripPreconditions (F : @Lambda.Factory CoreLParams) : @Lambda.Factory CoreLParams :=
  F.map fun func => { func with preconditions := [] }

/-! ## Main transformation -/

/--
Transform an entire program:
1. For each procedure, transform its body and optionally generate a WF procedure
2. For each function, strip preconditions and optionally generate a WF procedure
3. Strip preconditions from all functions in the returned Factory

Returns the transformed program and a Factory with preconditions removed.
-/
def precondElim (p : Program) (F : @Lambda.Factory CoreLParams)
    : Program × @Lambda.Factory CoreLParams :=
  let newDecls := transformDecls F p.decls
  ({ decls := newDecls }, stripPreconditions F)
where
  transformDecls (F : @Lambda.Factory CoreLParams) (decls : List Decl)
      : List Decl :=
    match decls with
    | [] => []
    | d :: rest =>
      let rest' := transformDecls F rest
      match d with
      | .proc proc md =>
        let body' := transformStmts F proc.body
        let proc' := { proc with body := body' }
        let procDecl := Decl.proc proc' md
        match mkContractWFProc F proc with
        | some wfDecl => wfDecl :: procDecl :: rest'
        | none => procDecl :: rest'
      | .func func md =>
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        match mkFuncWFProc F func with
        | some wfDecl => wfDecl :: funcDecl :: rest'
        | none => funcDecl :: rest'
      | _ => d :: rest'

end PrecondElim
end Core
