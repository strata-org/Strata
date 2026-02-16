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
The metadata from the original statement is attached to the generated assertions.
-/
def collectAsserts (F : @Lambda.Factory CoreLParams) (e : Expression.Expr) (labelPrefix : String)
    (md : Imperative.MetaData Expression := .empty) : List Statement :=
  let wfObs := Lambda.collectWFObligations F e
  wfObs.mapIdx fun idx ob =>
    Statement.assert s!"{labelPrefix}_calls_{ob.funcName}_{idx}" ob.obligation md

/--
Collect assertions for all expressions in a command.
-/
def collectCmdAsserts (F : @Lambda.Factory CoreLParams) (cmd : Imperative.Cmd Expression)
    : List Statement :=
  match cmd with
  | .init _ _ e md => collectAsserts F e "init" md
  | .set x e md => collectAsserts F e s!"set_{x.name}" md
  | .assert l e md => collectAsserts F e s!"assert_{l}" md
  | .assume l e md => collectAsserts F e s!"assume_{l}" md
  | .cover l e md => collectAsserts F e s!"cover_{l}" md
  | .havoc _ _ => []

/--
Collect assertions for call arguments.
-/
def collectCallAsserts (F : @Lambda.Factory CoreLParams) (pname : String) (args : List Expression.Expr)
    (md : Imperative.MetaData Expression := .empty) : List Statement :=
  args.flatMap fun arg =>
    collectAsserts F arg s!"call_{pname}_arg" md

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
    let asserts := collectAsserts F check.expr s!"{proc.header.name.name}_pre_{label}" check.md
    let assume := Statement.assume label check.expr check.md
    asserts ++ [assume]
  let postcondAsserts := proc.spec.postconditions.flatMap fun (label, check) =>
    let asserts := collectAsserts F check.expr s!"{proc.header.name.name}_post_{label}" check.md
    let assume := Statement.assume label check.expr check.md
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
    let asserts := collectAsserts F precond.expr s!"{funcName}_precond"
    let assume := Statement.assume s!"precond_{funcName}_{idx}" precond.expr
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

/-- Convert a PureFunc to an LFunc for adding to the factory -/
def pureFuncToLFunc (decl : Imperative.PureFunc Expression) : Function := {
  name := decl.name
  typeArgs := decl.typeArgs
  isConstr := decl.isConstr
  inputs := decl.inputs.map (fun (id, ty) => (id, Lambda.LTy.toMonoTypeUnsafe ty))
  output := Lambda.LTy.toMonoTypeUnsafe decl.output
  body := decl.body
  attr := decl.attr
  concreteEval := none
  axioms := decl.axioms
  preconditions := decl.preconditions
}

mutual
def transformStmts (F : @Lambda.Factory CoreLParams) (ss : List Statement)
    : List Statement × @Lambda.Factory CoreLParams :=
  match ss with
  | [] => ([], F)
  | s :: rest =>
    let (s', F') := transformStmt F s
    let (rest', F'') := transformStmts F' rest
    (s' ++ rest', F'')
  termination_by Imperative.Block.sizeOf ss
  decreasing_by all_goals (simp_wf; omega)

def transformStmt (F : @Lambda.Factory CoreLParams) (s : Statement)
    : List Statement × @Lambda.Factory CoreLParams :=
  match s with
  | .cmd (.cmd c) =>
    (collectCmdAsserts F c ++ [.cmd (.cmd c)], F)
  | .cmd (.call lhs pname args md) =>
    (collectCallAsserts F pname args md ++ [.call lhs pname args md], F)
  | .block lbl b md =>
    let (b', F') := transformStmts F b
    ([.block lbl b' md], F')
  | .ite c thenb elseb md =>
    let (thenb', F') := transformStmts F thenb
    let (elseb', F'') := transformStmts F' elseb
    ([.ite c thenb' elseb' md], F'')
  | .loop guard measure invariant body md =>
    let invAsserts := match invariant with
      | some inv => collectAsserts F inv "loop_invariant" md
      | none => []
    let guardAsserts := collectAsserts F guard "loop_guard" md
    let (body', F') := transformStmts F body
    (guardAsserts ++ invAsserts ++ [.loop guard measure invariant body' md], F')
  | .goto lbl md =>
    ([.goto lbl md], F)
  | .funcDecl decl md =>
    let funcName := decl.name.name
    -- Add function to factory before processing its preconditions/body
    let func := pureFuncToLFunc decl
    let F' := F.push func
    let (precondStmts, _) := decl.preconditions.foldl (fun (stmts, idx) precond =>
      let asserts := collectAsserts F' precond.expr s!"{funcName}_precond"
      let assume := Statement.assume s!"precond_{funcName}_{idx}" precond.expr
      (stmts ++ asserts ++ [assume], idx + 1)) ([], 0)
    let bodyStmts := match decl.body with
      | none => []
      | some body => collectAsserts F' body s!"{funcName}_body"
    let wfStmts := precondStmts ++ bodyStmts
    let decl' := { decl with preconditions := [] }
    let wfBlock := wfStmts.filter fun s => match s with
      | .assert _ _ _ => true | .assume _ _ _ => true | _ => false
    if wfBlock.isEmpty then
      ([.funcDecl decl' md], F')
    else
      -- Add init statements for function parameters so they're in scope
      let paramInits := decl.inputs.toList.map fun (name, ty) =>
        Statement.init name ty (.fvar () (CoreIdent.unres ("init_" ++ name.name)) none)
      ([.block s!"{funcName}{wfSuffix}" (paramInits ++ wfBlock), .funcDecl decl' md], F')
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
  let (newDecls, _) := transformDecls F p.decls
  ({ decls := newDecls }, stripPreconditions F)
where
  transformDecls (F : @Lambda.Factory CoreLParams) (decls : List Decl)
      : List Decl × @Lambda.Factory CoreLParams :=
    match decls with
    | [] => ([], F)
    | d :: rest =>
      match d with
      | .proc proc md =>
        let (body', F') := transformStmts F proc.body
        let proc' := { proc with body := body' }
        let procDecl := Decl.proc proc' md
        let (rest', F'') := transformDecls F' rest
        match mkContractWFProc F proc with
        | some wfDecl => (wfDecl :: procDecl :: rest', F'')
        | none => (procDecl :: rest', F'')
      | .func func md =>
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        let (rest', F') := transformDecls F rest
        match mkFuncWFProc F func with
        | some wfDecl => (wfDecl :: funcDecl :: rest', F')
        | none => (funcDecl :: rest', F')
      | _ =>
        let (rest', F') := transformDecls F rest
        (d :: rest', F')

end PrecondElim
end Core
