/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Program
import Strata.DL.Lambda.Preconditions
import Strata.DL.Lambda.TypeFactory

/-! # Partial Function Precondition Elimination

This transformation eliminates function preconditions.

In particular, it does the following:
1. For every call to a function with a precondition, it inserts an `assert` at
the call site.
2. For every function and procedure contract, it generates a well-formedness
check asserting that all calls to functions preconditions within the contract
hold, assuming earlier calls succeed.
3. For function declarations, the well-formedness check also asserts the
preconditions of any partial functions called within the body.
4. The returned program consists only of total functions (no preconditions).

See StrataTest/Transform/PrecondElim.lean for examples.

Note that this transformation must be called BEFORE typechecking, since
in the presence of polymorphic preconditions, the resulting assertions
have type variables that must be unified.
-/

namespace Core
namespace PrecondElim

open Lambda
open Strata (DiagnosticModel)

/-! ## Naming conventions -/

/-- Suffix for generated well-formedness procedures. -/
def wfSuffix : String := "$$wf"

def wfProcName (name : String) : String := s!"{name}{wfSuffix}"

/-! ## Collecting assertions from expressions -/

/--
Given a Factory and an expression, collect all partial function call
precondition obligations and return them as `assert` statements.
The metadata from the original statement is attached to the generated assertions.
-/
def collectAsserts (F : @Lambda.Factory CoreLParams) (e : Expression.Expr)
(labelPrefix : String) (md : Imperative.MetaData Expression := .empty)
: List Statement :=
  let wfObs := Lambda.collectWFObligations F e
  wfObs.mapIdx fun idx ob =>
    Statement.assert
    s!"{labelPrefix}_calls_{ob.funcName}_{idx}" ob.obligation md

/--
Collect assertions for all expressions in a command.
-/
def collectCmdAsserts (F : @Lambda.Factory CoreLParams)
  (cmd : Imperative.Cmd Expression) : List Statement :=
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
def collectCallAsserts (F : @Lambda.Factory CoreLParams) (pname : String)
  (args : List Expression.Expr) (md : Imperative.MetaData Expression := .empty)
  : List Statement :=
  args.flatMap fun arg => collectAsserts F arg s!"call_{pname}_arg" md

/-! ## Processing contract conditions -/

/--
Process a single contract condition: assert WF of partial function calls,
then assume the condition. Returns the generated statements.
-/
def processCondition (F : @Lambda.Factory CoreLParams)
    (expr : Expression.Expr) (assertLabel : String) (assumeLabel : String)
    (md : Imperative.MetaData Expression := .empty) : List Statement :=
  let asserts := collectAsserts F expr assertLabel md
  let assume := Statement.assume assumeLabel expr md
  asserts ++ [assume]

/-- Returns true if any statement in the list is an assert. -/
private def hasAssert (stmts : List Statement) : Bool :=
  stmts.any (fun s => match s with | .assert _ _ _ => true | _ => false)

/-! ## Contract well-formedness procedures -/

/--
Generate a well-formedness checking procedure for a procedure's contract.

For each precondition+postcondition (in order):
  - Assert WF of partial function calls in the condition
  - Assume the condition (for use by subsequent clauses)
-/
def mkContractWFProc (F : @Lambda.Factory CoreLParams) (proc : Procedure)
: Option Decl :=
  let name := proc.header.name.name
  let precondStmts := proc.spec.preconditions.flatMap fun (label, check) =>
    processCondition F check.expr s!"{name}_pre_{label}" label check.md
  let postcondStmts := proc.spec.postconditions.flatMap fun (label, check) =>
    processCondition F check.expr s!"{name}_post_{label}" label check.md
  let body := precondStmts ++ postcondStmts
  if hasAssert body then
    some <| .proc {
      header := { proc.header with name := CoreIdent.unres (wfProcName name) }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := body
    }
  else
    none

/-! ## Function well-formedness generation -/

/--
Generate the well-formedness checking statements for a function's preconditions
and body. This is shared between top-level function declarations and inline
function declarations.

For each precondition (in order):
  - Assert WF of partial function calls in the precondition
  - Assume the precondition

For the body (if present):
  - Assert WF of partial function calls in the body

Returns `none` if no assertions are generated, otherwise `some stmts`.
-/
def mkFuncWFStmts (F : @Lambda.Factory CoreLParams) (funcName : String)
    (preconditions : List (Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata))
    (body : Option Expression.Expr) : Option (List Statement) :=
  let (precondStmts, _) := preconditions.foldl (fun (stmts, idx) precond =>
    let stmts' := processCondition F precond.expr
      s!"{funcName}_precond" s!"precond_{funcName}_{idx}"
    (stmts ++ stmts', idx + 1)) ([], 0)
  let bodyStmts := match body with
    | none => []
    | some b => collectAsserts F b s!"{funcName}_body"
  let allStmts := precondStmts ++ bodyStmts
  if hasAssert allStmts then
    some allStmts
  else
    none

/--
Generate a well-formedness checking procedure for a top-level function declaration.
-/
def mkFuncWFProc (F : @Lambda.Factory CoreLParams) (func : Function) : Option Decl :=
  let funcName := func.name.name
  (mkFuncWFStmts F funcName func.preconditions func.body).bind
  (fun wfStmts =>
    some <| .proc {
      header := {
        name := CoreIdent.unres (wfProcName funcName)
        typeArgs := func.typeArgs
        inputs := func.inputs
        outputs := []
      }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := wfStmts
    })

/-! ## Statement transformation -/

mutual
/-- Eliminate function preconditions from blocks.  -/
def transformStmts (F : @Lambda.Factory CoreLParams) (ss : List Statement)
    : Except DiagnosticModel (List Statement × @Lambda.Factory CoreLParams) :=
  match ss with
  | [] => .ok ([], F)
  | s :: rest => do
    let (s', F') ← transformStmt F s
    let (rest', F'') ← transformStmts F' rest
    .ok (s' ++ rest', F'')
  termination_by Imperative.Block.sizeOf ss
  decreasing_by all_goals (simp_wf; omega)

/-- Eliminate function preconditions from statement, adding assertions
  at call sites (including in existing assertions and loop invariants).
  Function declaration statements produce a well-formedness check block
  mirroring the procedure created for top-level functions. -/
def transformStmt (F : @Lambda.Factory CoreLParams) (s : Statement)
    : Except DiagnosticModel (List Statement × @Lambda.Factory CoreLParams) :=
  match s with
  | .cmd (.cmd c) =>
    .ok (collectCmdAsserts F c ++ [.cmd (.cmd c)], F)
  | .cmd (.call lhs pname args md) =>
    .ok (collectCallAsserts F pname args md ++ [.call lhs pname args md], F)
  | .block lbl b md => do
    let (b', _) ← transformStmts F b
    .ok ([.block lbl b' md], F)
  | .ite c thenb elseb md => do
    let (thenb', _) ← transformStmts F thenb
    let (elseb', _) ← transformStmts F elseb
    .ok ([.ite c thenb' elseb' md], F)
  | .loop guard measure invariant body md => do
    let invAsserts := match invariant with
      | some inv => collectAsserts F inv "loop_invariant" md
      | none => []
    let guardAsserts := collectAsserts F guard "loop_guard" md
    let (body', _) ← transformStmts F body
    .ok (guardAsserts ++ invAsserts ++ [.loop guard measure invariant body' md], F)
  | .goto lbl md =>
    .ok ([.goto lbl md], F)
  | .funcDecl decl md => do
    let funcName := decl.name.name
    -- Add function to factory before processing its preconditions/body
    let func ← (Function.ofPureFunc decl).mapError DiagnosticModel.fromFormat
    let F' := F.push func
    let decl' := { decl with preconditions := [] }
    match mkFuncWFStmts F' funcName decl.preconditions decl.body with
    | none => .ok ([.funcDecl decl' md], F')
    | some wfStmts =>
      -- Add init statements for function parameters so they're in scope
      let paramInits := decl.inputs.toList.map fun (name, ty) =>
        Statement.init name ty (.fvar () (CoreIdent.unres ("init_" ++ name.name)) none)
      .ok ([.block s!"{funcName}{wfSuffix}" (paramInits ++ wfStmts), .funcDecl decl' md], F')
  termination_by s.sizeOf
  decreasing_by all_goals (simp_wf; try omega)
end

/-! ## Main transformation -/

/--
Transform an entire program:
1. For each procedure, transform its body and if needed generate a WF procedure
2. For each function, strip preconditions and if needed generate a WF procedure
3. For each function call, assert that the preconditions hold

Returns the transformed program.
-/
def precondElim (p : Program) (F : @Lambda.Factory CoreLParams)
    : Except DiagnosticModel Program := do
  let (newDecls, _) ← transformDecls F p.decls
  return { decls := newDecls }
where
  transformDecls (F : @Lambda.Factory CoreLParams) (decls : List Decl)
      : Except DiagnosticModel (List Decl × @Lambda.Factory CoreLParams) := do
    match decls with
    | [] => return ([], F)
    | d :: rest =>
      match d with
      | .proc proc md =>
        let (body', _) ← transformStmts F proc.body
        let proc' := { proc with body := body' }
        let procDecl := Decl.proc proc' md
        let (rest', F') ← transformDecls F rest
        match mkContractWFProc F proc with
        | some wfDecl => return (wfDecl :: procDecl :: rest', F')
        | none => return (procDecl :: rest', F')
      | .func func md =>
        let F' := F.push func
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        let (rest', F'') ← transformDecls F' rest
        match mkFuncWFProc F' func with
        | some wfDecl => return (wfDecl :: funcDecl :: rest', F'')
        | none => return (funcDecl :: rest', F'')
      | .type (.data block) _ =>
        let bf ← Lambda.genBlockFactory (T := CoreLParams) block
        let F' ← F.addFactory bf
        let (rest', F'') ← transformDecls F' rest
        return (d :: rest', F'')
      | _ =>
        let (rest', F') ← transformDecls F rest
        return (d :: rest', F')

end PrecondElim
end Core
