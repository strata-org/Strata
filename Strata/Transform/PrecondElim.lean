/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Transform.CoreTransform
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
open Core.Transform

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
def collectPrecondAsserts (F : @Lambda.Factory CoreLParams) (e : Expression.Expr)
(labelPrefix : String) (md : Imperative.MetaData Expression := .empty)
: List Statement :=
  let wfObs := Lambda.collectWFObligations F e
  wfObs.mapIdx fun idx ob =>
    Statement.assert
    s!"{labelPrefix}_calls_{ob.funcName}_{idx}" ob.obligation md

/--
Collect assertions for all expressions in a command.
-/
def collectCmdPrecondAsserts (F : @Lambda.Factory CoreLParams)
  (cmd : Imperative.Cmd Expression) : List Statement :=
  match cmd with
  | .init _ _ (some e) md => collectPrecondAsserts F e "init" md
  | .init _ _ _ _ => []
  | .set x e md => collectPrecondAsserts F e s!"set_{x.name}" md
  | .assert l e md => collectPrecondAsserts F e s!"assert_{l}" md
  | .assume l e md => collectPrecondAsserts F e s!"assume_{l}" md
  | .cover l e md => collectPrecondAsserts F e s!"cover_{l}" md
  | .havoc _ _ => []

/--
Collect assertions for call arguments.
-/
def collectCallPrecondAsserts (F : @Lambda.Factory CoreLParams) (pname : String)
  (args : List Expression.Expr) (md : Imperative.MetaData Expression := .empty)
  : List Statement :=
  args.flatMap fun arg => collectPrecondAsserts F arg s!"call_{pname}_arg" md

/-! ## Processing contract conditions -/

/--
Process a single contract condition: assert WF of partial function calls,
then assume the condition. Returns the generated statements.
-/
def processCondition (F : @Lambda.Factory CoreLParams)
    (expr : Expression.Expr) (assertLabel : String) (assumeLabel : String)
    (md : Imperative.MetaData Expression := .empty) : List Statement :=
  let asserts := collectPrecondAsserts F expr assertLabel md
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
      header := { proc.header with name := CoreIdent.unres (wfProcName name), noFilter := true }
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
    | some b => collectPrecondAsserts F b s!"{funcName}_body"
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
        noFilter := true
      }
      spec := { modifies := [], preconditions := [], postconditions := [] }
      body := wfStmts
    })

/-! ## Statement transformation -/

mutual
/-- Eliminate function preconditions from blocks. -/
def transformStmts (ss : List Statement)
    : CoreTransformM (Bool × List Statement) :=
  match ss with
  | [] => return (false, [])
  | s :: rest => do
    let (changed, s') ← transformStmt s
    let (changed', rest') ← transformStmts rest
    return (changed || changed', s' ++ rest')
  termination_by Imperative.Block.sizeOf ss
  decreasing_by all_goals term_by_mem

/-- Eliminate function preconditions from statement, adding assertions
  at call sites (including in existing assertions and loop invariants).
  Function declaration statements produce a well-formedness check block
  mirroring the procedure created for top-level functions. -/
def transformStmt (s : Statement)
    : CoreTransformM (Bool × List Statement) := do
  let F ← getFactory
  match s with
  | .cmd (.cmd c) =>
    let asserts := collectCmdPrecondAsserts F c
    return (!asserts.isEmpty, asserts ++ [.cmd (.cmd c)])
  | .cmd (.call lhs pname args md) =>
    let asserts := collectCallPrecondAsserts F pname args md
    return (!asserts.isEmpty, asserts ++ [.call lhs pname args md])
  | .block lbl b md => do
    let savedF ← getFactory
    let (changed, b') ← transformStmts b
    setFactory savedF
    return (changed, [.block lbl b' md])
  | .ite c thenb elseb md => do
    let savedF ← getFactory
    let (changed, thenb') ← transformStmts thenb
    setFactory savedF
    let (changed', elseb') ← transformStmts elseb
    setFactory savedF
    return (changed || changed', [.ite c thenb' elseb' md])
  | .loop guard measure invariant body md => do
    let invAsserts := invariant.flatMap (fun inv => collectPrecondAsserts F inv "loop_invariant" md)
    let guardAsserts := collectPrecondAsserts F guard "loop_guard" md
    let savedF ← getFactory
    let (changed, body') ← transformStmts body
    setFactory savedF
    return (changed || !invAsserts.isEmpty || !guardAsserts.isEmpty,
      guardAsserts ++ invAsserts ++ [.loop guard measure invariant body' md])
  | .goto lbl md =>
    return (false, [.goto lbl md])
  | .funcDecl decl md => do
    let funcName := decl.name.name
    -- Add function to factory before processing its preconditions/body
    let func ← liftDiag ((Function.ofPureFunc decl).mapError DiagnosticModel.fromFormat)
    let F' := F.push func
    setFactory F'
    let decl' := { decl with preconditions := [] }
    let hasPreconds := !decl.preconditions.isEmpty
    match mkFuncWFStmts F' funcName decl.preconditions decl.body with
    | none => return (hasPreconds, [.funcDecl decl' md])
    | some wfStmts =>
      -- Add init statements for function parameters so they're in scope
      let paramInits := decl.inputs.toList.map fun (name, ty) =>
        Statement.init name ty none md
      return (hasPreconds, [.block s!"{funcName}{wfSuffix}" (paramInits ++ wfStmts) md, .funcDecl decl' md])
  termination_by s.sizeOf
  decreasing_by all_goals term_by_mem
end

/-! ## Main transformation -/

/--
Transform an entire program:
1. For each procedure, transform its body and if needed generate a WF procedure
2. For each function, strip preconditions and if needed generate a WF procedure
3. For each function call, assert that the preconditions hold

Returns (changed, transformed program).
-/
def precondElim (p : Program) (F : @Lambda.Factory CoreLParams)
    : CoreTransformM (Bool × Program) := do
  setFactory F
  let (changed, newDecls) ← transformDecls p.decls
  return (changed, { decls := newDecls })
where
  transformDecls (decls : List Decl)
      : CoreTransformM (Bool × List Decl) := do
    match decls with
    | [] => return (false, [])
    | d :: rest =>
      match d with
      | .proc proc md => do
        let F ← getFactory
        let (changed, body') ← transformStmts proc.body
        setFactory F
        let proc' := { proc with body := body' }
        let procDecl := Decl.proc proc' md
        let (changed', rest') ← transformDecls rest
        match mkContractWFProc F proc with
        | some wfDecl => return (true, wfDecl :: procDecl :: rest')
        | none => return (changed || changed', procDecl :: rest')
      | .func func md => do
        let F ← getFactory
        let F' := F.push func
        setFactory F'
        let func' := { func with preconditions := [] }
        let funcDecl := Decl.func func' md
        let hasPreconds := !func.preconditions.isEmpty
        let (changed, rest') ← transformDecls rest
        match mkFuncWFProc F' func with
        | some wfDecl => return (true, wfDecl :: funcDecl :: rest')
        | none => return (changed || hasPreconds, funcDecl :: rest')
      | .type (.data block) _ => do
        let F ← getFactory
        let bf ← liftDiag (Lambda.genBlockFactory (T := CoreLParams) block)
        let F' ← liftDiag (F.addFactory bf)
        setFactory F'
        let (changed, rest') ← transformDecls rest
        return (changed, d :: rest')
      | _ => do
        let (changed, rest') ← transformDecls rest
        return (changed, d :: rest')

end PrecondElim
end Core
