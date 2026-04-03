/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Env

/-! # Expression Deduplication

A Core-to-Core transformation that extracts common subexpressions into fresh
variable definitions. This reduces duplication that arises from partial
evaluation inlining variable assignments.

## Overview

After partial evaluation, expressions may contain repeated subexpressions.
For example:
```
assume F(2+z) >= 5
assert F(2+z)+F(2+z) == 2*F(2+z)
```

This pass normalizes such programs by hoisting common subexpressions into
`var` declarations:
```
var $__dedup_0 := F(2+z)
assume $__dedup_0 >= 5
assert $__dedup_0+$__dedup_0 == 2*$__dedup_0
```

This is the second phase described in issue #749: after partial evaluation
produces a Core program with inlined expressions, deduplication normalizes
the result by factoring out common subexpressions.

## Design

The deduplication operates on two levels:

1. **Proof obligation level**: `deduplicateObligation` extracts common
   subexpressions from a single proof obligation's assumptions and obligation
   expression, introducing fresh variables as equality assumptions.

2. **Program level**: `deduplicateProgram` walks procedure bodies and extracts
   common subexpressions into `var` declarations prepended to the body.

The program-level deduplication prepares for the future separation of proof
obligation emission (issue #475), where the deduplicated program will be
the input to a simple 1-1 SMT emitter.
-/

public section

namespace Core.Deduplication

open Lambda Imperative

/-- Check if an expression is a leaf node that should not be deduplicated. -/
private def isTrivial (e : Expression.Expr) : Bool :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => true
  | _ => false

/-- Check if an expression contains bound variables, which would make
    deduplication unsound across different binding contexts. -/
partial def hasBVar (e : Expression.Expr) : Bool :=
  match e with
  | .bvar _ _ => true
  | .const _ _ | .fvar _ _ _ | .op _ _ _ => false
  | .app _ fn arg => hasBVar fn || hasBVar arg
  | .ite _ c t f => hasBVar c || hasBVar t || hasBVar f
  | .eq _ e1 e2 => hasBVar e1 || hasBVar e2
  | .abs _ _ _ body => hasBVar body
  | .quant _ _ _ _ tr body => hasBVar tr || hasBVar body

/-- Collect the head function and arguments of a curried application spine. -/
private partial def uncurry (e : Expression.Expr) : Expression.Expr × List Expression.Expr :=
  match e with
  | .app _ fn arg =>
    let (head, args) := uncurry fn
    (head, args ++ [arg])
  | other => (other, [])

/-- Collect non-trivial subexpressions from an expression, suitable for
    deduplication. For function applications, collects the full (curried)
    application and recurses into each argument, but does not collect
    intermediate partial applications from the spine. -/
partial def collectSubexprs (e : Expression.Expr) : List Expression.Expr :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => []
  | .app _ _ _ =>
    let (_, args) := uncurry e
    [e] ++ args.flatMap collectSubexprs
  | .ite _ c t f =>
    [e] ++ collectSubexprs c ++ collectSubexprs t ++ collectSubexprs f
  | .eq _ e1 e2 =>
    [e] ++ collectSubexprs e1 ++ collectSubexprs e2
  | .abs _ _ _ _ => []
  | .quant _ _ _ _ _ _ => []

/-- Find expressions that appear more than once in a list. Uses type-erased
    comparison to ignore type annotations that may differ between occurrences. -/
private def findDuplicates (exprs : List Expression.Expr) : List Expression.Expr :=
  go exprs [] []
where
  go : List Expression.Expr → List Expression.Expr → List Expression.Expr → List Expression.Expr
  | [], _, dups => dups.reverse
  | e :: rest, seen, dups =>
    let eErased := e.eraseTypes
    if seen.any (· == eErased) then
      if dups.any (fun d => d.eraseTypes == eErased) then go rest seen dups
      else go rest seen (e :: dups)
    else go rest (eErased :: seen) dups

/-- Replace all occurrences of `target` (compared with erased types) with
    `replacement` in an expression. -/
partial def replaceExpr (target replacement : Expression.Expr)
    (e : Expression.Expr) : Expression.Expr :=
  if e.eraseTypes == target.eraseTypes then replacement
  else match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => e
  | .app m fn arg =>
    .app m (replaceExpr target replacement fn) (replaceExpr target replacement arg)
  | .ite m c t f =>
    .ite m (replaceExpr target replacement c) (replaceExpr target replacement t)
           (replaceExpr target replacement f)
  | .eq m e1 e2 =>
    .eq m (replaceExpr target replacement e1) (replaceExpr target replacement e2)
  | .abs m name ty body =>
    .abs m name ty (replaceExpr target replacement body)
  | .quant m k name ty tr body =>
    .quant m k name ty (replaceExpr target replacement tr)
                       (replaceExpr target replacement body)

/-- Get the type annotation from an expression, if available. -/
private partial def getExprType? (e : Expression.Expr) : Option LMonoTy :=
  match e with
  | .fvar _ _ ty => ty
  | .op _ _ ty => ty
  | .const _ c => some c.ty
  | .eq _ _ _ => some .bool
  | .ite _ _ t _ => getExprType? t
  | .app _ fn _ =>
    match getExprType? fn with
    | some (.tcons "arrow" [_, ret]) => some ret
    | _ => none
  | _ => none

/-- Compute the size of an expression (number of nodes). -/
private def exprSize : Expression.Expr → Nat
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => 1
  | .app _ fn arg => 1 + exprSize fn + exprSize arg
  | .ite _ c t f => 1 + exprSize c + exprSize t + exprSize f
  | .eq _ e1 e2 => 1 + exprSize e1 + exprSize e2
  | .abs _ _ _ body => 1 + exprSize body
  | .quant _ _ _ _ tr body => 1 + exprSize tr + exprSize body

/-- Check if `sub` is a subexpression of `e` (type-erased comparison). -/
private partial def isSubexprOf (sub e : Expression.Expr) : Bool :=
  if sub.eraseTypes == e.eraseTypes then true
  else match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => false
  | .app _ fn arg => isSubexprOf sub fn || isSubexprOf sub arg
  | .ite _ c t f => isSubexprOf sub c || isSubexprOf sub t || isSubexprOf sub f
  | .eq _ e1 e2 => isSubexprOf sub e1 || isSubexprOf sub e2
  | .abs _ _ _ body => isSubexprOf sub body
  | .quant _ _ _ _ tr body => isSubexprOf sub tr || isSubexprOf sub body

/-- Remove entries that are subexpressions of other entries in the list. -/
private def removeSubsumed (exprs : List Expression.Expr) : List Expression.Expr :=
  exprs.filter (fun e =>
    !exprs.any (fun other =>
      exprSize other > exprSize e && isSubexprOf e other))

---------------------------------------------------------------------
-- Proof obligation level deduplication
---------------------------------------------------------------------

/-- Collect subexpressions from all expressions in a proof obligation. -/
private def collectFromObligation (ob : ProofObligation Expression) : List Expression.Expr :=
  let assumptionExprs := ob.assumptions.flatMap (·.map (·.snd))
  let allExprs := assumptionExprs ++ [ob.obligation]
  allExprs.flatMap collectSubexprs

/-- Deduplicate a single proof obligation by extracting common subexpressions
    into fresh variable definitions added as equality assumptions. -/
def deduplicateObligation (ob : ProofObligation Expression) (startIdx : Nat) :
    ProofObligation Expression × Nat :=
  let allSubexprs := collectFromObligation ob
  let candidates := allSubexprs.filter (fun e => !isTrivial e && !hasBVar e)
  let duplicates := findDuplicates candidates
  let duplicates := removeSubsumed duplicates
  let sorted := duplicates.mergeSort (fun a b => exprSize a > exprSize b)
  let (ob', nextIdx) := sorted.foldl (fun (ob, idx) dup =>
    let freshName : CoreIdent := ⟨s!"$__dedup_{idx}", ()⟩
    let freshTy := getExprType? dup
    let freshVar : Expression.Expr := .fvar () freshName freshTy
    let obligation' := replaceExpr dup freshVar ob.obligation
    let assumptions' := ob.assumptions.map (fun pc =>
      pc.map (fun (label, expr) => (label, replaceExpr dup freshVar expr)))
    let defLabel := s!"$__dedup_def_{idx}"
    let defExpr : Expression.Expr := .eq () freshVar dup
    let assumptions'' := match assumptions' with
      | [] => [[(defLabel, defExpr)]]
      | outerScope :: rest => ((defLabel, defExpr) :: outerScope) :: rest
    ({ ob with obligation := obligation', assumptions := assumptions'' }, idx + 1)
  ) (ob, startIdx)
  (ob', nextIdx)

---------------------------------------------------------------------
-- Program level deduplication
---------------------------------------------------------------------

/-- Collect all expressions from a list of statements. -/
private partial def collectFromStatements : Statements → List Expression.Expr
  | [] => []
  | s :: rest => collectFromStatement s ++ collectFromStatements rest
where
  collectFromStatement : Statement → List Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => collectSubexprs e
  | .cmd (.cmd (.assume _ e _)) => collectSubexprs e
  | .cmd (.cmd (.cover _ e _)) => collectSubexprs e
  | .cmd (.cmd (.init _ _ (.det e) _)) => collectSubexprs e
  | .cmd (.cmd (.set _ (.det e) _)) => collectSubexprs e
  | .cmd (.call _ _ args _) => args.flatMap collectSubexprs
  | .block _ ss _ => collectFromStatements ss
  | .ite (.det c) tss ess _ =>
    collectSubexprs c ++ collectFromStatements tss ++ collectFromStatements ess
  | .ite .nondet tss ess _ =>
    collectFromStatements tss ++ collectFromStatements ess
  | _ => []

/-- Replace an expression in all statements. -/
private partial def replaceInStatements (target replacement : Expression.Expr) :
    Statements → Statements
  | [] => []
  | s :: rest => replaceInStatement target replacement s :: replaceInStatements target replacement rest
where
  replaceInStatement (target replacement : Expression.Expr) : Statement → Statement
  | .cmd (.cmd (.assert l e md)) =>
    .cmd (.cmd (.assert l (replaceExpr target replacement e) md))
  | .cmd (.cmd (.assume l e md)) =>
    .cmd (.cmd (.assume l (replaceExpr target replacement e) md))
  | .cmd (.cmd (.cover l e md)) =>
    .cmd (.cmd (.cover l (replaceExpr target replacement e) md))
  | .cmd (.cmd (.init n ty (.det e) md)) =>
    .cmd (.cmd (.init n ty (.det (replaceExpr target replacement e)) md))
  | .cmd (.cmd (.set n (.det e) md)) =>
    .cmd (.cmd (.set n (.det (replaceExpr target replacement e)) md))
  | .cmd (.call lhs pname args md) =>
    .cmd (.call lhs pname (args.map (replaceExpr target replacement)) md)
  | .block l ss md =>
    .block l (replaceInStatements target replacement ss) md
  | .ite (.det c) tss ess md =>
    .ite (.det (replaceExpr target replacement c))
         (replaceInStatements target replacement tss)
         (replaceInStatements target replacement ess) md
  | .ite .nondet tss ess md =>
    .ite .nondet
         (replaceInStatements target replacement tss)
         (replaceInStatements target replacement ess) md
  | other => other

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index. -/
def deduplicateBody (body : Statements) (startIdx : Nat) : Statements × Nat :=
  let allSubexprs := collectFromStatements body
  let candidates := allSubexprs.filter (fun e => !isTrivial e && !hasBVar e)
  let duplicates := findDuplicates candidates
  let duplicates := removeSubsumed duplicates
  let sorted := duplicates.mergeSort (fun a b => exprSize a > exprSize b)
  let (varDecls, body', nextIdx) := sorted.foldl (fun (decls, body, idx) dup =>
    let freshName : CoreIdent := ⟨s!"$__dedup_{idx}", ()⟩
    let freshTy := getExprType? dup
    let freshVar : Expression.Expr := .fvar () freshName freshTy
    let ty : Expression.Ty := match freshTy with
      | some mty => LTy.forAll [] mty
      | none => LTy.forAll ["α"] (.ftvar "α")
    let varDecl := Statement.init freshName ty (.det dup) .empty
    let body' := replaceInStatements dup freshVar body
    (decls ++ [varDecl], body', idx + 1)
  ) ([], body, startIdx)
  (varDecls ++ body', nextIdx)

/-- Deduplicate all procedures in a program. -/
def deduplicateProgram (p : Program) : Program :=
  let (decls, _) := p.decls.foldl (fun (acc, idx) decl =>
    match decl with
    | .proc proc md =>
      let (body', idx') := deduplicateBody proc.body idx
      (acc ++ [.proc { proc with body := body' } md], idx')
    | other => (acc ++ [other], idx)
  ) ([], 0)
  { decls }

end Core.Deduplication

end -- public section
