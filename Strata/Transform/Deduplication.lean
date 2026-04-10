/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

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
var $__d.0 := F(2+z)
assume $__d.0 >= 5
assert $__d.0+$__d.0 == 2*$__d.0
```

This is the second phase described in issue #749: after partial evaluation
produces a Core program with inlined expressions, deduplication normalizes
the result by factoring out common subexpressions.

## Design

The pass operates at the program level: `deduplicateProgram` walks procedure
bodies and extracts common subexpressions into `var` declarations prepended
to the body.

After deduplication, proof obligation extraction (issue #475) becomes a simple
tree traversal that collects individual goals from `if * { } else { }` trees
— no further SMT-to-SMT optimization is needed.
-/

public section

namespace Core.Deduplication

open Lambda Imperative

---------------------------------------------------------------------
-- Expression analysis utilities
---------------------------------------------------------------------

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
private partial def uncurry (e : Expression.Expr) :
    Expression.Expr × List Expression.Expr :=
  go e []
where
  go (e : Expression.Expr) (acc : List Expression.Expr) :
      Expression.Expr × List Expression.Expr :=
    match e with
    | .app _ fn arg => go fn (arg :: acc)
    | other => (other, acc)

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
  go : List Expression.Expr → List Expression.Expr → List Expression.Expr →
       List Expression.Expr
  | [], _, dups => dups.reverse
  | e :: rest, seen, dups =>
    let eErased := e.eraseTypes
    if seen.any (· == eErased) then
      if dups.any (fun d => d.eraseTypes == eErased) then go rest seen dups
      else go rest seen (e :: dups)
    else go rest (eErased :: seen) dups

/-- Replace all occurrences of `target` (compared with erased types) with
    `replacement` in an expression. Erases `target` once upfront to avoid
    redundant traversals at each node. -/
partial def replaceExpr (target replacement : Expression.Expr)
    (e : Expression.Expr) : Expression.Expr :=
  go target.eraseTypes replacement e
where
  go (targetErased replacement : Expression.Expr)
      (e : Expression.Expr) : Expression.Expr :=
    if e.eraseTypes == targetErased then replacement
    else match e with
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => e
    | .app m fn arg =>
      .app m (go targetErased replacement fn)
             (go targetErased replacement arg)
    | .ite m c t f =>
      .ite m (go targetErased replacement c)
             (go targetErased replacement t)
             (go targetErased replacement f)
    | .eq m e1 e2 =>
      .eq m (go targetErased replacement e1)
            (go targetErased replacement e2)
    | .abs m name ty body =>
      .abs m name ty (go targetErased replacement body)
    | .quant m k name ty tr body =>
      .quant m k name ty (go targetErased replacement tr)
                         (go targetErased replacement body)

/-- Get the type annotation from an expression, if available. -/
private def getExprType? : Expression.Expr → Option LMonoTy
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
  go sub.eraseTypes e
where
  go (subErased : Expression.Expr) (e : Expression.Expr) : Bool :=
    if e.eraseTypes == subErased then true
    else match e with
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => false
    | .app _ fn arg => go subErased fn || go subErased arg
    | .ite _ c t f =>
      go subErased c || go subErased t || go subErased f
    | .eq _ e1 e2 => go subErased e1 || go subErased e2
    | .abs _ _ _ body => go subErased body
    | .quant _ _ _ _ tr body =>
      go subErased tr || go subErased body

/-- Remove entries that are subexpressions of other entries in the list. -/
private def removeSubsumed (exprs : List Expression.Expr) : List Expression.Expr :=
  exprs.filter (fun e =>
    !exprs.any (fun other =>
      exprSize other > exprSize e && isSubexprOf e other))

/-- Shared pipeline: collect subexpressions, filter, find duplicates, remove
    subsumed, and sort by size (largest first). -/
private def findDeduplicationTargets (exprs : List Expression.Expr) :
    List Expression.Expr :=
  let candidates := exprs.filter (fun e => !isTrivial e && !hasBVar e)
  let duplicates := findDuplicates candidates
  let duplicates := removeSubsumed duplicates
  duplicates.mergeSort (fun a b => exprSize a > exprSize b)

---------------------------------------------------------------------
-- Statement-level expression mapping
---------------------------------------------------------------------

/-- Apply a function to all user-facing expressions in a list of statements. -/
private partial def mapExprsInStatements (f : Expression.Expr → Expression.Expr) :
    Statements → Statements
  | [] => []
  | s :: rest => mapExprsInStatement f s :: mapExprsInStatements f rest
where
  mapExprsInStatement (f : Expression.Expr → Expression.Expr) : Statement → Statement
  | .cmd (.cmd (.assert l e md)) => .cmd (.cmd (.assert l (f e) md))
  | .cmd (.cmd (.assume l e md)) => .cmd (.cmd (.assume l (f e) md))
  | .cmd (.cmd (.cover l e md)) => .cmd (.cmd (.cover l (f e) md))
  | .cmd (.cmd (.init n ty (.det e) md)) => .cmd (.cmd (.init n ty (.det (f e)) md))
  | .cmd (.cmd (.set n (.det e) md)) => .cmd (.cmd (.set n (.det (f e)) md))
  | .cmd (.call lhs pname args md) => .cmd (.call lhs pname (args.map f) md)
  | .block l ss md => .block l (mapExprsInStatements f ss) md
  | .ite (.det c) tss ess md =>
    .ite (.det (f c)) (mapExprsInStatements f tss) (mapExprsInStatements f ess) md
  | .ite .nondet tss ess md =>
    .ite .nondet (mapExprsInStatements f tss) (mapExprsInStatements f ess) md
  | .loop (.det g) measure inv body md =>
    .loop (.det (f g)) (measure.map f) (inv.map f) (mapExprsInStatements f body) md
  | .loop .nondet measure inv body md =>
    .loop .nondet (measure.map f) (inv.map f) (mapExprsInStatements f body) md
  | other => other

/-- Collect all user-facing expressions from a list of statements. -/
private partial def collectExprsFromStatements : Statements → List Expression.Expr
  | [] => []
  | s :: rest => collectExprsFromStatement s ++ collectExprsFromStatements rest
where
  collectExprsFromStatement : Statement → List Expression.Expr
  | .cmd (.cmd (.assert _ e _)) => collectSubexprs e
  | .cmd (.cmd (.assume _ e _)) => collectSubexprs e
  | .cmd (.cmd (.cover _ e _)) => collectSubexprs e
  | .cmd (.cmd (.init _ _ (.det e) _)) => collectSubexprs e
  | .cmd (.cmd (.set _ (.det e) _)) => collectSubexprs e
  | .cmd (.call _ _ args _) => args.flatMap collectSubexprs
  | .block _ ss _ => collectExprsFromStatements ss
  | .ite (.det c) tss ess _ =>
    collectSubexprs c ++ collectExprsFromStatements tss ++
    collectExprsFromStatements ess
  | .ite .nondet tss ess _ =>
    collectExprsFromStatements tss ++ collectExprsFromStatements ess
  | .loop (.det g) measure inv body _ =>
    collectSubexprs g ++ measure.toList.flatMap collectSubexprs ++
    inv.flatMap collectSubexprs ++ collectExprsFromStatements body
  | .loop .nondet measure inv body _ =>
    measure.toList.flatMap collectSubexprs ++
    inv.flatMap collectSubexprs ++ collectExprsFromStatements body
  | _ => []

---------------------------------------------------------------------
-- Program level deduplication
---------------------------------------------------------------------

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index. -/
def deduplicateBody (body : Statements) (startIdx : Nat) : Statements × Nat :=
  let targets := findDeduplicationTargets (collectExprsFromStatements body)
  -- Build var declarations in reverse, then reverse at the end
  let (revDecls, body', nextIdx) := targets.foldl (fun (decls, body, idx) dup =>
    let freshName : CoreIdent := ⟨s!"$__d.{idx}", ()⟩
    let freshTy := getExprType? dup
    let freshVar : Expression.Expr := .fvar () freshName freshTy
    let ty : Expression.Ty := match freshTy with
      | some mty => LTy.forAll [] mty
      | none => LTy.forAll ["α"] (.ftvar "α")
    let varDecl := Statement.init freshName ty (.det dup) .empty
    let body' := mapExprsInStatements (replaceExpr dup freshVar) body
    (varDecl :: decls, body', idx + 1)
  ) ([], body, startIdx)
  (revDecls.reverse ++ body', nextIdx)

/-- Deduplicate all procedures in a program. -/
def deduplicateProgram (p : Program) : Program :=
  let (revDecls, _, _) := p.decls.foldl (fun (acc, idx, _) decl =>
    match decl with
    | .proc proc md =>
      let (body', idx') := deduplicateBody proc.body idx
      (.proc { proc with body := body' } md :: acc, idx', ())
    | other => (other :: acc, idx, ())
  ) ([], 0, ())
  { decls := revDecls.reverse }

end Core.Deduplication

/-- Deduplication pipeline phase: extracts common subexpressions into fresh
    variable declarations. Model-preserving because it only introduces
    definitional equalities without changing program semantics. -/
def Core.deduplicationPipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "Deduplication" fun prog => do
    return (true, Core.Deduplication.deduplicateProgram prog)

end -- public section
