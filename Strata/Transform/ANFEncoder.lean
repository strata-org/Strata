/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

/-! # Expression ANFEncoder

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
var $__t.0 := F(2+z)
assume $__t.0 >= 5
assert $__t.0+$__t.0 == 2*$__t.0
```

This is the second phase described in issue #749: after partial evaluation
produces a Core program with inlined expressions, ANF encoding normalizes
the result by factoring out common subexpressions.

## Design

The pass operates at the program level: `anfEncodeProgram` walks procedure
bodies and extracts common subexpressions into `var` declarations prepended
to the body.

After ANF encoding, proof obligation extraction (issue #475) becomes a simple
tree traversal that collects individual goals from `if * { } else { }` trees
— no further SMT-to-SMT optimization is needed.
-/

public section

namespace Core.ANFEncoder

open Lambda Imperative

---------------------------------------------------------------------
-- Expression analysis utilities
---------------------------------------------------------------------

/-- Check if an expression is a leaf node that should not be anfEncoded. -/
private def isTrivial (e : Expression.Expr) : Bool :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => true
  | _ => false

/-- Check if an expression contains bound variables, which would make
    ANF encoding unsound across different binding contexts. -/
private def hasBVar (e : Expression.Expr) : Bool :=
  match e with
  | .bvar _ _ => true
  | .const _ _ | .fvar _ _ _ | .op _ _ _ => false
  | .app _ fn arg => hasBVar fn || hasBVar arg
  | .ite _ c t f => hasBVar c || hasBVar t || hasBVar f
  | .eq _ e1 e2 => hasBVar e1 || hasBVar e2
  | .abs _ _ _ body => hasBVar body
  | .quant _ _ _ _ tr body => hasBVar tr || hasBVar body

/-- Collect non-trivial subexpressions from an expression, suitable for
    ANF encoding. For function applications, collects the full (curried)
    application and recurses into each argument, but does not collect
    intermediate partial applications from the spine. -/
private def collectSubexprs (e : Expression.Expr) : List Expression.Expr :=
  match e with
  | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => []
  | .app _ fn arg =>
    -- Collect the full application, then recurse into arguments of the spine
    [e] ++ collectAppArgs fn ++ collectSubexprs arg
  | .ite _ c t f =>
    [e] ++ collectSubexprs c ++ collectSubexprs t ++ collectSubexprs f
  | .eq _ e1 e2 =>
    [e] ++ collectSubexprs e1 ++ collectSubexprs e2
  | .abs _ _ _ _ => []
  | .quant _ _ _ _ _ _ => []
where
  /-- Recurse into the arguments along an application spine. -/
  collectAppArgs (e : Expression.Expr) : List Expression.Expr :=
    match e with
    | .app _ fn arg => collectAppArgs fn ++ collectSubexprs arg
    | _ => []

/-- Hash an expression structurally, ignoring type annotations (matching
    `eraseTypes` semantics) for use in HashMap-based ANF encoding. -/
private def hashExpr : Expression.Expr → UInt64
  | .const _ c => mixHash 1 (hash (toString c))
  | .bvar _ i => mixHash 2 (hash i)
  | .fvar _ n _ => mixHash 3 (hash n.name)
  | .op _ o _ => mixHash 4 (hash o.name)
  | .app _ fn arg => mixHash 5 (mixHash (hashExpr fn) (hashExpr arg))
  | .ite _ c t f => mixHash 6 (mixHash (hashExpr c) (mixHash (hashExpr t) (hashExpr f)))
  | .eq _ e1 e2 => mixHash 7 (mixHash (hashExpr e1) (hashExpr e2))
  | .abs _ name _ body => mixHash 8 (mixHash (hash name) (hashExpr body))
  | .quant _ k name _ tr body =>
    let kh : UInt64 := match k with | .all => 0 | .exist => 1
    mixHash 9 (mixHash kh (mixHash (hash name) (mixHash (hashExpr tr) (hashExpr body))))

/-- Wrapper for using expressions as HashMap keys with type-erased comparison. -/
private structure ExprKey where
  expr : Expression.Expr

private instance : BEq ExprKey where
  beq a b := a.expr.eraseTypes == b.expr.eraseTypes

private instance : Hashable ExprKey where
  hash k := hashExpr k.expr

/-- Find expressions that appear more than once in a list. Uses a HashMap
    for O(1) lookup with type-erased comparison. -/
private def findDuplicates (exprs : List Expression.Expr) : List Expression.Expr :=
  -- Single pass: count occurrences and remember the first expression per key
  let map := exprs.foldl (fun (m : Std.HashMap ExprKey (Expression.Expr × Nat)) e =>
    let key := ⟨e⟩
    match m[key]? with
    | some (orig, n) => m.insert key (orig, n + 1)
    | none => m.insert key (e, 1)
  ) {}
  let revDups := map.fold (fun acc _ (orig, count) =>
    if count > 1 then orig :: acc else acc
  ) ([] : List Expression.Expr)
  revDups.reverse

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
private def findANFEncoderTargets (exprs : List Expression.Expr) :
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
-- Program level ANF encoding
---------------------------------------------------------------------

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index. -/
def anfEncodeBody (body : Statements) (startIdx : Nat) : Statements × Nat :=
  let targets := findANFEncoderTargets (collectExprsFromStatements body)
  -- Build var declarations in reverse, then reverse at the end
  let (revDecls, body', nextIdx) := targets.foldl (fun (decls, body, idx) dup =>
    let freshName : CoreIdent := ⟨s!"$__t.{idx}", ()⟩
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
def anfEncodeProgram (p : Program) : Program :=
  let (revDecls, _, _) := p.decls.foldl (fun (acc, idx, _) decl =>
    match decl with
    | .proc proc md =>
      let (body', idx') := anfEncodeBody proc.body idx
      (.proc { proc with body := body' } md :: acc, idx', ())
    | other => (other :: acc, idx, ())
  ) ([], 0, ())
  { decls := revDecls.reverse }

end Core.ANFEncoder

/-- ANFEncoder pipeline phase: extracts common subexpressions into fresh
    variable declarations. Model-preserving because it only introduces
    definitional equalities without changing program semantics. -/
def Core.anfEncoderPipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "ANFEncoder" fun prog => do
    return (true, Core.ANFEncoder.anfEncodeProgram prog)

end -- public section
