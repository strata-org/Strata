/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Util.List

/-! # ANF Encoder

Core-to-Core transformation that extracts common subexpressions into fresh
`var` declarations, reducing duplication from partial evaluation.

For example:
```
assume F(2+z) >= 5
assert F(2+z)+F(2+z) == 2*F(2+z)
```
becomes:
```
var $__anf.0 := F(2+z)
assume $__anf.0 >= 5
assert $__anf.0+$__anf.0 == 2*$__anf.0
```

The pass walks procedure bodies via `anfEncodeProgram`, hoisting duplicated
subexpressions into `var` declarations prepended to the body.
-/

public section

namespace Core.ANFEncoder

open Lambda Imperative

/-- Prefix used for ANF-generated variable names. Shared between the encoder
    and the verifier's model filter. -/
def anfVarPrefix : String := "$__anf."

---------------------------------------------------------------------
-- Expression analysis utilities
---------------------------------------------------------------------

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

/-- Wrapper for using expressions as HashMap keys with metadata-ignoring comparison. -/
private structure ExprKey where
  expr : Expression.Expr

private instance : BEq ExprKey where
  beq a b := a.expr == b.expr

private instance : Hashable ExprKey where
  hash k := LExpr.hashExpr k.expr

/-- Find expressions that appear more than once in a list, using metadata-ignoring
    comparison via `ExprKey`. -/
private def findDuplicates (exprs : List Expression.Expr) : List Expression.Expr :=
  (exprs.map ExprKey.mk).findDuplicates.map ExprKey.expr

/-- Replace all occurrences of any target with its corresponding replacement
    in an expression. Computes hashes bottom-up to avoid redundant traversals.
    The map stores (target, replacement) pairs keyed by hash. -/
def replaceExprs (replacements : Std.HashMap UInt64 (Expression.Expr × Expression.Expr))
    (e : Expression.Expr) : Expression.Expr :=
  (go e).2
where
  /-- Bottom-up traversal returning (hash, replaced expression). -/
  go (e : Expression.Expr) : UInt64 × Expression.Expr :=
    match e with
    | .const _ c => check (LExpr.hashConst (hash c)) e
    | .bvar _ i => check (LExpr.hashBVar (hash i)) e
    | .fvar _ n ty => check (LExpr.hashFVar (hash n.name) (LExpr.hashOptTy ty)) e
    | .op _ o ty => check (LExpr.hashOp (hash o.name) (LExpr.hashOptTy ty)) e
    | .app m fn arg =>
      let (hfn, fn') := go fn
      let (harg, arg') := go arg
      let e' : Expression.Expr := .app m fn' arg'
      check (LExpr.hashApp hfn harg) e'
    | .ite m c t f =>
      let (hc, c') := go c
      let (ht, t') := go t
      let (hf, f') := go f
      let e' : Expression.Expr := .ite m c' t' f'
      check (LExpr.hashIte hc ht hf) e'
    | .eq m e1 e2 =>
      let (h1, e1') := go e1
      let (h2, e2') := go e2
      let e' : Expression.Expr := .eq m e1' e2'
      check (LExpr.hashEqExpr h1 h2) e'
    | .abs m name ty body =>
      let (hbody, body') := go body
      let e' : Expression.Expr := .abs m name ty body'
      check (LExpr.hashAbs (hash name) (LExpr.hashOptTy ty) hbody) e'
    | .quant m k name ty tr body =>
      let (htr, tr') := go tr
      let (hbody, body') := go body
      let e' : Expression.Expr := .quant m k name ty tr' body'
      let kh : UInt64 := match k with | .all => 0 | .exist => 1
      check (LExpr.hashQuantExpr kh (hash name) (LExpr.hashOptTy ty) htr hbody) e'
  /-- Check if the hash matches a replacement target. -/
  check (h : UInt64) (e : Expression.Expr) : UInt64 × Expression.Expr :=
    match replacements[h]? with
    | some (target, replacement) =>
      if e == target then (h, replacement) else (h, e)
    | none => (h, e)

/-- Collect all subexpression hashes from an expression,
    excluding the expression itself. -/
private def collectSubexprHashes (e : Expression.Expr) : Std.HashSet UInt64 :=
  let (topHash, set) := go e
  set.insert topHash |>.erase topHash
where
  /-- Bottom-up traversal returning (hash, set of descendant hashes). -/
  go (e : Expression.Expr) : UInt64 × Std.HashSet UInt64 :=
    match e with
    | .const _ c => (LExpr.hashConst (hash c), {})
    | .bvar _ i => (LExpr.hashBVar (hash i), {})
    | .fvar _ n ty => (LExpr.hashFVar (hash n.name) (LExpr.hashOptTy ty), {})
    | .op _ o ty => (LExpr.hashOp (hash o.name) (LExpr.hashOptTy ty), {})
    | .app _ fn arg =>
      let (hfn, s1) := go fn
      let (harg, s2) := go arg
      (LExpr.hashApp hfn harg, s1.union s2 |>.insert hfn |>.insert harg)
    | .ite _ c t f =>
      let (hc, s1) := go c
      let (ht, s2) := go t
      let (hf, s3) := go f
      (LExpr.hashIte hc ht hf, s1.union s2 |>.union s3 |>.insert hc |>.insert ht |>.insert hf)
    | .eq _ e1 e2 =>
      let (h1, s1) := go e1
      let (h2, s2) := go e2
      (LExpr.hashEqExpr h1 h2, s1.union s2 |>.insert h1 |>.insert h2)
    | .abs _ name ty body =>
      let (hbody, s) := go body
      (LExpr.hashAbs (hash name) (LExpr.hashOptTy ty) hbody, s.insert hbody)
    | .quant _ k name ty tr body =>
      let (htr, s1) := go tr
      let (hbody, s2) := go body
      let kh : UInt64 := match k with | .all => 0 | .exist => 1
      (LExpr.hashQuantExpr kh (hash name) (LExpr.hashOptTy ty) htr hbody,
       s1.union s2 |>.insert htr |>.insert hbody)

/-- Remove entries that are subexpressions of larger entries in the list.
    Uses hash-based lookup for O(n) per-target instead of O(n × tree_size). -/
private def removeSubsumed (exprs : List Expression.Expr) : List Expression.Expr :=
  -- Build a set of all subexpression hashes from all targets
  let subHashes := exprs.foldl (fun (acc : Std.HashSet UInt64) e =>
    acc.union (collectSubexprHashes e)
  ) {}
  -- Keep only expressions whose hash is NOT a subexpression of another target
  exprs.filter (fun e => !subHashes.contains (LExpr.hashExpr e))

/-- Shared pipeline: collect subexpressions, filter, find duplicates, remove
    subsumed, and sort by size (largest first). -/
private def findANFEncoderTargets (exprs : List Expression.Expr) :
    List Expression.Expr :=
  let candidates := exprs.filter (fun e => !e.isLeaf && !e.hasBVar)
  let duplicates := findDuplicates candidates
  let duplicates := removeSubsumed duplicates
  duplicates.mergeSort (fun a b => LExpr.size _ a > LExpr.size _ b)

---------------------------------------------------------------------
-- Program level ANF encoding
---------------------------------------------------------------------

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index.
    Assumes single-assignment (SSA-like) property of the post-PE Core IR:
    variables are assigned only once, so structurally equal expressions
    always denote the same value within a procedure body. -/
def anfEncodeBody (body : Statements) (startIdx : Nat) : Statements × Nat :=
  let targets := findANFEncoderTargets ((Statements.collectExprs body).flatMap collectSubexprs)
  -- Build all var declarations and the replacement map
  let (revDecls, replacements, nextIdx) := targets.foldl (fun (decls, repMap, idx) dup =>
    let freshName : CoreIdent := ⟨s!"{anfVarPrefix}{idx}", ()⟩
    let freshTy := dup.typeOf
    let freshVar : Expression.Expr := .fvar () freshName freshTy
    let ty : Expression.Ty := match freshTy with
      | some mty => LTy.forAll [] mty
      | none => LTy.forAll ["α"] (.ftvar "α")
    let varDecl := Statement.init freshName ty (.det dup) .empty
    let h := LExpr.hashExpr dup
    (varDecl :: decls, repMap.insert h (dup, freshVar), idx + 1)
  ) ([], ({} : Std.HashMap UInt64 (Expression.Expr × Expression.Expr)), startIdx)
  -- Single pass: replace all targets at once
  let body' := Statements.mapExprs (replaceExprs replacements) body
  (revDecls.reverse ++ body', nextIdx)

/-- Deduplicate all procedures in a program. Returns the modified program
    and whether any changes were made. -/
def anfEncodeProgram (p : Program) : Bool × Program :=
  let (revDecls, _, changed) := p.decls.foldl (fun (acc, idx, changed) decl =>
    match decl with
    | .proc proc md =>
      let (body', idx') := anfEncodeBody proc.body idx
      (.proc { proc with body := body' } md :: acc, idx', changed || idx' > idx)
    | other => (other :: acc, idx, changed)
  ) ([], 0, false)
  (changed, { decls := revDecls.reverse })

end Core.ANFEncoder

/-- ANFEncoder pipeline phase: extracts common subexpressions into fresh
    variable declarations. Model-preserving because it only introduces
    definitional equalities without changing program semantics. -/
def Core.anfEncoderPipelinePhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "ANFEncoder" fun prog => do
    let (changed, prog') := Core.ANFEncoder.anfEncodeProgram prog
    return (changed, prog')

end -- public section
