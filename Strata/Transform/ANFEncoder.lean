/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase

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

/-- Hash an optional type annotation. -/
private def hashOptType (ty : Option LMonoTy) : UInt64 :=
  match ty with
  | none => 0
  | some t => hash t

/-- Hash an expression structurally, including type annotations but ignoring
    metadata, for use in HashMap-based ANF encoding. -/
private def hashExpr : Expression.Expr → UInt64
  | .const _ c => mixHash 1 (hash (toString c))
  | .bvar _ i => mixHash 2 (hash i)
  | .fvar _ n ty => mixHash 3 (mixHash (hash n.name) (hashOptType ty))
  | .op _ o ty => mixHash 4 (mixHash (hash o.name) (hashOptType ty))
  | .app _ fn arg => mixHash 5 (mixHash (hashExpr fn) (hashExpr arg))
  | .ite _ c t f => mixHash 6 (mixHash (hashExpr c) (mixHash (hashExpr t) (hashExpr f)))
  | .eq _ e1 e2 => mixHash 7 (mixHash (hashExpr e1) (hashExpr e2))
  | .abs _ name ty body => mixHash 8 (mixHash (hash name) (mixHash (hashOptType ty) (hashExpr body)))
  | .quant _ k name ty tr body =>
    let kh : UInt64 := match k with | .all => 0 | .exist => 1
    mixHash 9 (mixHash kh (mixHash (hash name) (mixHash (hashOptType ty) (mixHash (hashExpr tr) (hashExpr body)))))

/-- Wrapper for using expressions as HashMap keys with metadata-ignoring comparison. -/
private structure ExprKey where
  expr : Expression.Expr

private instance : BEq ExprKey where
  beq a b := a.expr == b.expr

private instance : Hashable ExprKey where
  hash k := hashExpr k.expr

/-- Find expressions that appear more than once in a list. Uses a HashMap
    for O(1) lookup. -/
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

/-- Replace all occurrences of any target with its corresponding replacement
    in an expression. Computes hashes bottom-up to avoid redundant traversals.
    The map stores (target, replacement) pairs keyed by hash. -/
partial def replaceExprs (replacements : Std.HashMap UInt64 (Expression.Expr × Expression.Expr))
    (e : Expression.Expr) : Expression.Expr :=
  (go e).2
where
  /-- Bottom-up traversal returning (hash, replaced expression). -/
  go (e : Expression.Expr) : UInt64 × Expression.Expr :=
    match e with
    | .const _ c => (mixHash 1 (hash (toString c)), e)
    | .bvar _ i => (mixHash 2 (hash i), e)
    | .fvar _ n ty => (mixHash 3 (mixHash (hash n.name) (hashOptType ty)), e)
    | .op _ o ty => (mixHash 4 (mixHash (hash o.name) (hashOptType ty)), e)
    | .app m fn arg =>
      let (hFn, fn') := go fn
      let (hArg, arg') := go arg
      let h := mixHash 5 (mixHash hFn hArg)
      check h (.app m fn' arg')
    | .ite m c t f =>
      let (hC, c') := go c
      let (hT, t') := go t
      let (hF, f') := go f
      let h := mixHash 6 (mixHash hC (mixHash hT hF))
      check h (.ite m c' t' f')
    | .eq m e1 e2 =>
      let (h1, e1') := go e1
      let (h2, e2') := go e2
      let h := mixHash 7 (mixHash h1 h2)
      check h (.eq m e1' e2')
    | .abs m name ty body =>
      let (hB, body') := go body
      let h := mixHash 8 (mixHash (hash name) (mixHash (hashOptType ty) hB))
      check h (.abs m name ty body')
    | .quant m k name ty tr body =>
      let (hTr, tr') := go tr
      let (hB, body') := go body
      let kh : UInt64 := match k with | .all => 0 | .exist => 1
      let h := mixHash 9 (mixHash kh (mixHash (hash name) (mixHash (hashOptType ty) (mixHash hTr hB))))
      check h (.quant m k name ty tr' body')
  /-- Check if the hash matches a replacement target. -/
  check (h : UInt64) (e : Expression.Expr) : UInt64 × Expression.Expr :=
    match replacements[h]? with
    | some (target, replacement) =>
      if e == target then (h, replacement) else (h, e)
    | none => (h, e)

/-- Collect all subexpression hashes from an expression,
    excluding the expression itself. -/
private def collectSubexprHashes (e : Expression.Expr) : Std.HashSet UInt64 :=
  let topHash := hashExpr e
  go e |>.erase topHash
where
  go (e : Expression.Expr) : Std.HashSet UInt64 :=
    let h := hashExpr e
    match e with
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => ({} : Std.HashSet UInt64).insert h
    | .app _ fn arg => (go fn |>.union (go arg)).insert h
    | .ite _ c t f => (go c |>.union (go t) |>.union (go f)).insert h
    | .eq _ e1 e2 => (go e1 |>.union (go e2)).insert h
    | .abs _ _ _ body => (go body).insert h
    | .quant _ _ _ _ tr body => (go tr |>.union (go body)).insert h

/-- Remove entries that are subexpressions of larger entries in the list.
    Uses hash-based lookup for O(n) per-target instead of O(n × tree_size). -/
private def removeSubsumed (exprs : List Expression.Expr) : List Expression.Expr :=
  -- Build a set of all subexpression hashes from all targets
  let subHashes := exprs.foldl (fun (acc : Std.HashSet UInt64) e =>
    acc.union (collectSubexprHashes e)
  ) {}
  -- Keep only expressions whose hash is NOT a subexpression of another target
  exprs.filter (fun e => !subHashes.contains (hashExpr e))

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
    let freshTy := Core.getExprType? dup
    let freshVar : Expression.Expr := .fvar () freshName freshTy
    let ty : Expression.Ty := match freshTy with
      | some mty => LTy.forAll [] mty
      | none => LTy.forAll ["α"] (.ftvar "α")
    let varDecl := Statement.init freshName ty (.det dup) .empty
    let h := hashExpr dup
    (varDecl :: decls, repMap.insert h (dup, freshVar), idx + 1)
  ) ([], ({} : Std.HashMap UInt64 (Expression.Expr × Expression.Expr)), startIdx)
  -- Single pass: replace all targets at once
  let body' := Statements.mapExprs (replaceExprs replacements) body
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
