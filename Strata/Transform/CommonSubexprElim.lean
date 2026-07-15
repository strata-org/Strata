/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Util.List
public import Strata.Util.PtrCache
import Lean.Util.ShareCommon

/-! # Common Subexpression Elimination

Core-to-Core transformation that extracts common subexpressions into fresh
`var` declarations, reducing duplicated subexpressions from partially evaluated
result.

For example:
```
assume F(2+z) >= 5
assert F(2+z)+F(2+z) == 2*F(2+z)
```
becomes:
```
// Note that 2+z is not deduplicated even if it appeared four times in the
// original code.

var $__cse.0 := F(2+z)
assume $__cse.0 >= 5
assert $__cse.0+$__cse.0 == 2*$__cse.0
```

The pass walks procedure bodies via `runCSE`, hoisting duplicated
subexpressions into `var` declarations prepended to the body.
-/

public section

namespace Core.CSE

open Lambda Imperative

/-- Prefix used for CSE-generated variable names. -/
def cseVarPrefix : String := "$__cse."

open Strata.PtrCache

abbrev hx : Expression.Expr → UInt64 := LExpr.hashExpr

---------------------------------------------------------------------
-- Subexpression hashes calculator
---------------------------------------------------------------------

/-- Monadic structural hash: threads the shared `PtrCache` (the state monad's
    state) and returns the memoized structural hash of `e`. O(1) for a node that
    was already hashed. -/
private def hashM (e : Expression.Expr) : StateM (PtrCache hx) UInt64 := do
  return (← evalPtrCache e (LExpr.hashExprPtrCache e)).output

/-- Collect the hashes of every proper subexpression of `e` into `acc`.
    `top := true` marks a top-level candidate, whose own hash is not
    recorded. -/
private def collectSubexprHashes (acc : Std.HashSet UInt64) (top : Bool)
    (e : Expression.Expr) : StateM (PtrCache hx) (Std.HashSet UInt64) := do
  let he ← hashM e
  if !top && acc.contains he then return acc
  else
    let acc := if top then acc else acc.insert he
    match e with
    | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => return acc
    | .app _ fn arg =>
      let acc ← collectSubexprHashes acc false fn
      collectSubexprHashes acc false arg
    | .ite _ c t f =>
      let acc ← collectSubexprHashes acc false c
      let acc ← collectSubexprHashes acc false t
      collectSubexprHashes acc false f
    | .eq _ e1 e2 =>
      let acc ← collectSubexprHashes acc false e1
      collectSubexprHashes acc false e2
    | .abs _ _ _ body => collectSubexprHashes acc false body
    | .quant _ _ _ _ tr body =>
      let acc ← collectSubexprHashes acc false tr
      collectSubexprHashes acc false body
  termination_by e

/-- Remove entries that are subexpressions of larger entries in the list,
    keeping only the maximal ones. Each entry is paired with its structural hash
    (the `dups` bucket key), so no expression is re-hashed here. -/
private def removeSubsumed (memo : PtrCache hx)
    (exprs : List (UInt64 × Expression.Expr)) : List (UInt64 × Expression.Expr) :=
  let (subHashes, _) :=
    (exprs.foldlM (fun acc (p : UInt64 × Expression.Expr) => collectSubexprHashes acc true p.2)
      ({} : Std.HashSet UInt64)).run memo
  exprs.filter (fun (h, _) => !subHashes.contains h)


---------------------------------------------------------------------
-- Common subexpressions finder
---------------------------------------------------------------------

/-- Traversal state.
    * `memoHash` caches each visited node's structural hash by pointer identity.
    * `seen` records visited LExprs. Maps hash to the distinct subexpressions carrying it;
    * `dups` is the subset of `seen` encountered at least twice. -/
private structure CollectedExprs where
  memoHash : PtrCache hx := PtrCache.empty
  seen : Std.HashMap UInt64 (Array Expression.Expr) := {}
  dups : Std.HashMap UInt64 (Array Expression.Expr) := {}

/-- Record the first occurrence of a bvar-free `e` in `seen` under hash `h`. -/
private def CollectedExprs.recordSeen (st : CollectedExprs) (h : UInt64)
    (e : Expression.Expr) : CollectedExprs :=
  { st with seen := st.seen.insert h ((st.seen.getD h #[]).push e) }

/-- Structural equality with a safe pointer-equality fast path. -/
private def exprEq (a b : Expression.Expr) : Bool :=
  (withPtrEqDecEq a b (fun _ => (inferInstance : DecidableEq Expression.Expr) a b)).decide

/-- Note a repeated occurrence: add `e` to the `dups` bucket for `h` (once). -/
private def CollectedExprs.recordDup (st : CollectedExprs) (h : UInt64)
    (e : Expression.Expr) : CollectedExprs :=
  let bucket := st.dups.getD h #[]
  -- The performance of the code below relies on an assumption that there is
  -- almost no hash collision; hence bucket.size is either 0 or 1.
  if bucket.any (exprEq e) then st
  else { st with dups := st.dups.insert h (bucket.push e) }

/-- Structural hash of `e` (O(1) once cached), threading the shared `PtrCache`
    held in the `memoHash` field. -/
private def CollectedExprs.withHash (st : CollectedExprs) (e : Expression.Expr) :
    UInt64 × CollectedExprs :=
  let (r, memoHash) := (evalPtrCache e (LExpr.hashExprPtrCache e)).run st.memoHash
  (r.output, { st with memoHash })

/-- Walk `e` and record every eligible subexpression into `st`.
    A subexpression is eligible when it is a non-leaf.
    For function applications, records the full (curried) application and
    recurses into each argument, but does not record intermediate partial
    applications from the spine. `abs` bodies contribute nothing but
    still propagate their bvar-free flag to the parent.

    The returned `Bool` is `true` when `e` is bvar-free. The node's hash is
    computed once at the top via the pointer-memoized `hashCached`, so the
    `seen` early-return costs O(1) rather than an O(tree) rehash. -/
private def collectSubexprs (st : CollectedExprs) (e : Expression.Expr) :
    Bool/- is `e` bvar-free? -/ × CollectedExprs :=
  let (h, st) := st.withHash e
  -- Early exit on a subexpression we have already fully traversed. Everything
  -- recorded in `seen` was inserted on the bvar-free branch, so a hit means
  -- `e` is bvar-free and its subexpressions were already recorded on the first
  -- encounter; we only bump its duplicate count.
  if (st.seen.getD h #[]).any (exprEq e) then
    (true, st.recordDup h e)
  else
  match e with
  | .const _ _ | .fvar _ _ _ | .op _ _ _ => (true, st)
  | .bvar _ _ => (false, st)
  | .app _ fn arg =>
    let (fnOk, st) := walkSpine st fn
    let (argOk, st) := collectSubexprs st arg
    let ok := fnOk && argOk
    (ok, if ok then st.recordSeen h e else st)
  | .ite _ c t f =>
    let (cOk, st) := collectSubexprs st c
    let (tOk, st) := collectSubexprs st t
    let (fOk, st) := collectSubexprs st f
    let ok := cOk && tOk && fOk
    (ok, if ok then st.recordSeen h e else st)
  | .eq _ e1 e2 =>
    let (ok1, st) := collectSubexprs st e1
    let (ok2, st) := collectSubexprs st e2
    let ok := ok1 && ok2
    (ok, if ok then st.recordSeen h e else st)
  | .abs _ _ _ body =>
    -- Report bvar-freeness (may spuriously return true because it doesn't
    -- compare de bruijn index with the depth) through the body so a parent
    -- sees the flag, but do not record subexpressions under the binder.
    -- `hasBVarCached` memoizes by pointer identity, so this stays proportional
    -- to the number of distinct DAG nodes rather than a full tree walk.
    (!LExpr.hasBVarCached body, st)
  | .quant _ _ _ _ tr body =>
    let (ok1, st1) := collectSubexprs st tr
    let (ok2, st2) := collectSubexprs { st with memoHash := st1.memoHash } body
    (ok1 && ok2, { st with memoHash := st2.memoHash })
where
  /-- Walk an application spine: recurse into each argument via
      `collectSubexprs`, but do not record the intermediate partial
      applications (matches the original behavior). Threads the bvar-free flag
      through the spine head so the enclosing `.app` sees it. In practice
      spine heads in Core IR are always `.app`/`.op`/`.fvar`/`.const`; the
      catch-all fallback preserves correctness for the rare exotic case
      (e.g. `(if ... then f else g) x`). -/
  walkSpine (st : CollectedExprs) (e : Expression.Expr) : Bool × CollectedExprs :=
    match e with
    | .app _ fn arg =>
      let (fnOk, st) := walkSpine st fn
      let (argOk, st) := collectSubexprs st arg
      (fnOk && argOk, st)
    | .bvar _ _ => (false, st)
    | .const _ _ | .fvar _ _ _ | .op _ _ _ => (true, st)
    | e => (!LExpr.hasBVarCached e, st)

/-- Shared pipeline: walk the input expressions once to collect duplicate
    eligible subexpressions, remove subsumed entries. Returns each surviving
    duplicate paired with its structural hash (the `dups` bucket key), so the
    caller need not re-hash it. -/
private def collectExprsToAbbreviate (exprs : List Expression.Expr) :
    List (UInt64 × Expression.Expr) :=
  let final := exprs.foldl (fun st e => (collectSubexprs st e).2) ({} : CollectedExprs)
  let duplicates := (final.dups.toList.mergeSort (fun a b => a.1 < b.1)).flatMap
    (fun (h, bucket) => bucket.toList.map (h, ·))
  removeSubsumed final.memoHash duplicates

---------------------------------------------------------------------
-- Fast replacement of subexpressions
---------------------------------------------------------------------

/-- A memoized rewrite of one node: the `original` expression and its
    `rewritten` form. Bucketed by the original node's structural hash (the memo
    map key), kept collision-safe by an `exprEq` guard on `original`. -/
private structure Rewrite where
  original  : Expression.Expr
  rewritten : Expression.Expr

/-- Traversal state for `replaceExprs`: the shared structural-hash `PtrCache`
    plus the rewrite memo (bucketed by original-node hash). -/
private structure RwState where
  cache : PtrCache hx := PtrCache.empty
  memo  : Std.HashMap UInt64 (List Rewrite) := {}

/-- Structural hash of `e` (O(1) once cached), threading the shared cache held
    in the `RwState`. -/
private def RwState.hashM (e : Expression.Expr) : StateM RwState UInt64 := do
  let s ← get
  let (r, cache) := (evalPtrCache e (LExpr.hashExprPtrCache e)).run s.cache
  set { s with cache }
  return r.output

/-- If the original node `e` (identified by its structural hash `h`) matches a
    replacement target, return the replacement; otherwise return `e'` (the node
    rebuilt with its children already rewritten). -/
private def tryReplace
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (h : UInt64) (e e' : Expression.Expr) : Expression.Expr :=
  match replacements[h]? with
  | some pairs =>
    match pairs.find? (fun (t, _) => exprEq e t) with
    | some (_, replacement) => replacement
    | none => e'
  | none => e'

/-- Bottom-up rewrite of `e` into its rewritten form. Each node's result is
    memoized in `RwState.memo`, keyed by the original node's structural hash
    `ho` (O(1) from the shared `PtrCache`) and made collision-safe by an `exprEq`
    guard on the stored original. Note we reuse `ho` for the `tryReplace`
    lookup: the replacement targets are keyed by their own structural hash, so
    there is no need to recombine a hash from the children (which would
    duplicate `hashExpr`'s definition and risk drifting out of sync). -/
private def replaceSubexprs
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) : StateM RwState Expression.Expr := do
  let ho ← RwState.hashM e
  let s ← get
  match (s.memo.getD ho []).find? (fun r => exprEq r.original e) with
  | some r => return r.rewritten
  | none =>
    -- Rebuild the node with its children rewritten (relevant when `e` itself is
    -- not a target but contains targets in its subterms).
    let e' ← match e with
      | .const _ _ | .bvar _ _ | .fvar _ _ _ | .op _ _ _ => pure e
      | .app m fn arg =>
        let fn' ← replaceSubexprs replacements fn
        let arg' ← replaceSubexprs replacements arg
        pure (.app m fn' arg')
      | .ite m c t f =>
        let c' ← replaceSubexprs replacements c
        let t' ← replaceSubexprs replacements t
        let f' ← replaceSubexprs replacements f
        pure (.ite m c' t' f')
      | .eq m e1 e2 =>
        let e1' ← replaceSubexprs replacements e1
        let e2' ← replaceSubexprs replacements e2
        pure (.eq m e1' e2')
      | .abs m name ty body =>
        let body' ← replaceSubexprs replacements body
        pure (.abs m name ty body')
      | .quant m k name ty tr body =>
        let tr' ← replaceSubexprs replacements tr
        let body' ← replaceSubexprs replacements body
        pure (.quant m k name ty tr' body')
    let result := tryReplace replacements ho e e'
    modify fun s => { s with memo := s.memo.insert ho (⟨e, result⟩ :: s.memo.getD ho []) }
    return result
  termination_by e

/-- Apply subexpression replacement to `e`. -/
private def replaceExprs
    (replacements : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr)))
    (e : Expression.Expr) : Expression.Expr :=
  (replaceSubexprs replacements e).run' {}

---------------------------------------------------------------------
-- Program level common subexpression elimination
---------------------------------------------------------------------

/-- Fuel bounding `stmtRunCSE`'s fixpoint loop: the total number of distinct DAG
    nodes across the body's expressions. Each iteration lifts at least one
    maximal duplicate and introduces no new non-leaf subexpression, so this many
    rounds always suffices to reach the fixpoint. Reuses `collectSubexprHashes`
    (with `top := false` it records every node's hash), so the distinct-node
    count is O(#distinct nodes) and shares the same traversal machinery. -/
def fuel (exprs : List Expression.Expr) : Nat :=
  ((exprs.foldlM (fun acc e => collectSubexprHashes acc false e)
    ({} : Std.HashSet UInt64)).run' PtrCache.empty).size

/-- A single common-subexpression-elimination iteration. Extracts the maximal
    duplicated subexpressions of `body` into fresh `var` declarations (fresh
    indices starting at `startIdx`), rewrites the body to reference them, and
    prepends the declarations. Returns `none` when there is nothing to extract. -/
def stmtRunCSEIter (body : Statements) (startIdx : Nat) : Option (Statements × Nat) :=
  let targets := collectExprsToAbbreviate (Statements.collectExprs body)
  if targets.isEmpty then
    none
  else
    -- Build all var declarations and the replacement map. The map value is a
    -- list of (target, replacement) pairs to be collision-safe under the
    -- structural hash; see `replaceExprs` above.
    let (revDecls, replacements, nextIdx) := targets.foldl (fun (decls, repMap, idx) (h, dup) =>
      let freshName : CoreIdent := ⟨s!"{cseVarPrefix}{idx}", ()⟩
      let freshTy := dup.typeOf
      let freshVar : Expression.Expr := .fvar () freshName freshTy
      let ty : Expression.Ty := match freshTy with
        | some mty => LTy.forAll [] mty
        | none => LTy.forAll ["α"] (.ftvar "α")
      let varDecl := Statement.init freshName ty (.det dup) .empty
      -- `h` is `dup`'s structural hash, already computed by
      -- `collectExprsToAbbreviate` (the `dups` bucket key); no need to re-hash.
      let pairs := repMap.getD h []
      (varDecl :: decls, repMap.insert h ((dup, freshVar) :: pairs), idx + 1)
    ) ([], ({} : Std.HashMap UInt64 (List (Expression.Expr × Expression.Expr))), startIdx)
    let body' := Statements.mapExprs (replaceExprs replacements) body
    -- `reverseAux` reverses `revDecls` onto `body'` in a single pass, avoiding
    -- the intermediate list that `revDecls.reverse ++ body'` would allocate.
    some (revDecls.reverseAux body', nextIdx)

/-- Deduplicate a procedure's body by extracting common subexpressions into
    `var` declarations prepended to the body. Returns the modified body and
    the next available dedup index. -/
def stmtRunCSE (body : Statements) (startIdx : Nat) : Statements × Nat :=
  -- For performance, maximize structural sharing of subexpressions up front, so
  -- the pointer-address hash cache hashes each distinct subterm exactly once
  -- (and `exprEq`'s pointer fast path hits more often).
  let body := Lean.ShareCommon.shareCommon body
  go (fuel (Statements.collectExprs body)) body startIdx
where
  go (steps : Nat) (body : Statements) (startIdx : Nat) : Statements × Nat :=
    match steps with
    | 0 => (body, startIdx)
    | steps' + 1 =>
      match stmtRunCSEIter body startIdx with
      | none => (body, startIdx)
      | some (newBody, nextIdx) => go steps' newBody nextIdx

/-- Deduplicate all procedures in a program. Returns the modified program
    and whether any changes were made. -/
def runCSE (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  let (revDecls, _, changed) := p.decls.foldl (fun (acc, idx, changed) decl =>
    match decl with
    | .proc proc md =>
      match proc.body with
      | .structured ss =>
        let (body', idx') := stmtRunCSE ss idx
        (.proc { proc with body := .structured body' } md :: acc, idx', changed || idx' > idx)
      | .cfg _ =>
        -- CFG bodies are not transformed by CSE for now.
        (.proc proc md :: acc, idx, changed)
    | other => (other :: acc, idx, changed)
  ) ([], 0, false)
  return (changed, { decls := revDecls.reverse })

end Core.CSE

/-- CSE pipeline phase: extracts common subexpressions into fresh
    variable declarations. Model-preserving because it only introduces
    definitional equalities without changing program semantics. -/
def Core.commonSubexprElimPhase : Core.PipelinePhase :=
  Core.modelPreservingPipelinePhase "CommonSubexprElim" Core.CSE.runCSE

end -- public section
