/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExpr

/-! # Generic `LExpr` traversals

General-purpose depth-first traversals of `LExpr` that both accumulate a value
(any `Append` "writer" `ω`) and optionally rewrite nodes. These are intended as
convenient, reusable building blocks — unlike the special-purpose,
high-performance operations in `LExpr.lean` and `LExprWF.lean`
(e.g., `hashExpr`).

Each traversal has a pointer-address-memoized (`PtrCache`) variant that visits
each physically distinct subterm exactly once; the `Result` it carries proves it
equals the pure reference, so memoization is a transparent optimization.
-/

namespace Lambda
namespace LExpr
namespace Traversal

public section

open Strata.PtrCache

/-- Where a node's own contribution sits relative to its children's in a
    depth-first accumulation. -/
inductive Order where
  | preorder
  | postorder
  deriving Repr, DecidableEq, Inhabited

/-- Monadic depth-first traversal that rewrites each node *at most once*, over an
    arbitrary monad `m` so the visitor `f` may thread state.
    At each node `e`, `f e` yields `(mopt, w)`.
    - If `mopt = some e'` the node is replaced by `e'`, and its subtree is
      not descended into.
    - Otherwise the children are traversed and the node's `w` placed `preorder`
      (before) or `postorder` (after) the children's contributions.
    The output ω is intentionally not embedded into the state, to make it clear
    that ω doesn't depend on the current state. This fact is used to make
    the pointer-cached version of applyOnceDFS (which is applyOnceDFSM with
    `Id` monad).
-/
def applyOnceDFSM {m : Type → Type} [Monad m] {T : LExprParamsT} {ω : Type} [Append ω]
    (order : Order) (f : LExpr T → m (Option (LExpr T) × ω)) : LExpr T → m (LExpr T × ω)
  | .const mt c => do let (mo, w) ← f (.const mt c); pure (mo.getD (.const mt c), w)
  | .bvar mt i => do let (mo, w) ← f (.bvar mt i); pure (mo.getD (.bvar mt i), w)
  | .fvar mt n ty => do let (mo, w) ← f (.fvar mt n ty); pure (mo.getD (.fvar mt n ty), w)
  | .op mt o ty => do let (mo, w) ← f (.op mt o ty); pure (mo.getD (.op mt o ty), w)
  | .app mt fn arg => do
    let (mo, w) ← f (.app mt fn arg)
    match mo with
    | some e' => pure (e', w)
    | none =>
      let (fn', wfn) ← applyOnceDFSM order f fn
      let (arg', warg) ← applyOnceDFSM order f arg
      pure (.app mt fn' arg',
            match order with | .preorder => w ++ wfn ++ warg | .postorder => wfn ++ warg ++ w)
  | .ite mt c t g => do
    let (mo, w) ← f (.ite mt c t g)
    match mo with
    | some e' => pure (e', w)
    | none =>
      let (c', wc) ← applyOnceDFSM order f c
      let (t', wt) ← applyOnceDFSM order f t
      let (g', wg) ← applyOnceDFSM order f g
      pure (.ite mt c' t' g',
            match order with | .preorder => w ++ wc ++ wt ++ wg | .postorder => wc ++ wt ++ wg ++ w)
  | .eq mt e1 e2 => do
    let (mo, w) ← f (.eq mt e1 e2)
    match mo with
    | some e' => pure (e', w)
    | none =>
      let (e1', w1) ← applyOnceDFSM order f e1
      let (e2', w2) ← applyOnceDFSM order f e2
      pure (.eq mt e1' e2',
            match order with | .preorder => w ++ w1 ++ w2 | .postorder => w1 ++ w2 ++ w)
  | .abs mt nm ty body => do
    let (mo, w) ← f (.abs mt nm ty body)
    match mo with
    | some e' => pure (e', w)
    | none =>
      let (body', wb) ← applyOnceDFSM order f body
      pure (.abs mt nm ty body',
            match order with | .preorder => w ++ wb | .postorder => wb ++ w)
  | .quant mt k nm ty tr body => do
    let (mo, w) ← f (.quant mt k nm ty tr body)
    match mo with
    | some e' => pure (e', w)
    | none =>
      let (tr', wtr) ← applyOnceDFSM order f tr
      let (body', wb) ← applyOnceDFSM order f body
      pure (.quant mt k nm ty tr' body',
            match order with | .preorder => w ++ wtr ++ wb | .postorder => wtr ++ wb ++ w)

/-- The pure (`Id`-monad) instance of `applyOnceDFSM`; `applyOnceDFSPtrCache`
    memoizes this version. -/
def applyOnceDFS {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → Option (LExpr T) × ω) : LExpr T → (LExpr T × ω) :=
  applyOnceDFSM (m := Id) order f

/-- Pointer-address-memoized `applyOnceDFS`: each physically distinct subterm is
    visited exactly once.  The `Result` proves the value equals `applyOnceDFS`. -/
def applyOnceDFSPtrCache {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → Option (LExpr T) × ω) :
    (e : LExpr T) → PtrCacheM (applyOnceDFS order f) e
  | .const m c => pure ⟨applyOnceDFS order f (.const m c), rfl⟩
  | .bvar m i => pure ⟨applyOnceDFS order f (.bvar m i), rfl⟩
  | .fvar m n ty => pure ⟨applyOnceDFS order f (.fvar m n ty), rfl⟩
  | .op m o ty => pure ⟨applyOnceDFS order f (.op m o ty), rfl⟩
  | .app m fn arg =>
    match hfe : f (.app m fn arg) with
    | (some e', w) => pure ⟨(e', w), by simp [applyOnceDFS, applyOnceDFSM, hfe] <;> rfl⟩
    | (none, w) => do
      let rfn ← evalPtrCache fn (applyOnceDFSPtrCache order f fn)
      let rarg ← evalPtrCache arg (applyOnceDFSPtrCache order f arg)
      pure ⟨(.app m rfn.output.1 rarg.output.1,
             match order with
             | .preorder => w ++ rfn.output.2 ++ rarg.output.2
             | .postorder => rfn.output.2 ++ rarg.output.2 ++ w),
            by cases order <;> simp [applyOnceDFS, applyOnceDFSM, hfe, rfn.h, rarg.h] <;> rfl⟩
  | .ite m c t g =>
    match hfe : f (.ite m c t g) with
    | (some e', w) => pure ⟨(e', w), by simp [applyOnceDFS, applyOnceDFSM, hfe] <;> rfl⟩
    | (none, w) => do
      let rc ← evalPtrCache c (applyOnceDFSPtrCache order f c)
      let rt ← evalPtrCache t (applyOnceDFSPtrCache order f t)
      let rg ← evalPtrCache g (applyOnceDFSPtrCache order f g)
      pure ⟨(.ite m rc.output.1 rt.output.1 rg.output.1,
             match order with
             | .preorder => w ++ rc.output.2 ++ rt.output.2 ++ rg.output.2
             | .postorder => rc.output.2 ++ rt.output.2 ++ rg.output.2 ++ w),
            by cases order <;> simp [applyOnceDFS, applyOnceDFSM, hfe, rc.h, rt.h, rg.h] <;> rfl⟩
  | .eq m e1 e2 =>
    match hfe : f (.eq m e1 e2) with
    | (some e', w) => pure ⟨(e', w), by simp [applyOnceDFS, applyOnceDFSM, hfe] <;> rfl⟩
    | (none, w) => do
      let r1 ← evalPtrCache e1 (applyOnceDFSPtrCache order f e1)
      let r2 ← evalPtrCache e2 (applyOnceDFSPtrCache order f e2)
      pure ⟨(.eq m r1.output.1 r2.output.1,
             match order with
             | .preorder => w ++ r1.output.2 ++ r2.output.2
             | .postorder => r1.output.2 ++ r2.output.2 ++ w),
            by cases order <;> simp [applyOnceDFS, applyOnceDFSM, hfe, r1.h, r2.h] <;> rfl⟩
  | .abs m nm ty body =>
    match hfe : f (.abs m nm ty body) with
    | (some e', w) => pure ⟨(e', w), by simp [applyOnceDFS, applyOnceDFSM, hfe] <;> rfl⟩
    | (none, w) => do
      let rb ← evalPtrCache body (applyOnceDFSPtrCache order f body)
      pure ⟨(.abs m nm ty rb.output.1,
             match order with
             | .preorder => w ++ rb.output.2
             | .postorder => rb.output.2 ++ w),
            by cases order <;> simp [applyOnceDFS, applyOnceDFSM, hfe, rb.h] <;> rfl⟩
  | .quant m k nm ty tr body =>
    match hfe : f (.quant m k nm ty tr body) with
    | (some e', w) => pure ⟨(e', w), by simp [applyOnceDFS, applyOnceDFSM, hfe] <;> rfl⟩
    | (none, w) => do
      let rtr ← evalPtrCache tr (applyOnceDFSPtrCache order f tr)
      let rb ← evalPtrCache body (applyOnceDFSPtrCache order f body)
      pure ⟨(.quant m k nm ty rtr.output.1 rb.output.1,
             match order with
             | .preorder => w ++ rtr.output.2 ++ rb.output.2
             | .postorder => rtr.output.2 ++ rb.output.2 ++ w),
            by cases order <;> simp [applyOnceDFS, applyOnceDFSM, hfe, rtr.h, rb.h] <;> rfl⟩

/-- Run the pointer-address-memoized `applyOnceDFS` on `e`. -/
def applyOnceDFSPtrCached {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → Option (LExpr T) × ω) (e : LExpr T) : LExpr T × ω :=
  ((applyOnceDFSPtrCache order f e).run' PtrCache.empty).output


/-- Depth-first fold that accumulates `f` over every node without rewriting. -/
def visitDFS {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → ω) (e : LExpr T) : ω :=
  (applyOnceDFS order (fun e => (none, f e)) e).2

/-- Pointer-address-memoized `visitDFS`, exposed as a `PtrCacheM` so callers can
    thread one `PtrCache (visitDFS order f)` across several traversals (each
    physically distinct subterm is folded once, cumulatively).  The `Result`
    proves the value equals `visitDFS order f e`. -/
def visitDFSPtrCache {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → ω) : (e : LExpr T) → PtrCacheM (visitDFS order f) e
  | .const m c => pure ⟨f (.const m c), by simp [visitDFS, applyOnceDFS, applyOnceDFSM] <;> rfl⟩
  | .bvar m i => pure ⟨f (.bvar m i), by simp [visitDFS, applyOnceDFS, applyOnceDFSM] <;> rfl⟩
  | .fvar m n ty => pure ⟨f (.fvar m n ty), by simp [visitDFS, applyOnceDFS, applyOnceDFSM] <;> rfl⟩
  | .op m o ty => pure ⟨f (.op m o ty), by simp [visitDFS, applyOnceDFS, applyOnceDFSM] <;> rfl⟩
  | .app m fn arg => do
    let rfn ← evalPtrCache fn (visitDFSPtrCache order f fn)
    let rarg ← evalPtrCache arg (visitDFSPtrCache order f arg)
    pure ⟨(match order with
           | .preorder => f (.app m fn arg) ++ rfn.output ++ rarg.output
           | .postorder => rfn.output ++ rarg.output ++ f (.app m fn arg)),
          by cases order <;> simp [visitDFS, applyOnceDFS, applyOnceDFSM, rfn.h, rarg.h] <;> rfl⟩
  | .ite m c t g => do
    let rc ← evalPtrCache c (visitDFSPtrCache order f c)
    let rt ← evalPtrCache t (visitDFSPtrCache order f t)
    let rg ← evalPtrCache g (visitDFSPtrCache order f g)
    pure ⟨(match order with
           | .preorder => f (.ite m c t g) ++ rc.output ++ rt.output ++ rg.output
           | .postorder => rc.output ++ rt.output ++ rg.output ++ f (.ite m c t g)),
          by cases order <;> simp [visitDFS, applyOnceDFS, applyOnceDFSM, rc.h, rt.h, rg.h] <;> rfl⟩
  | .eq m e1 e2 => do
    let r1 ← evalPtrCache e1 (visitDFSPtrCache order f e1)
    let r2 ← evalPtrCache e2 (visitDFSPtrCache order f e2)
    pure ⟨(match order with
           | .preorder => f (.eq m e1 e2) ++ r1.output ++ r2.output
           | .postorder => r1.output ++ r2.output ++ f (.eq m e1 e2)),
          by cases order <;> simp [visitDFS, applyOnceDFS, applyOnceDFSM, r1.h, r2.h] <;> rfl⟩
  | .abs m nm ty body => do
    let rb ← evalPtrCache body (visitDFSPtrCache order f body)
    pure ⟨(match order with
           | .preorder => f (.abs m nm ty body) ++ rb.output
           | .postorder => rb.output ++ f (.abs m nm ty body)),
          by cases order <;> simp [visitDFS, applyOnceDFS, applyOnceDFSM, rb.h] <;> rfl⟩
  | .quant m k nm ty tr body => do
    let rtr ← evalPtrCache tr (visitDFSPtrCache order f tr)
    let rb ← evalPtrCache body (visitDFSPtrCache order f body)
    pure ⟨(match order with
           | .preorder => f (.quant m k nm ty tr body) ++ rtr.output ++ rb.output
           | .postorder => rtr.output ++ rb.output ++ f (.quant m k nm ty tr body)),
          by cases order <;> simp [visitDFS, applyOnceDFS, applyOnceDFSM, rtr.h, rb.h] <;> rfl⟩

/-- Run the pointer-address-memoized `visitDFS` on `e` (fresh cache). -/
def visitDFSPtrCached {T : LExprParamsT} {ω : Type} [Append ω] (order : Order)
    (f : LExpr T → ω) (e : LExpr T) : ω :=
  ((visitDFSPtrCache order f e).run' PtrCache.empty).output

end -- public section

end Traversal
end LExpr
end Lambda
