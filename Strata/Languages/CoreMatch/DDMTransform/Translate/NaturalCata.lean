/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.CoreMatch.DDMTransform.Translate.Basic
public import Strata.Languages.CoreMatch.DDMTransform.Translate.Datatypes
public import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprWF

/-!
Desugar natural-style match arms to cata-style ones, so both surface
forms emit the same eliminator argument.

The transformation runs in two passes. During body translation,
`tryRecRewrite` replaces each self-call `f(field)` with a sentinel
fvar carrying the rec-result slot index. After translation,
`desugarNaturalToCata` injects rec-result binders, lifts the body's
existing bvars past them, and substitutes each sentinel with the
matching `bvar`.
-/

namespace Strata.CoreMatch.Translate

open Lambda
open Strata.CoreMatchDDM

public section

/-- Name of the placeholder fvar that stands in for a rec-result
reference until `desugarNaturalToCata` resolves it. -/
def recSentinelName (slot : Nat) : String :=
  s!"$$coreMatch$rec${slot}"

/-- If the application is a self-call `f(field)` that should lower to
a rec-result slot, return the matching sentinel; otherwise `none`. -/
def tryRecRewrite (f a : CoreMatchDDM.Expr SourceRange)
    : TransM (Option Core.Expression.Expr) := do
  let .fvar _ fIdx := f | return none
  let .bvar _ bIdx := a | return none
  let s ← StateT.get
  let some fName := s.gctx.nameOf? fIdx | return none
  unless s.recFns.contains fName do return none
  let stackSize := s.bvars.size
  unless bIdx < stackSize do return none
  let fieldPos := stackSize - 1 - bIdx
  let some slot := s.recRewrites[(fName, fieldPos)]? | return none
  return some <| .fvar () ⟨recSentinelName slot, ()⟩ none

/-- The shape of an arm's pattern binders relative to its
constructor's declared fields. -/
inductive ArmShape where
  /-- One binder per declared field; the body's self-calls on
  recursive fields will be rewritten. `recFieldIdxs` are the
  positions of the recursive-typed fields. -/
  | natural (recFieldIdxs : List Nat)
  /-- Field binders followed by one extra binder per recursive
  field; the body is taken verbatim. -/
  | cata
  /-- Datatype isn't cached; trust the user's binder count. -/
  | unknown

def classifyArm (dtName ctor : String)
    (binderTys : List LMonoTy) : TransM ArmShape := do
  let isRecField : LMonoTy → Bool
    | .tcons n _ => n == dtName
    | _          => false
  let userArity := binderTys.length
  match (← lookupCtor dtName ctor) with
  | none => return .unknown
  | some fields =>
    let fc := fields.length
    let recIdxs := binderTys.take fc |>.zipIdx.filterMap fun (ty, i) =>
      if isRecField ty then some i else none
    if userArity == fc                    then return .natural recIdxs
    if userArity == fc + recIdxs.length   then return .cata
    throw <| .fromMessage
      s!"match arm '{ctor}': expected {fc} field binders \
         or {fc + recIdxs.length} (with rec-results), got {userArity}"

/-- Build the rewrite-map entries for an arm: one
`(recFn, fieldStackPos) ↦ recResultIdx` per pairing of a current rec
function with a recursive field. Stack positions are bottom-relative
so they survive nested binders inside the body. -/
def naturalRecRewrites
    (recFns : List String) (recIdxs : List Nat) (baseDepth : Nat)
    : List ((String × Nat) × Nat) :=
  let recCount := recIdxs.length
  recFns.flatMap fun fn =>
    recIdxs.zipIdx.map fun (fieldIdx, i) =>
      ((fn, baseDepth + fieldIdx), recCount - 1 - i)

/-- Resolve the sentinels left in a natural-style arm body, returning
the cata-shaped `(binders, body)` pair: appends one rec-result binder
per recursive field, lifts the body's existing bvars past them, and
substitutes each sentinel `$$coreMatch$rec$i` with `bvar i`. -/
def desugarNaturalToCata
    (resultMTy : LMonoTy) (recCount : Nat)
    (binders : List (String × LMonoTy)) (body : Core.Expression.Expr)
    : List (String × LMonoTy) × Core.Expression.Expr :=
  let injected := (List.range recCount).map fun i =>
    (s!"rec_{i}", resultMTy)
  let subst : _root_.Map Core.Expression.Ident Core.Expression.Expr :=
    _root_.Map.ofList <| (List.range recCount).map fun i =>
      (⟨recSentinelName i, ()⟩, .bvar () i)
  let lifted := LExpr.liftBVars recCount body
  (binders ++ injected, LExpr.substFvarsLifting lifted subst)

end

end Strata.CoreMatch.Translate
