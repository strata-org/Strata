/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Denote.LExprDenote

/-!
## Test: `InterpConsistentEval` for a polymorphic factory function

We define a polymorphic identity function `id : ∀a. a → a` with a
`concreteEval` that returns its argument unchanged, and verify that
`InterpConsistentEval` holds when `opInterp` interprets `id` as the
identity at every sort.
-/

namespace Lambda

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

private def idFunc : LFunc TP :=
  LFunc.mk (⟨"id", ()⟩ : Identifier Unit)
    (typeArgs := ["a"])
    (inputs := [(⟨"x", ()⟩, .ftvar "a")])
    (output := .ftvar "a")
    (concreteEval := some fun _ args => match args with
      | [x] => some x
      | _ => none)

private def idCeval : Unit → List (LExpr TP.mono) → Option (LExpr TP.mono) :=
  fun _ args => match args with
  | [x] => some x
  | _ => none

-- opInterp maps "id" to the identity function at every sort.
-- For well-typed uses, the sort is always `a → a` for some `a`.
private noncomputable def idOpInterp (tcInterp : TyConstrInterp) [TyConstrInterp.AllInhabited tcInterp] : OpInterp tcInterp :=
  fun name sort => match name with
  | "id" => match sort with
    | .tcons "arrow" [a, b] =>
      if h : a = b then h ▸ (fun (x : SortDenote tcInterp a) => x)
      else default
    | _ => default
  | _ => default

/-- `idOpInterp` applied at an arrow sort `s → s` is the identity. -/
private theorem idOpInterp_apply (tcInterp : TyConstrInterp) [TyConstrInterp.AllInhabited tcInterp]
    (s : LSort) (x : SortDenote tcInterp s) :
    SortDenote.applyArgs tcInterp (idOpInterp tcInterp "id" (LSort.mkArrow s [s]))
      (.cons x .nil) = x := by
  simp [idOpInterp, LSort.mkArrow]
  rfl

-- The key test: InterpConsistentEval holds for the polymorphic id function
noncomputable example (tcInterp : TyConstrInterp) [TyConstrInterp.AllInhabited tcInterp] :
    LFunc.InterpConsistentEval tcInterp (idOpInterp tcInterp) idFunc idCeval := by
  intro vt fvarVal md tySubst argExprs resultExpr heval
  -- Normalize the types manually
  change ∀ (h_args : List.Rel₂ (LExpr.HasTypeA []) argExprs [LMonoTy.subst tySubst (.ftvar "a")])
    (h_result : LExpr.HasTypeA [] resultExpr (LMonoTy.subst tySubst (.ftvar "a"))), _
  intro h_args h_result
  cases h_args with
  | cons hx htail =>
    cases htail
    simp [idCeval] at heval; subst heval
    exact (idOpInterp_apply tcInterp _ _).symm

end Lambda
