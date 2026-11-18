/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTyUnify

/-! ## One-way type matching

Matching a pattern type against a type binds only the pattern's listed type
variables; every other type variable, on either side, is a constant.
-/

namespace Lambda

public section

mutual
/-- Extend `S` so that substituting it into `pat` gives `ty`, binding only the type variables in
    `params`; `none` on a mismatch or when a variable would need two types. -/
def LMonoTy.matchTy? (params : List TyIdentifier) (S : SubstOne) (pat ty : LMonoTy) :
    Option SubstOne :=
  match pat, ty with
  | .ftvar a, _ =>
    if params.contains a then
      match S.find? a with
      | some bound => if bound == ty then some S else none
      | none => some (S.insert a ty)
    else if pat == ty then some S else none
  | .bitvec n, .bitvec m => if n == m then some S else none
  | .tcons n pats, .tcons m tys =>
    if n == m then LMonoTys.matchTys? params S pats tys else none
  | _, _ => none

/-- `LMonoTy.matchTy?` on two lists of types of the same length, position by position. -/
def LMonoTys.matchTys? (params : List TyIdentifier) (S : SubstOne) (pats tys : LMonoTys) :
    Option SubstOne :=
  match pats, tys with
  | [], [] => some S
  | pat :: pats, ty :: tys => do
    let S ← LMonoTy.matchTy? params S pat ty
    LMonoTys.matchTys? params S pats tys
  | _, _ => none
end

/-- `LMonoTy.matchTy?` on each pattern paired with a known type, position by position, skipping
    the patterns whose type is unknown. -/
def LMonoTys.matchKnown? (params : List TyIdentifier) (pairs : List (LMonoTy × Option LMonoTy)) :
    Option SubstOne :=
  pairs.foldlM (init := Strata.Util.HMap.empty) fun S (pat, ty?) =>
    match ty? with
    | some ty => LMonoTy.matchTy? params S pat ty
    | none => some S

/-- `σ` extended to map each unbound `i`-th type variable of `params` to the type variable
    `pfx ++ toString i`. -/
def SubstOne.completeParams (params : List TyIdentifier) (pfx : String) (σ : SubstOne) :
    SubstOne :=
  params.zipIdx.foldl (init := σ) fun S (p, i) =>
    if (S.find? p).isSome then S else S.insert p (.ftvar (pfx ++ toString i))

end -- public section

end Lambda
