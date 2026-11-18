/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.FunctionType
import Strata.Languages.Core.WrittenTyVarScope

public section

namespace Core

open Lambda
open Std (ToFormat Format format)

namespace Distinct

/-- Constraints equating every expression's type with the first expression's type. -/
def sharedTypeConstraints :
    List (LExprT CoreLParams.mono) → Constraints
  | [] => []
  | et :: ets => ets.map fun et' => (et'.toLMonoTy, et.toLMonoTy)

/-- The first expression, among those paired with their types, whose type cannot be unified
    with `t0` under `S` extended by the earlier ones, with its type and the substitution
    at the failure. -/
def firstMismatch (S : SubstInfo) (t0 : LMonoTy) :
    List (Expression.Expr × LMonoTy) → Option (Expression.Expr × LMonoTy × SubstInfo)
  | [] => none
  | (e, t) :: rest =>
    match Constraints.unify [(t, t0)] S with
    | .ok S' => firstMismatch S' t0 rest
    | .error _ => some (e, t, S)

/-- An expression as shown in messages: a constant or variable by its name alone, any other
    expression as formatted. -/
def exprLabel : Expression.Expr → Format
  | .op _ c _ => format c
  | .fvar _ x _ => format x
  | e => format e

/-- The error for expressions of differing types: the first expression whose type differs
    from the first expression's type, with both types. Generated type names are hidden
    unless `known` registers them. -/
def mismatchMsg (known : KnownTypes) (name : Expression.Ident)
    (es : List Expression.Expr) (ets : List (LExprT CoreLParams.mono))
    (S : SubstInfo) : Format :=
  let generic := f!"Distinct '{name}' expressions must have the same type"
  match es, ets with
  | e0 :: es', et0 :: ets' =>
    let t0 := et0.toLMonoTy
    match firstMismatch S t0 (es'.zip (ets'.map (·.toLMonoTy))) with
    | some (e, t, S') =>
      let render (ty : LMonoTy) : Format :=
        format (hideGeneratedTyCons known (displayTy S'.subst ty))
      f!"Distinct '{name}': {exprLabel e0} has type {render t0} \
        but {exprLabel e} has type {render t}"
    | none => generic
  | _, _ => generic

/-- Type check a distinct declaration: its annotations mention no type variable a user may
    write, and its two or more expressions share one type with no type variable in their stored
    annotations. -/
def typeCheck (C : Expression.TyContext) (Env : Expression.TyEnv)
    (name : Expression.Ident) (es : List Expression.Expr) :
    Except Format (List Expression.Expr × Expression.TyEnv) :=
  match WrittenTyVarScope.unboundAnnotMsg? false [] [] es with
  | some msg => .error f!"Error in distinct {name}: {msg}"
  | none =>
  let resolved := match es with
    | _ :: _ :: _ => SourceExpr.resolves C Env es
    | _ => .error f!"Distinct '{name}' must contain at least two expressions"
  match SourceExpr.orFreeVarError (fun _ => Env.freeVarChecks es) resolved with
  | .error e => .error e
  | .ok (ets, EnvR) =>
    match Constraints.unify (sharedTypeConstraints ets) EnvR.stateSubstInfo with
    | .error _ => .error (mismatchMsg C.knownTypes name es ets EnvR.stateSubstInfo)
    | .ok S =>
      let out := ets.map (finishStored [] S.subst (tyVarsIn []))
      if out.all (·.2) then
        .ok (out.map (·.1), EnvR)
      else
        .error
          f!"Distinct '{name}' is typed at a generated type variable that is not declared"

end Distinct

end Core
