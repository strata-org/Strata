/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LTy
import Strata.DDM.AST
import Strata.DDM.Util.Array
import Strata.DL.Util.Func
import Strata.DL.Util.List
import Strata.DL.Util.ListMap
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.LExprTypeSpec

/-!
## Lambda's Factory

This module formalizes Lambda's _factory_, which is a mechanism to extend the
type checker (see `Strata.DL.Lambda.LExprT`) and partial evaluator (see
`Strata.DL.Lambda.LExprEval`) by providing a map from operations to their types
and optionally, denotations. The factory allows adding type checking and
evaluation support for new operations without modifying the implementation of
either or any core ASTs.

Also see `Strata.DL.Lambda.IntBoolFactory` for a concrete example of a factory.
-/


namespace Lambda
open Strata
open Std (ToFormat Format format)

variable {T : LExprParams} [Inhabited T.Metadata] [ToFormat T.IDMeta]

abbrev TypeContext.{u} := List (TyIdentifier × Type u)

def denoteLMonoTy : TypeContext.{u} → LMonoTy → Type u
| _, .bool => ULift Bool
| _, .int => ULift Int
| _, .string => ULift String
| _, .bitvec n => ULift (BitVec n)
| ctx, .arrow t1 t2 => denoteLMonoTy ctx t1 → denoteLMonoTy ctx t2
| ctx, .ftvar x => (ctx.lookup x).getD (ULift Empty)
| _, .tcons _ _ => ULift Empty

def denoteLTy.{u} : TypeContext.{u} → LTy → Type (u+1)
| ctx, .forAll [] ty =>
    ULift.{u+1, u} (denoteLMonoTy.{u} ctx ty)
| ctx, .forAll (v :: vs) ty =>
    (α : Type u) → denoteLTy ((v, α) :: ctx) (.forAll vs ty)

def denoteCtx {T : LExprParams} (ctx : TContext T.IDMeta) : TypeContext := sorry

def denoteLExpr
  {T : LExprParams}
  [Inhabited T.IDMeta]
  [DecidableEq T.IDMeta]
  [Monad m]
  (hMono: T.mono.TypeType = LMonoTy)
  (C: LContext T)
  (ctx : TContext T.IDMeta)
  (e : LExpr T.mono)
  (wt : LExpr.HasType C ctx e ty) : m (denoteLTy (denoteCtx ctx) ty) :=
  match h: e with
  | .boolConst _ b =>
    have : ty = LTy.forAll [] LMonoTy.bool := by cases wt<;> sorry --PROBLEM!
    sorry

  | .realConst _ r => sorry
  | .bitvecConst _ n bv => sorry
  | .strConst _ s => sorry
  | .intConst _ i => sorry
  | .op    _ o ty => sorry
  | .bvar  _ deBruijnIndex => sorry
  | .fvar  _ name ty => sorry
  | .abs   _ mty e => sorry
  | .quant _ .all bty _ body => sorry
  | .quant _ .exist bty _ e => sorry
  | .app   _ fn e => sorry
  | .ite   _ c t e =>
    have Hc: LExpr.HasType C ctx c (.forAll [] .bool) := by
      cases wt;  sorry
    have Ht: LExpr.HasType C ctx t ty := by sorry
    have He: LExpr.HasType C ctx e ty := by sorry
    do
      let c' ← denoteLExpr hMono C ctx c Hc
      let t' ← denoteLExpr hMono C ctx t Ht
      let e' ← denoteLExpr hMono C ctx e He
      return (if c' then t' else e')
   sorry
  | .eq    _ e1 e2 => sorry
