
/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LExprTypeSpec
import Strata.DL.Lambda.LTy

namespace Lambda

/-------------------------------/
/- Polymorphic type denotation -/
/-------------------------------/

abbrev TypeContextP.{u} := List (TyIdentifier × Type u)

def denoteLMonoTyP.{u} : TypeContextP → LMonoTy → Type u
| _, .bool => ULift Bool
| _, .int => ULift Int
| _, .string => ULift String
| _, .bitvec n => ULift (BitVec n)
| ctx, .arrow t1 t2 => denoteLMonoTyP ctx t1 → denoteLMonoTyP ctx t2
| ctx, .ftvar x => (ctx.lookup x).getD (ULift Empty)
| _, .tcons _ _ => ULift Empty

def denoteLTyP.{u} : TypeContextP → LTy → Type (u+1)
| ctx, .forAll [] ty =>
    ULift.{u+1, u} (denoteLMonoTyP.{u} ctx ty)
| ctx, .forAll (v :: vs) ty =>
    (α : Type u) → denoteLTyP ((v, α) :: ctx) (.forAll vs ty)

def denoteCtxP (ctx : TContext IdMeta) : TypeContextP :=
  ctx.types.flatMap (List.map (fun (xv, ty) => (xv.name, denoteLTyP [] ty)))

/-------------------------------/
/- Monomorphic type denotation -/
/-------------------------------/

abbrev TypeContext := List (TyIdentifier × Type)

def denoteLMonoTy : TypeContext → LMonoTy → Type
| _, .bool => ULift Bool
| _, .int => ULift Int
| _, .string => ULift String
| _, .bitvec n => ULift (BitVec n)
| ctx, .arrow t1 t2 => denoteLMonoTy ctx t1 → denoteLMonoTy ctx t2
| ctx, .ftvar x => (ctx.lookup x).getD (ULift Empty)
| _, .tcons _ _ => ULift Empty

def denoteLTy : TypeContext → LTy → Type
| ctx, .forAll [] ty => denoteLMonoTy ctx ty
| _, .forAll _ _ => Empty

def denoteCtx (ctx : TContext IdMeta) : TypeContext :=
  ctx.types.flatMap (List.map (fun (xv, ty) => (xv.name, denoteLTy [] ty)))

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
  match e with
  | .boolConst _ b => sorry
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
  | .ite   _ c t e => sorry
  | .eq    _ e1 e2 => sorry

end Lambda
