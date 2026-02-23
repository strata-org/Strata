/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprTypeEnv
import Lean.Elab.Term
import Lean.Meta

/-!
## Reflect Lambda expressions into Lean's Logic

WIP.
-/

namespace Lambda
open Lean Elab Tactic Expr Meta
open Std (ToFormat Format format)

-------------------------------------------------------------------------------

def LMonoTy.toExpr (mty : LMonoTy) : MetaM Lean.Expr := do
  match mty with
  | LMonoTy.bool    => return (mkConst ``Bool)
  | LMonoTy.int     => return (mkConst ``Int)
  | LMonoTy.string  => return (mkConst ``String)
  | LMonoTy.bv1     => return (mkApp (mkConst ``BitVec) (mkNatLit 1))
  | LMonoTy.bv8     => return (mkApp (mkConst ``BitVec) (mkNatLit 8))
  | LMonoTy.bv16    => return (mkApp (mkConst ``BitVec) (mkNatLit 16))
  | LMonoTy.bv32    => return (mkApp (mkConst ``BitVec) (mkNatLit 32))
  | LMonoTy.bv64    => return (mkApp (mkConst ``BitVec) (mkNatLit 64))
  | .tcons "arrow" [a, b] =>
    let a ← LMonoTy.toExpr a
    let b ← LMonoTy.toExpr b
    return (.forallE `x a b .default)
  | .tcons "Map" [a, b] =>
    let a ← LMonoTy.toExpr a
    let b ← LMonoTy.toExpr b
    return mkApp2 (mkConst ``Map) a b
  | _ => throwError f!"[LMonoTy.toExpr] Unimplemented: {mty}"

def toProp (e : Lean.Expr) : MetaM Lean.Expr := do
  let eType ← inferType e
  let eLvl ← getLevel eType
  if eType.isProp then
    return e
  else if eType == mkConst ``Bool then
    let expr := mkAppN (mkConst ``Eq [eLvl]) #[eType, e, mkConst ``Bool.true]
    return expr
  else
    throwError f!"Cannot coerce to a Prop: {e}"

def LExpr.const.toExpr (c : LConst) : MetaM Lean.Expr := do
  match c with
  | .boolConst .true => return (mkConst ``Bool.true)
  | .boolConst .false => return (mkConst ``Bool.false)
  | .intConst i => return (mkIntLit i)
  | .strConst s => return (mkStrLit s)
  | _ => throwError f!"Unexpected constant: {c}"

abbrev MonoString: LExprParamsT := ⟨⟨Unit, String⟩, LMonoTy⟩

def LExpr.toExprNoFVars (e : LExpr MonoString) : MetaM Lean.Expr := do
  match e with
  | .const _ c =>
    let expr ← LExpr.const.toExpr c
    return expr

  | .op _ _ _ =>
    throwError f!"[LExpr.toExprNoFVars] Operations not yet supported: {e}"

  | .bvar _ i =>
    let lctx ← getLCtx
    let some decl := lctx.getAt? (lctx.decls.size - i - 1) |
        throwError f!"[LExpr {e}]: No local declaration found in the context!"
    let expr := .fvar decl.fvarId
    return expr

  | .fvar _ f _ =>
    let lctx ← getLCtx
    match lctx.findFromUserName? (Lean.Name.mkSimple f.name) with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot find free var in the local context: {e}"
    | some decl => return decl.toExpr

  | .abs _ mty e' =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped abstraction!"
    | some ty => do
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e'
        mkLambdaFVars #[x] bodyExpr

  | .quant _ qk mty _ e =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped quantifier!"
    | some ty =>
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e
        let bodyExpr ← toProp bodyExpr
        match qk with
        | .all =>
            let expr ← mkForallFVars #[x] bodyExpr
            return expr
        | .exist => do
          let lambdaExpr ← mkLambdaFVars #[x] bodyExpr
          mkAppM ``Exists #[lambdaExpr]

  | .app _ fn arg =>
    let fnExpr ← LExpr.toExprNoFVars fn
    let argExpr ← LExpr.toExprNoFVars arg
    mkAppM' fnExpr #[argExpr]

  | .ite _ c t e =>
    -- Lean's ite:
    -- _root_.ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α
    let cExpr ← LExpr.toExprNoFVars c
    let tExpr ← LExpr.toExprNoFVars t
    let eExpr ← LExpr.toExprNoFVars e
    -- In `cProp` below, `Eq` helps coerce `cExpr`, which is a `Bool`, to
    -- `Prop`.
    let cProp ← mkAppM ``Eq #[cExpr, mkConst ``Bool.true]
    mkAppM ``_root_.ite #[cProp, tExpr, eExpr]

  | .eq _ e1 e2 =>
    let e1Expr ← LExpr.toExprNoFVars e1
    let e2Expr ← LExpr.toExprNoFVars e2
    let expr ← mkAppM ``BEq.beq #[e1Expr, e2Expr]
    return expr

def LExpr.toExpr (e : LExpr MonoString) : MetaM Lean.Expr := do
  let idTs := e.freeVars
  let decls : List (Name × (Array Lean.Expr → MetaM Lean.Expr)) ←
    idTs.mapM fun idT => do
      match idT.snd with
      | none => throwError f!"Untyped fvar encountered: {idT.fst}"
      | some ty =>
        -- let name ← Lean.Core.mkFreshUserName (Lean.Name.mkSimple idT.fst)
        let name := Lean.Name.mkSimple idT.fst.name
        return (name, fun _ => LMonoTy.toExpr ty)
  withLocalDeclsD decls.toArray fun fvars => do
    let e ← LExpr.toExprNoFVars e
    let e ← toProp e
    mkForallFVars (usedOnly := true) fvars e

-------------------------------------------------------------------------------

section Tests

open LTy.Syntax LExpr.Syntax

end Tests

-------------------------------------------------------------------------------
