/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Strata.DL.Lambda.LExpr
import Strata.DL.Lambda.LState
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.LExprTypeEnv
import Lean
import Lean.Elab.Term

namespace Lambda
open Lean Elab Tactic Expr Meta
open Std (ToFormat Format format)

/-!
## Reflect Lambda expressions into Lean's logic
-/
-------------------------------------------------------------------------------

def LMonoTy.toExpr (mty : LMonoTy) : MetaM Lean.Expr := do
  match mty with
  | LMonoTy.bool    => return (mkConst ``Bool)
  | LMonoTy.int     => return (mkConst ``Int)
  | LMonoTy.string  => return (mkConst ``String)
  | _               => throwError f!"[LMonoTy.toExpr] Unimplemented: {mty}"

def toProp (e : Lean.Expr) : MetaM Lean.Expr := do
  let eType ← inferType e
  let eLvl ← getLevel eType
  if eType.isProp then
    return e
  else
    let expr := mkAppN (mkConst ``Eq [eLvl]) #[eType, e, mkConst ``Bool.true]
    return expr

def LExpr.const.toExpr (c : String) (mty : Option LMonoTy) : MetaM Lean.Expr := do
  match mty with
  | none => throwError f!"Cannot reflect an untyped constant: {c}!"
  | some mty => match mty with
    | LMonoTy.bool =>
      match c with
      | "true" => return (mkConst ``Bool.true)
      | "false" => return (mkConst ``Bool.false)
      | _ => throwError f!"Unexpected boolean: {c}"
    | LMonoTy.int =>
      if c.isInt then
        return (mkIntLit c.toInt!)
      else
        throwError f!"Unexpected integer: {c}"
    | LMonoTy.string =>
      return (mkStrLit c)
    | _ => throwError f!"Unexpected constant: {c}"

def LExpr.toExprNoFVars (e : LExpr String) : MetaM Lean.Expr := do
  match e with
  | .const c mty =>
    let expr ← LExpr.const.toExpr c mty
    return expr

  | .op _ _ =>
    throwError f!"[LExpr.toExprNoFVars] Operations not yet supported: {e}"

  | .bvar i =>
    let lctx ← getLCtx
    let some decl := lctx.getAt? (lctx.decls.size - i - 1) |
        throwError f!"[LExpr {e}]: No local declaration found in the context!"
    let expr := .fvar decl.fvarId
    return expr

  | .fvar f _ =>
    let lctx ← getLCtx
    match lctx.findFromUserName? (Lean.Name.mkSimple f) with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot find free var in the local context: {e}"
    | some decl => return decl.toExpr

  | .mdata _ e' => LExpr.toExprNoFVars e'

  | .abs mty e' =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped abstraction!"
    | some ty => do
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e'
        mkLambdaFVars #[x] bodyExpr

  | .quant qk mty e =>
    match mty with
    | none => throwError f!"[LExpr.toExprNoFVars] Cannot reflect untyped quantifier!"
    | some ty =>
      let tyExpr ← LMonoTy.toExpr ty
      let fname ← Lean.Core.mkFreshUserName `x
      withLocalDecl fname .default tyExpr fun x => do
        let bodyExpr ← LExpr.toExprNoFVars e
        -- let bodyType ← inferType bodyExpr
        -- let bodyLvl ← getLevel bodyType
        let bodyExpr ← toProp bodyExpr
        --   if bodyType.isProp then
        --     bodyExpr
        --   else
        --     let expr := mkAppN (mkConst ``Eq [bodyLvl]) #[bodyType, bodyExpr, mkConst ``Bool.true]
        --     expr
        match qk with
        | .all =>
            let expr ← mkForallFVars #[x] bodyExpr
            return expr
        | .exist => do
          let lambdaExpr ← mkLambdaFVars #[x] bodyExpr
          mkAppM ``Exists #[lambdaExpr]

  | .app fn arg =>
    let fnExpr ← LExpr.toExprNoFVars fn
    let argExpr ← LExpr.toExprNoFVars arg
    mkAppM' fnExpr #[argExpr]

  | .ite c t e =>
    -- Lean's ite:
    -- _root_.ite.{u} {α : Sort u} (c : Prop) [h : Decidable c] (t e : α) : α
    let cExpr ← LExpr.toExprNoFVars c
    -- let cType ← inferType cExpr
    -- let cLvl ← getLevel cType
    let tExpr ← LExpr.toExprNoFVars t
    let eExpr ← LExpr.toExprNoFVars e
    -- let tType ← inferType tExpr
    -- let tLvl ← getLevel tType
    -- In `cProp` below, `Eq` helps coerce `cExpr`, which is a `Bool`, to
    -- `Prop`.
    -- let cProp := mkAppN (mkConst ``Eq [cLvl]) #[cType, cExpr, mkConst ``Bool.true]
    -- let decidableInst := mkAppN (mkConst ``instDecidableEqBool) #[cExpr, mkConst ``Bool.true]
    -- return (mkAppN (mkConst ``_root_.ite [tLvl]) #[tType, cProp, decidableInst, tExpr, eExpr])
    let cProp ← mkAppM ``Eq #[cExpr, mkConst ``Bool.true]
    mkAppM ``_root_.ite #[cProp, tExpr, eExpr]

  | .eq e1 e2 =>
    let e1Expr ← LExpr.toExprNoFVars e1
    let e2Expr ← LExpr.toExprNoFVars e2
    -- let e1Type ← inferType e1Expr
    -- let e1Lvl ← getLevel e1Type
    -- let expr := mkAppN (mkConst ``Eq [e1Lvl]) #[e1Type, e1Expr, e2Expr]
    -- dbg_trace f!"eq expr: {expr}"
    -- return expr
    -- let expr ← mkAppM ``Eq #[e1Expr, e2Expr]
    let expr ← mkAppM ``BEq.beq #[e1Expr, e2Expr]
    return expr

def foo : MetaM Lean.Expr :=
  open LExpr.Syntax LTy.Syntax in
  LExpr.toExprNoFVars
  -- es[(#true : bool)]
  --  es[(#hello : string)]
  --  es[(#1 : int) == (#2 : int)]
  --  es[if (#false : bool) then (#1 : int) else (#2 : int)]
  -- (LExpr.abs (some mty[int]) (.bvar 0))
  -- (LExpr.app (.abs (some mty[int]) (.bvar 0)) (.const "5" mty[int]))
  -- (LExpr.app (.abs (some mty[bool]) (.bvar 0)) (.eq (.const "4" mty[int]) (.const "4" mty[int])))
  -- (@LExpr.quant String .all (some mty[int]) (.eq (.bvar 0) (.const "55" mty[int])))
  -- (@LExpr.quant String .all (some mty[int]) (@LExpr.eq String (@LExpr.bvar String 0) (@LExpr.bvar String 0)))
  -- (@LExpr.quant String .all (some mty[int]) (.eq (.bvar 0) (.const "42" (some mty[int]))))
  -- (@LExpr.quant String .exist (some mty[int]) (.eq (.bvar 0) (.const "42" (some mty[int]))))
  (LExpr.quant .all (some mty[int]) (.quant .all (some mty[int]) (.eq (.bvar 1) (.bvar 0))))
  -- (.quant .all (some mty[int]) (.eq (.fvar "a" mty[int]) (.bvar 0))) -- ∀ (a : Int) (y : Int), a = y

#eval foo

#eval show MetaM _ from do
  ppExpr (← foo)

elab "foo" : term => do
  let result ← liftM foo
  return result

#check foo
-- #eval foo

def LExpr.toExpr (e : LExpr String) : MetaM Lean.Expr := do
  let idTs := e.freeVars
  let decls : List (Name × (Array Lean.Expr → MetaM Lean.Expr)) ←
    idTs.mapM fun idT => do
      match idT.snd with
      | none => throwError f!"Untyped fvar encountered: {idT.fst}"
      | some ty =>
        -- let name ← Lean.Core.mkFreshUserName (Lean.Name.mkSimple idT.fst)
        let name := Lean.Name.mkSimple idT.fst
        return (name, fun _ => LMonoTy.toExpr ty)
  withLocalDeclsD decls.toArray fun fvars => do
    let e ← LExpr.toExprNoFVars e
    let e ← toProp e
    mkForallFVars (usedOnly := true) fvars e

def bar : MetaM Lean.Expr :=
  open LExpr.Syntax LTy.Syntax in
  LExpr.toExpr
    es[(x : int) == (y : int)]

#eval bar

#eval show MetaM _ from do
  ppExpr (← bar)

elab "bar" : term => do
  let result ← liftM bar
  return result

#check bar
-- #eval bar

-------------------------------------------------------------------------------
