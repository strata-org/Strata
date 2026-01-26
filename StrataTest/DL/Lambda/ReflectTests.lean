/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.Reflect

/-! ## Tests for Reflect -/

namespace Lambda
open Lean Elab Tactic Expr Meta
open Std (ToFormat Format format)
open LTy.Syntax LExpr.Syntax

/--
info: Lean.Expr.app (Lean.Expr.app (Lean.Expr.const `Map []) (Lean.Expr.const `Int [])) (Lean.Expr.const `Bool [])
-/
#guard_msgs in
#eval LMonoTy.toExpr mty[Map int bool]

def test1 : MetaM Lean.Expr :=
  LExpr.toExpr
    (.quant () .all (some mty[int]) (LExpr.noTrigger ()) (.eq () (.fvar () "x" mty[int]) (.bvar () 0)))

/--
info: Lean.Expr.forallE
  `x
  (Lean.Expr.const `Int [])
  (Lean.Expr.forallE
    (Lean.Name.mkNum (Lean.Name.mkStr (Lean.Name.mkStr (Lean.Name.mkNum `x.«_@».StrataTest.DL.Lambda.ReflectTests 1611904336) "_hygCtx") "_hyg") 8)
    (Lean.Expr.const `Int [])
    (Lean.Expr.app
      (Lean.Expr.app
        (Lean.Expr.app (Lean.Expr.const `Eq [Lean.Level.succ (Lean.Level.zero)]) (Lean.Expr.const `Bool []))
        (Lean.Expr.app
          (Lean.Expr.app
            (Lean.Expr.app
              (Lean.Expr.app (Lean.Expr.const `BEq.beq [Lean.Level.zero]) (Lean.Expr.const `Int []))
              (Lean.Expr.app
                (Lean.Expr.app (Lean.Expr.const `instBEqOfDecidableEq [Lean.Level.zero]) (Lean.Expr.const `Int []))
                (Lean.Expr.const `Int.instDecidableEq [])))
            (Lean.Expr.bvar 1))
          (Lean.Expr.bvar 0)))
      (Lean.Expr.const `Bool.true []))
    (Lean.BinderInfo.default))
  (Lean.BinderInfo.default)
-/
#guard_msgs in
#eval test1

end Lambda


/-! ## Additional Reflect Tests -/

namespace Lambda.Reflect.AdditionalTests

open Lean Elab Tactic Expr Meta Term
open Std (ToFormat Format format)
open LTy.Syntax LExpr.Syntax

def test1' : MetaM Lean.Expr :=
  LExpr.toExpr
    (.quant () .all (some mty[int]) (LExpr.noTrigger ()) (.eq () (.fvar () "x" mty[int]) (.bvar () 0)))

elab "test1" : term => do
  let result ← liftM test1'
  return result

/-- info: ∀ (x x_1 : Int), (x == x_1) = true : Prop -/
#guard_msgs in
#check test1


def test2 : MetaM Lean.Expr :=
  LExpr.toExpr
    (LExpr.app () (.abs () (some mty[bool]) (.bvar () 0)) (.eq () (.const () (.intConst 4)) (.const () (.intConst 4))))


elab "test2" : term => do
  let result ← liftM test2
  return result

/-- info: (fun x => x) (4 == 4) = true : Prop -/
#guard_msgs in
#check test2

elab "elaborate_lexpr" "[" e:term "]" : term => unsafe do
  let expr ← elabTerm e none
  let lexpr ← Lean.Meta.evalExpr (LExpr MonoString)
    (mkApp (mkConst ``LExpr) (mkConst ``MonoString)) expr
  let result ← liftM (LExpr.toExpr lexpr)
  return result

/-- info: true -/
#guard_msgs in
#eval elaborate_lexpr [@LExpr.eq MonoString ()
                        (@LExpr.const MonoString () (.intConst 5))
                        (@LExpr.const MonoString () (.intConst 5))]

/-- info: ∀ (x : Int), (x == 5) = true : Prop -/
#guard_msgs in
#check elaborate_lexpr [@LExpr.eq MonoString ()
                          (@LExpr.fvar MonoString () "x" (Option.some (LMonoTy.int)))
                          (@LExpr.const MonoString () (.intConst 5))]

end Lambda.Reflect.AdditionalTests
