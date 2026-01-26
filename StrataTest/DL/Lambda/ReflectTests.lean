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

/-- info: true -/
#guard_msgs in
#eval elaborate_lexpr [@LExpr.eq MonoString ()
                        (@LExpr.const MonoString () (.intConst 5))
                        (@LExpr.const MonoString () (.intConst 5))]

end Lambda
