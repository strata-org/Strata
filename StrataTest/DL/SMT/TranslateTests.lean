/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Translate

open Lean
open Strata
open SMT
open Elab Command

def elabQuery (ctx : Core.SMT.Context) (assums : List SMT.Term) (conc : SMT.Term) : CommandElabM Unit := do
  runTermElabM fun _ => do
    let e ← translateQueryMeta ctx assums conc
    Meta.check e
    logInfo e

/-- info: ∀ (a : Int), 42 > a -/
#guard_msgs in
#eval
  let a := { id := "a", ty := .prim .int }
  (elabQuery {} [] (.quant .all [a] a (.app .gt [.prim (.int 42), a] (.prim .int))))

/--
info: ∀ (α : Type → Type → Type) [inst : ∀ (α_1 α_2 : Type), Nonempty (α α_1 α_2)] (β : Type) [inst : Nonempty β]
  (γ : Type → Type) [inst : ∀ (α : Type), Nonempty (γ α)] (a : α β Prop) (b : γ (α β Prop)) (f : α β Prop → β),
  a = a ∧ b = b
-/
#guard_msgs in
#eval
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let γ := { name := "γ", arity := 1 }
  let f := { id := "f", args := [{ id := "x", ty := .constr α.name [.constr β.name [], .prim .bool] }], out := .constr β.name [] }
  let a := { id := "a", args := [], out := .constr α.name [.constr β.name [], .prim .bool] }
  let b := { id := "b", args := [], out := .constr γ.name [.constr α.name [.constr β.name [], .prim .bool]] }
  elabQuery { sorts := #[α, β, γ], ufs := #[a, b, f] } [] (.app .and [(.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool)), (.app .eq [.app (.uf b) [] b.out, .app (.uf b) [] b.out] (.prim .bool))] (.prim .bool))

/-- info: (if -5 < 0 then - -5 else -5) = 5 -/
#guard_msgs in
#eval
  elabQuery {} [] (.app .eq [(.app .abs [(.prim (.int (-5)))] (.prim .int)), (.prim (.int 5))] (.prim .bool))

/-- info: (if 0 = 0 then 0 else 1) = 0 -/
#guard_msgs in
#eval
  let c := .app .eq [(.prim (.int 0)), (.prim (.int 0))] (.prim .bool)
  let t := .app .ite [c, (.prim (.int 0)), (.prim (.int 1))] (.prim .int)
  elabQuery {} [] (.app .eq [t, (.prim (.int 0))] (.prim .bool))

-- Int literal as the first operand of `.app .eq`: previously built
-- `@Eq Prop 5 ...` because `.prim (.int 5)` returned `(mkProp, _)`.
/-- info: 5 = -5 -/
#guard_msgs in
#eval
  elabQuery {} [] (.app .eq [(.prim (.int 5)), (.app .neg [(.prim (.int 5))] (.prim .int))] (.prim .bool))

-- Int literal as the first operand of arithmetic: `leftAssocOp` propagates the
-- first operand's type as the whole expression's type, so before the fix the
-- entire `add` was typed `Prop`.
/-- info: 1 + 2 = 3 -/
#guard_msgs in
#eval
  elabQuery {} [] (.app .eq [(.app .add [(.prim (.int 1)), (.prim (.int 2))] (.prim .int)), (.prim (.int 3))] (.prim .bool))

-- Int literal as a branch of a nested ITE: exercises type propagation across
-- nested conditionals.
/-- info: (if 0 = 0 then if 0 = 0 then 1 else 2 else 3) = 1 -/
#guard_msgs in
#eval
  let c := .app .eq [(.prim (.int 0)), (.prim (.int 0))] (.prim .bool)
  let inner := .app .ite [c, (.prim (.int 1)), (.prim (.int 2))] (.prim .int)
  let outer := .app .ite [c, inner, (.prim (.int 3))] (.prim .int)
  elabQuery {} [] (.app .eq [outer, (.prim (.int 1))] (.prim .bool))
