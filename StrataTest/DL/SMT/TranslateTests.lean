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
