/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
meta import all Strata.DL.SMT.Denote
import all Strata.DL.SMT.TermType
import all Strata.DL.SMT.Term
import all Strata.DL.SMT.Op
import all Strata.Languages.Core.SMTEncoder


meta section

open Strata.SMT

-- In the module system, some definition bodies from non-module libraries (Std,
-- Init) are opaque to the kernel. We prove the needed emptiness facts via
-- `native_decide` and then use `simp` to rewrite them before `rfl`.
private theorem hashset_empty_isEmpty : ({} : Std.HashSet String).isEmpty = true := by
  native_decide
@[simp] private theorem array_empty_isEmpty :
    (#[] : Array α).isEmpty = true := by rfl
@[simp] private theorem map_empty_isEmpty :
    (Map.empty : Map α β).isEmpty = true := by rfl

-- The `denoteQuery` function uses `Std.HashSet.isEmpty` which is opaque
-- to the kernel in the module system. We unfold `denoteQuery`, resolve
-- the isEmpty checks, and normalize the Option monad before `rfl`.
-- Helper lemmas to normalize `Option` monad operations that the kernel
-- cannot reduce in the module system.
private theorem option_bind_some {f : α → Option β} {x : α} :
    Option.bind (some x) f = f x := rfl
private theorem option_map_some {f : α → β} {x : α} :
    Option.map f (some x) = some (f x) := rfl

-- The `do { pure PUnit.unit; body }` desugars to `Bind.bind (pure PUnit.unit) (fun _ => body)`.
-- In the `Option` monad, `pure x = some x`, so after simp it becomes
-- `Option.bind (some PUnit.unit) (fun _ => body) = body`.
-- We add a `Pure.pure` + `Bind.bind` rewrite to handle this pattern.
private theorem option_pure_bind {f : PUnit → Option β} :
    (Bind.bind (Pure.pure PUnit.unit : Option PUnit) f : Option β) = f PUnit.unit := rfl

macro "denoteQuery_rfl" : tactic =>
  `(tactic| (simp only [denoteQuery, hashset_empty_isEmpty, array_empty_isEmpty, map_empty_isEmpty,
                         Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
                         option_bind_some, option_map_some, option_pure_bind, Option.map];
             rfl))

-- For examples with `sorts := #[...]`, `denoteBoolTermFromContext` involves
-- `bindUS`/`denoteSort` which the kernel cannot fully reduce.  We use the
-- elaborator's `reduce` to normalize the LHS and then clean up the residual
-- `mkTypeFunType`/`mkNonemptyPred` applications.
private theorem mkISContext_nil : mkISContext [] = ∅ := by rfl
private theorem list_reverse_empty_map : List.reverse (∅ : Map α β) = ∅ := by rfl

set_option linter.unusedSimpArgs false in
macro "denoteQuery_sorts_rfl" : tactic =>
  `(tactic| (
    unfold denoteQuery;
    simp only [hashset_empty_isEmpty, array_empty_isEmpty, map_empty_isEmpty,
               Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
               option_pure_bind, mkISContext_nil, list_reverse_empty_map,
               List.reverse_nil, List.reverse_cons, List.nil_append,
               mkISContext, mkISContext.go];
    conv => lhs; reduce;
    simp only [mkTypeFunType, Nat.repeat, mkNonemptyPred];
    rfl))

/-- info: some (Int.ofNat 3) -/
#guard_msgs in
#reduce denoteIntTermAux (.app .add [.prim (.int 1), .prim (.int 2)] (.prim .int))

/-- info: some (Int.ofNat 0).NonNeg -/
#guard_msgs in
#reduce (types := true) denoteBoolTermAux (.app .lt [.prim (.int 1), .prim (.int 2)] (.prim .int))

example :
  let a := { id := "a", ty := .prim .int }
  (denoteBoolTermAux (.quant .all [a] a (.app .gt [.prim (.int 42), a] (.prim .int)))) =
  .some (∀ (x : Int), 42 > x) := by
  rfl

example :
  let a := { id := "a", ty := .prim (.bitvec 32) }
  (denoteQuery {} [] (.quant .all [a] a (.app .bvugt [.prim (.bitvec (42 : BitVec 32)), a] (.prim (.bitvec 32))))) =
  .some (∀ (x : BitVec 32), 42 > x) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [],  out := .prim (.bitvec 32) }
  let b := { id := "b", args := [],  out := .prim (.bitvec 16) }
  (denoteQuery { ufs := #[a, b] } []
    (.app .eq [.app .bvconcat [.app (.uf a) [] a.out, .app (.uf b) [] b.out] (.prim (.bitvec 48)),
               .app .bvconcat [.app (.uf b) [] b.out, .app (.uf a) [] a.out] (.prim (.bitvec 48))] (.prim .bool))) =
  .some (∀ (x : BitVec 32) (y : BitVec 16), x ++ y = y ++ x) := by
  denoteQuery_rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
example :
  let α := { name := "α", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [] }
  (denoteQuery { sorts := #[α], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type) [Nonempty α] (x : α), x = x) := by
  denoteQuery_sorts_rfl

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 4096 in
example :
  let α := { name := "α", arity := 1 }
  let a := { id := "a", args := [],  out := .constr α.name [.prim .int] }
  (denoteQuery { sorts := #[α], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type) [∀ x, Nonempty (α x)] (x : α Int), x = x) := by
  denoteQuery_sorts_rfl

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 4096 in
example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [.constr β.name [], .prim .bool] }
  (denoteQuery { sorts := #[α, β], ufs := #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ x y, Nonempty (α x y)] (β : Type) [Nonempty β] (x : α β Prop), x = x) := by
  denoteQuery_sorts_rfl

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 4096 in
example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let γ := ("γ", .constr α.name [.constr β.name [], .prim .bool])
  let a := { id := "a", args := [],  out := .constr γ.fst [] }
  (denoteQuery { sorts := #[α, β], ufs := #[a], tySubst := [γ] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ (x y : Type), Nonempty (α x y)] (β : Type) [Nonempty β],
         let γ := α β Prop
         ∀ (a : γ), a = a) := by
  denoteQuery_sorts_rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .constr α.fst [] }
  (denoteQuery { ufs := #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (a : α), ¬a) := by
  denoteQuery_rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .prim .bool }
  (denoteQuery { ufs := #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (a : α), ¬a) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [],  out := .prim .int }
  (denoteQuery { ufs := #[a] } [] (.app .gt [.prim (.int 42), .app (.uf a) [] a.out] (.prim .int))) =
  .some (∀ (x : Int), 42 > x) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [], out := .prim .int }
  (denoteQuery {ufs := #[a]} [] (.app .gt [.prim (.int 42), .app (.uf a) [] (.prim .int)] (.prim .int))) =
  .some (∀ (x : Int), 42 > x) := by
  denoteQuery_rfl

example :
  let f := { id := "f", args := [{ id := "a", ty := .prim .int }], out := .prim .int }
  let f3 := .app (.uf f) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ufs := #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (∀ (f : Int → Int), 42 > f 3) := by
  denoteQuery_rfl

example :
  let a := { id := "a", ty := .prim .int }
  let f := { uf := { id := "f", args := [a], out := .prim .int }, body := .app .add [.var a, .prim (.int 2)] (.prim .int) }
  let f3 := .app (.uf f.uf) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ifs := #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (let f (a : Int) := a + 2; 42 > f 3) := by
  denoteQuery_rfl

example :
  let ctx := {
      sorts := #[],
      ufs := #[{ id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }],
      ifs := #[],
      axms := #[],
      tySubst := [] }
  let ts := [Term.app
       (Op.lt)
       [Term.prim (TermPrim.int 0),
        Term.app
          (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int))]
       (TermType.prim (TermPrimType.bool)),
     Term.app
       (Op.ge)
       [Term.app
          (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int)),
        Term.prim (TermPrim.int 0)]
       (TermType.prim (TermPrimType.bool))]
  let t := Term.app
      (Op.and)
      [Term.app
         (Op.le)
         [Term.prim (TermPrim.int 0),
          Term.app
            (Op.uf { id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }) [] (TermType.prim (TermPrimType.int))]
         (TermType.prim (TermPrimType.bool)),
       Term.prim (TermPrim.bool true)]
      (TermType.prim (TermPrimType.bool))
  (denoteQuery ctx ts t) =
  .some (∀ («$__n0» : Int), 0 < «$__n0» → «$__n0» ≥ 0 → 0 ≤ «$__n0» ∧ True) := by
  denoteQuery_rfl
