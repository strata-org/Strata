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
import all Strata.Util.OrderedSet
import all Strata.Util.OrderedSetProps
import Std.Data.HashMap.Lemmas

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
  `(tactic| (simp (disch := decide) only [denoteQuery, hashset_empty_isEmpty, array_empty_isEmpty, map_empty_isEmpty,
                         Strata.Util.OrderedSet.toList_empty, Strata.Util.OrderedKeyedSet.toList_empty,
                         Strata.Util.OrderedKeyedSet.toList_ofArrayUnchecked, Std.HashMap.isEmpty_empty,
                         Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
                         option_bind_some, option_map_some, option_pure_bind, Option.map];
             rfl))

-- For examples with `sorts := #[...]`, `denoteBoolTermFromContext` involves
-- `bindUS`/`denoteSort` which the kernel cannot fully reduce.  We use the
-- elaborator's `reduce` to normalize the LHS and then clean up the residual
-- `mkTypeFunType`/`mkNonemptyPred` applications.
private theorem mkISContext_nil : mkISContext [] = ∅ := by rfl
private theorem list_reverse_empty_map : List.reverse (∅ : Map α β) = ∅ := by rfl

macro "denoteQuery_sorts_rfl" : tactic =>
  `(tactic| (
    unfold denoteQuery;
    simp (disch := decide) only [hashset_empty_isEmpty, array_empty_isEmpty, map_empty_isEmpty,
               Std.HashMap.isEmpty_empty,
               Strata.Util.OrderedSet.toList_empty, Strata.Util.OrderedKeyedSet.toList_empty,
               Strata.Util.OrderedKeyedSet.toList_ofArrayUnchecked,
               Bool.not_true, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
               option_pure_bind, mkISContext_nil, list_reverse_empty_map,
               List.reverse_nil, List.reverse_cons, List.nil_append,
               mkISContext, mkISContext.go];
    conv => lhs; reduce;
    simp only [mkTypeFunType, Nat.repeat, mkNonemptyPred, denoteBoolTermFromContext.closeTermEnv];
    rfl))


/-! SMT-LIB leaves integer `div` and `mod` by zero unspecified, so their
denotation quantifies over every model's values at a zero divisor: neither
Lean's `5 / 0 = 0` nor its `5 % 0 = 5` holds in the denotation. -/

private def int (i : Int) : Term := .prim (.int i)
private def intEq (a b : Term) : Term := .app .eq [a, b] (.prim .bool)

/-- The denotation of `5 div 0 = 0` quantifies over the model's `divByZero`, instead of using Lean's `5 / 0 = 0`. -/
private theorem denote_div_zero :
    denoteQuery {} [] (intEq (.app .div [int 5, int 0] (.prim .int)) (int 0)) =
    .some (∀ (divByZero _modByZero : Int → Int),
      (if (0 : Int) = 0 then divByZero 5 else 5 / 0) = 0) := by
  denoteQuery_rfl

example (P : Prop) (h : denoteQuery {} [] (intEq (.app .div [int 5, int 0] (.prim .int)) (int 0)) = some P) :
    ¬ P := by
  obtain rfl := Option.some.inj (denote_div_zero.symm.trans h)
  intro hP
  simpa using hP (fun _ => 1) id

/-- The denotation of `5 mod 0 = 5` quantifies over the model's `modByZero`, instead of using Lean's `5 % 0 = 5`. -/
private theorem denote_mod_zero :
    denoteQuery {} [] (intEq (.app .mod [int 5, int 0] (.prim .int)) (int 5)) =
    .some (∀ (_divByZero modByZero : Int → Int),
      (if (0 : Int) = 0 then modByZero 5 else 5 % 0) = 5) := by
  denoteQuery_rfl

example (P : Prop) (h : denoteQuery {} [] (intEq (.app .mod [int 5, int 0] (.prim .int)) (int 5)) = some P) :
    ¬ P := by
  obtain rfl := Option.some.inj (denote_mod_zero.symm.trans h)
  intro hP
  simpa using hP id (fun _ => 0)

/-! The values at a zero divisor are chosen once per model, for the whole
query: two occurrences of `x div 0` are equal, but `5 div 0` and `6 div 0`
need not be. -/

example : denoteQuery {} []
    (.quant .all [⟨"x", .prim .int⟩] []
      (intEq (.app .div [.var ⟨"x", .prim .int⟩, int 0] (.prim .int))
             (.app .add [.app .div [.var ⟨"x", .prim .int⟩, int 0] (.prim .int), int 0] (.prim .int)))) =
    .some (∀ (divByZero _modByZero : Int → Int) (x : Int),
      (if (0 : Int) = 0 then divByZero x else x / 0) = (if (0 : Int) = 0 then divByZero x else x / 0) + 0) := by
  denoteQuery_rfl

/-- The denotation of `5 div 0 = 6 div 0` applies the model's `divByZero` to each dividend, so the two sides need not be equal. -/
private theorem denote_div_zero_distinct :
    denoteQuery {} [] (intEq (.app .div [int 5, int 0] (.prim .int)) (.app .div [int 6, int 0] (.prim .int))) =
    .some (∀ (divByZero _modByZero : Int → Int),
      (if (0 : Int) = 0 then divByZero 5 else 5 / 0) = (if (0 : Int) = 0 then divByZero 6 else 6 / 0)) := by
  denoteQuery_rfl

example (P : Prop)
    (h : denoteQuery {} [] (intEq (.app .div [int 5, int 0] (.prim .int)) (.app .div [int 6, int 0] (.prim .int))) = some P) :
    ¬ P := by
  obtain rfl := Option.some.inj (denote_div_zero_distinct.symm.trans h)
  intro hP
  simpa using hP id id

/-! `usesIntDivMod` finds a `div` or `mod` under every constructor that holds
subterms, so no query that uses them is denoted with Lean's values. -/

private def d50 : Term := .app .div [int 5, int 0] (.prim .int)
private def vI : TermVar := ⟨"v", .prim .int⟩
#guard Term.hasIntDivMod d50
#guard Term.hasIntDivMod (.app .mod [int 5, int 0] (.prim .int))
#guard Term.hasIntDivMod (.some d50)
#guard Term.hasIntDivMod (intEq (.app .add [int 1, d50] (.prim .int)) (int 0))
#guard Term.hasIntDivMod (.quant .all [vI] [] (intEq d50 (.var vI)))
#guard Term.hasIntDivMod (.quant .all [vI] [[d50]] (intEq (.var vI) (.var vI)))
#guard !Term.hasIntDivMod (intEq (.app .add [int 1, int 0] (.prim .int)) (int 1))
private def fDiv : IF := { id := "f", args := [vI], out := .prim .int, body := .app .div [.var vI, int 0] (.prim .int) }
#guard usesIntDivMod [fDiv] (.prim (.bool true))
private def wI : TermVar := ⟨"w", .prim .int⟩
private def quantDiv : Term := .quant .all [wI] [] (intEq (.app .div [.var vI, .var wI] (.prim .int)) (int 0))
private def fQuantDiv : IF := { id := "g", args := [vI], out := .prim .bool, body := quantDiv }
#guard usesIntDivMod [fQuantDiv] (.prim (.bool true))

/-! Constant folding leaves a zero divisor alone. -/
#guard Factory.intDiv (int 5) (int 0) matches .app .div _ _
#guard Factory.intMod (int 5) (int 0) matches .app .mod _ _
#guard Factory.intDiv (int 6) (int 2) matches .prim (.int 3)

/-! `div`, like `mod`, is binary: a three-operand `div` has no denotation. -/
example : denoteQuery {} [] (intEq (.app .div [int 12, int 3, int 2] (.prim .int)) (int 2)) = none := by
  denoteQuery_rfl

/-- info: some (Int.ofNat 3) -/
#guard_msgs in
#reduce denoteIntTermAux (.app .add [.prim (.int 1), .prim (.int 2)] (.prim .int))

/-- info: some (Int.ofNat 0).NonNeg -/
#guard_msgs in
#reduce (types := true) denoteBoolTermAux (.app .lt [.prim (.int 1), .prim (.int 2)] (.prim .int))

example :
  let a := { id := "a", ty := .prim .int }
  (denoteBoolTermAux (.quant .all [a] [] (.app .gt [.prim (.int 42), a] (.prim .int)))) =
  .some (∀ (x : Int), 42 > x) := by
  rfl

example :
  let a := { id := "a", ty := .prim (.bitvec 32) }
  (denoteQuery {} [] (.quant .all [a] [] (.app .bvugt [.prim (.bitvec (42 : BitVec 32)), a] (.prim (.bitvec 32))))) =
  .some (∀ (_divByZero _modByZero : Int → Int) (x : BitVec 32), 42 > x) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [],  out := .prim (.bitvec 32) }
  let b := { id := "b", args := [],  out := .prim (.bitvec 16) }
  (denoteQuery { ufs := .ofArrayUnchecked #[a, b] } []
    (.app .eq [.app .bvconcat [.app (.uf a) [] a.out, .app (.uf b) [] b.out] (.prim (.bitvec 48)),
               .app .bvconcat [.app (.uf b) [] b.out, .app (.uf a) [] a.out] (.prim (.bitvec 48))] (.prim .bool))) =
  .some (∀ (_divByZero _modByZero : Int → Int) (x : BitVec 32) (y : BitVec 16), x ++ y = y ++ x) := by
  denoteQuery_rfl

example :
  let α := { name := "α", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [] }
  (denoteQuery { sorts := .ofArrayUnchecked #[α], ufs := .ofArrayUnchecked #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type) [Nonempty α] (_divByZero _modByZero : Int → Int) (x : α), x = x) := by
  denoteQuery_sorts_rfl

example :
  let α := { name := "α", arity := 1 }
  let a := { id := "a", args := [],  out := .constr α.name [.prim .int] }
  (denoteQuery { sorts := .ofArrayUnchecked #[α], ufs := .ofArrayUnchecked #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type) [∀ x, Nonempty (α x)] (_divByZero _modByZero : Int → Int) (x : α Int), x = x) := by
  denoteQuery_sorts_rfl

example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let a := { id := "a", args := [],  out := .constr α.name [.constr β.name [], .prim .bool] }
  (denoteQuery { sorts := .ofArrayUnchecked #[α, β], ufs := .ofArrayUnchecked #[a] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ x y, Nonempty (α x y)] (β : Type) [Nonempty β] (_divByZero _modByZero : Int → Int) (x : α β Prop), x = x) := by
  denoteQuery_sorts_rfl

example :
  let α := { name := "α", arity := 2 }
  let β := { name := "β", arity := 0 }
  let γ := ("γ", .constr α.name [.constr β.name [], .prim .bool])
  let a := { id := "a", args := [],  out := .constr γ.fst [] }
  (denoteQuery { sorts := .ofArrayUnchecked #[α, β], ufs := .ofArrayUnchecked #[a], tySubst := [γ] } [] (.app .eq [.app (.uf a) [] a.out, .app (.uf a) [] a.out] (.prim .bool))) =
  .some (∀ (α : Type → Type → Type) [∀ (x y : Type), Nonempty (α x y)] (β : Type) [Nonempty β],
         let γ := α β Prop
         ∀ (_divByZero _modByZero : Int → Int) (a : γ), a = a) := by
  denoteQuery_sorts_rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .constr α.fst [] }
  (denoteQuery { ufs := .ofArrayUnchecked #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (_divByZero _modByZero : Int → Int) (a : α), ¬a) := by
  denoteQuery_rfl

example :
  let α := ("α", .prim .bool)
  let a := { id := "a", args := [],  out := .prim .bool }
  (denoteQuery { ufs := .ofArrayUnchecked #[a], tySubst := [α] } [] (.app .not [.app (.uf a) [] a.out] (.prim .bool))) =
  .some (let α := Prop
         ∀ (_divByZero _modByZero : Int → Int) (a : α), ¬a) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [],  out := .prim .int }
  (denoteQuery { ufs := .ofArrayUnchecked #[a] } [] (.app .gt [.prim (.int 42), .app (.uf a) [] a.out] (.prim .int))) =
  .some (∀ (_divByZero _modByZero : Int → Int) (x : Int), 42 > x) := by
  denoteQuery_rfl

example :
  let a := { id := "a", args := [], out := .prim .int }
  (denoteQuery {ufs := .ofArrayUnchecked #[a]} [] (.app .gt [.prim (.int 42), .app (.uf a) [] (.prim .int)] (.prim .int))) =
  .some (∀ (_divByZero _modByZero : Int → Int) (x : Int), 42 > x) := by
  denoteQuery_rfl

example :
  let f : UF := { id := "f", args := [.prim .int], out := .prim .int }
  let f3 := .app (.uf f) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ufs := .ofArrayUnchecked #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (∀ (_divByZero _modByZero : Int → Int) (f : Int → Int), 42 > f 3) := by
  denoteQuery_rfl

example :
  let a : TermVar := { id := "a", ty := .prim .int }
  let f : IF := { id := "f", args := [a], out := .prim .int, body := .app .add [.var a, .prim (.int 2)] (.prim .int) }
  let f3 := .app (.uf f.toUF) [.prim (.int 3)] (.prim .int)
  (denoteQuery {ifs := .ofArrayUnchecked #[f]} [] (.app .gt [.prim (.int 42), f3] (.prim .int))) =
  .some (∀ (_divByZero _modByZero : Int → Int), let f (a : Int) := a + 2; 42 > f 3) := by
  denoteQuery_rfl

example :
  let ctx := {
      sorts := .ofArrayUnchecked #[],
      ufs := .ofArrayUnchecked #[{ id := "$__n0", args := [], out := TermType.prim (TermPrimType.int) }],
      ifs := .ofArrayUnchecked #[],
      axms := .ofArrayUnchecked #[],
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
  .some (∀ (_divByZero _modByZero : Int → Int) («$__n0» : Int), 0 < «$__n0» → «$__n0» ≥ 0 → 0 ≤ «$__n0» ∧ True) := by
  denoteQuery_rfl
end
