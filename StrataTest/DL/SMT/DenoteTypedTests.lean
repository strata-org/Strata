/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all Strata.DL.SMT.DenoteTyped
import all Strata.DL.SMT.Term
import all Strata.DL.SMT.TermType
import all Strata.DL.SMT.Op

/-! ## Unit tests for the SMT Term type checker (`Term.typeCheck`)

`Term.typeCheck` (`Strata.DL.SMT.DenoteTyped`) is a total, pure function
`TypedContext → Term → Except String TermType`; the `#guard`s compare `.toOption`
against `some`/`none` to stay robust against the exact error strings.

Every branch of `Term.typeCheck` gets at least one positive and one negative case;
the helpers `typeCheckArgs` (UF / `distinct`), `typeCheckAll` / `wfTriggers`
(quantifier triggers), and `WFSort` / `isBase` are exercised transitively.
-/

meta section
namespace Strata.SMT.DenoteTyped

/-! ### Shared fixtures -/

/-- Empty typing context: no sorts, functions, or variables declared. -/
private def emptyCtx : TypedContext := { uss := [], ufs := [], Γ := [] }

/-- An integer-typed variable `x`. -/
private def xInt : TermVar := { id := "x", ty := .int }

/-- Context declaring `x : Int`. -/
private def ctxX : TypedContext := { uss := [], ufs := [], Γ := [xInt] }

/-- A second integer-typed variable `y`. -/
private def yInt : TermVar := { id := "y", ty := .int }

/-- A bool-typed variable also named `x` (used to exercise same-name binder shadowing). -/
private def xBool : TermVar := { id := "x", ty := .bool }

/-- An uninterpreted function `f : Int → Bool`. -/
private def fUF : UF := { id := "f", args := [.int], out := .bool }

/-- Context declaring `f : Int → Bool`. -/
private def ctxF : TypedContext := { uss := [], ufs := [fUF], Γ := [] }

/-- A UF whose output sort is an undeclared constructor (used to exercise the `WFSort` guard on a
    UF signature). -/
private def gUF : UF := { id := "g", args := [.int], out := .constr "Bogus" [] }

/-- An `(Array Int Bool)`-typed variable `a`. -/
private def aArr : TermVar := { id := "a", ty := .constr "Array" [.int, .bool] }

/-- Context declaring `a : (Array Int Bool)`. -/
private def ctxA : TypedContext := { uss := [], ufs := [], Γ := [aArr] }

/-- Context declaring a nullary uninterpreted sort `Foo`. -/
private def ctxSort : TypedContext := { uss := [{ name := "Foo", arity := 0 }], ufs := [], Γ := [] }

/-! ### Primitive literals -/

#guard (Term.typeCheck emptyCtx (.prim (.bool true))).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.prim (.int 5))).toOption == some .int
#guard (Term.typeCheck emptyCtx (.prim (.string "hi"))).toOption == some .string
#guard (Term.typeCheck emptyCtx (.prim (.bitvec (0 : BitVec 8)))).toOption == some (.bitvec 8)
-- `real` is not a denotable base sort (`isBase` rejects it).
#guard (Term.typeCheck emptyCtx (.prim (.real ⟨1, 0⟩))).toOption == none

/-! ### Variables -/

#guard (Term.typeCheck ctxX (.var xInt)).toOption == some .int
-- Absent from the context.
#guard (Term.typeCheck emptyCtx (.var xInt)).toOption == none
-- Present under the same name but with a mismatched declared type.
#guard (Term.typeCheck ctxX (.var { id := "x", ty := .bool })).toOption == none

/-! ### Uninterpreted function applications -/

#guard (Term.typeCheck ctxF (.app (.uf fUF) [.prim (.int 3)] .bool)).toOption == some .bool
-- Undeclared function.
#guard (Term.typeCheck emptyCtx (.app (.uf fUF) [.prim (.int 3)] .bool)).toOption == none
-- The function symbol is shadowed by a bound variable of the same id.
#guard (Term.typeCheck { uss := [], ufs := [fUF], Γ := [{ id := "f", ty := .int }] }
  (.app (.uf fUF) [.prim (.int 3)] .bool)).toOption == none
-- Declared return type disagrees with the function's output sort.
#guard (Term.typeCheck ctxF (.app (.uf fUF) [.prim (.int 3)] .int)).toOption == none
-- Argument type disagrees with the function's input sort.
#guard (Term.typeCheck ctxF (.app (.uf fUF) [.prim (.bool true)] .bool)).toOption == none
-- A UF whose signature references an undeclared sort → rejected by the `WFSort` guard on the signature.
#guard (Term.typeCheck { uss := [], ufs := [gUF], Γ := [] }
  (.app (.uf gUF) [.prim (.int 1)] (.constr "Bogus" []))).toOption == none

/-! ### `not` -/

#guard (Term.typeCheck emptyCtx (.app .not [.prim (.bool true)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .not [.prim (.int 1)] .bool)).toOption == none
-- Wrong arity falls through to the catch-all.
#guard (Term.typeCheck emptyCtx (.app .not [] .bool)).toOption == none

/-! ### `and` / `or` / `implies` -/

#guard (Term.typeCheck emptyCtx (.app .and [.prim (.bool true), .prim (.bool false)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .or [.prim (.bool true), .prim (.bool false)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .implies [.prim (.bool true), .prim (.bool false)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .and [.prim (.bool true), .prim (.int 1)] .bool)).toOption == none

/-! ### `eq` -/

#guard (Term.typeCheck emptyCtx (.app .eq [.prim (.int 1), .prim (.int 2)] .bool)).toOption == some .bool
-- Operands of different types.
#guard (Term.typeCheck emptyCtx (.app .eq [.prim (.int 1), .prim (.bool true)] .bool)).toOption == none

/-! ### `ite` -/

#guard (Term.typeCheck emptyCtx (.app .ite [.prim (.bool true), .prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
-- Non-boolean condition.
#guard (Term.typeCheck emptyCtx (.app .ite [.prim (.int 0), .prim (.int 1), .prim (.int 2)] .int)).toOption == none
-- Branches of different types.
#guard (Term.typeCheck emptyCtx (.app .ite [.prim (.bool true), .prim (.int 1), .prim (.bool false)] .int)).toOption == none

/-! ### Integer arithmetic -/

#guard (Term.typeCheck emptyCtx (.app .neg [.prim (.int 5)] .int)).toOption == some .int
#guard (Term.typeCheck emptyCtx (.app .neg [.prim (.bool true)] .int)).toOption == none
#guard (Term.typeCheck emptyCtx (.app .add [.prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
#guard (Term.typeCheck emptyCtx (.app .sub [.prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
#guard (Term.typeCheck emptyCtx (.app .mul [.prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
#guard (Term.typeCheck emptyCtx (.app .div [.prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
#guard (Term.typeCheck emptyCtx (.app .mod [.prim (.int 1), .prim (.int 2)] .int)).toOption == some .int
-- A non-integer operand.
#guard (Term.typeCheck emptyCtx (.app .add [.prim (.int 1), .prim (.bool true)] .int)).toOption == none

/-! ### Integer comparisons -/

#guard (Term.typeCheck emptyCtx (.app .le [.prim (.int 1), .prim (.int 2)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .lt [.prim (.int 1), .prim (.int 2)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .ge [.prim (.int 1), .prim (.int 2)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .gt [.prim (.int 1), .prim (.int 2)] .bool)).toOption == some .bool
#guard (Term.typeCheck emptyCtx (.app .lt [.prim (.int 1), .prim (.bool true)] .bool)).toOption == none

/-! ### `distinct` (variadic, ≥ 2 args, all one type) -/

#guard (Term.typeCheck emptyCtx
  (.app .distinct [.prim (.int 1), .prim (.int 2), .prim (.int 3)] .bool)).toOption == some .bool
-- Mixed argument types.
#guard (Term.typeCheck emptyCtx
  (.app .distinct [.prim (.int 1), .prim (.bool true)] .bool)).toOption == none
-- Fewer than two arguments does not match the pattern (catch-all).
#guard (Term.typeCheck emptyCtx (.app .distinct [.prim (.int 1)] .bool)).toOption == none

/-! ### Quantifiers -/

-- `∀ x : Int, x < 5`, with the bound variable used in the body (confirms the binder is in scope).
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt] (.var xInt) (.app .lt [.var xInt, .prim (.int 5)] .bool))).toOption == some .bool
-- `∃`, same shape.
#guard (Term.typeCheck emptyCtx
  (.quant .exist [xInt] (.var xInt) (.app .lt [.var xInt, .prim (.int 5)] .bool))).toOption == some .bool
-- A proper `triggers` group as the trigger (exercises `wfTriggers` / `typeCheckAll`).
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt] (.app .triggers [.var xInt] .bool)
    (.app .lt [.var xInt, .prim (.int 5)] .bool))).toOption == some .bool
-- Non-boolean body.
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt] (.var xInt) (.prim (.int 1)))).toOption == none
-- Bound variable with an undeclared sort → rejected by the `WFSort` guard.
#guard (Term.typeCheck emptyCtx
  (.quant .all [{ id := "z", ty := .constr "Bogus" [] }]
    (.var { id := "z", ty := .constr "Bogus" [] }) (.prim (.bool true)))).toOption == none
-- Ill-typed trigger pattern → rejected by `wfTriggers`.
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt] (.app .triggers [.prim (.real ⟨1, 0⟩)] .bool)
    (.app .lt [.var xInt, .prim (.int 5)] .bool))).toOption == none
-- Multi-binder group (`vs.length > 1`, so `vs.reverse` is non-trivial): both variables are in scope.
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt, yInt] (.var xInt) (.app .lt [.var xInt, .var yInt] .bool))).toOption == some .bool
-- Same-name binders in one group: after `reverse` the last-listed binder (`xInt`) wins, so a
-- reference at the shadowed earlier binder's sort (`xBool`) no longer resolves.
#guard (Term.typeCheck emptyCtx
  (.quant .all [xBool, xInt] (.var xInt) (.app .eq [.var xBool, .var xBool] .bool))).toOption == none

/-! ### Option literals -/

#guard (Term.typeCheck emptyCtx (.none .int)).toOption == some (.option .int)
#guard (Term.typeCheck emptyCtx (.some (.prim (.int 3)))).toOption == some (.option .int)
-- Inner term ill-typed → `.some` propagates the failure.
#guard (Term.typeCheck emptyCtx (.some (.prim (.real ⟨1, 0⟩)))).toOption == none
-- `none` at a non-denotable primitive sort is rejected (`WFSort` admits only base sorts).
#guard (Term.typeCheck emptyCtx (.none .real)).toOption == none
-- A `none` at an undeclared (malformed) sort.
#guard (Term.typeCheck emptyCtx (.none (.constr "Foo" []))).toOption == none
-- A `none` at a declared uninterpreted sort is accepted (exercises the `uss.any` branch of `WFSort`).
#guard (Term.typeCheck ctxSort (.none (.constr "Foo" []))).toOption == some (.option (.constr "Foo" []))
-- An undeclared sort is still rejected even when other sorts are declared.
#guard (Term.typeCheck ctxSort (.none (.constr "Bar" []))).toOption == none

/-! ### Array `select` -/

#guard (Term.typeCheck ctxA (.app .select [.var aArr, .prim (.int 0)] .bool)).toOption == some .bool
-- Index type does not match the array's key sort.
#guard (Term.typeCheck ctxA (.app .select [.var aArr, .prim (.bool true)] .bool)).toOption == none
-- First argument is not an array.
#guard (Term.typeCheck emptyCtx (.app .select [.prim (.int 0), .prim (.int 0)] .int)).toOption == none

/-! ### Array `store` -/

#guard (Term.typeCheck ctxA
  (.app .store [.var aArr, .prim (.int 0), .prim (.bool true)] (.constr "Array" [.int, .bool]))
   ).toOption == some (.constr "Array" [.int, .bool])
-- Stored element type does not match the array's value sort.
#guard (Term.typeCheck ctxA
  (.app .store [.var aArr, .prim (.int 0), .prim (.int 9)] (.constr "Array" [.int, .bool]))).toOption == none

/-! ### Nested / recursive terms -/

-- Nested arithmetic: an `add` whose first operand is itself a `mul`.
#guard (Term.typeCheck emptyCtx
  (.app .add [.app .mul [.prim (.int 2), .prim (.int 3)] .int, .prim (.int 1)] .int)).toOption == some .int
-- Nested quantifier: `∀ x : Int, ∃ y : Int, x < y`, exercising the recursive binder-pushing path.
#guard (Term.typeCheck emptyCtx
  (.quant .all [xInt] (.var xInt)
    (.quant .exist [yInt] (.var yInt) (.app .lt [.var xInt, .var yInt] .bool)))).toOption == some .bool

/-! ### Unsupported operators (catch-all) -/

-- Bit-vector operators are outside the type-checked fragment.
#guard (Term.typeCheck emptyCtx (.app (.bv .bvadd) [] (.bitvec 8))).toOption == none

end Strata.SMT.DenoteTyped
end
