/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Transform.Simplify
meta import Strata.Transform.Simplify.Precondition

/-! # Simplify keeps a body whose simplified form fails the def-use check

The phase installs a simplified body only when it is def-use well-formed from the body's
entry variables, with the factory's functions declared (`gateOK`); otherwise it keeps the
body. Here `wrap` is an `inline` function whose body calls `ghost`, which the factory does not
declare, so expanding `wrap(m)` brings in an undeclared operator and the body is kept. -/

meta section

namespace Core.Simplify.FallbackTest

open Lambda Imperative

/-- `inline wrap (n : int) : int := ghost(n)`, with `ghost` not in the factory. -/
def factory : Lambda.Factory CoreLParams :=
  Factory.ofArray #[
    { name := ⟨"wrap", ()⟩, inputs := [(⟨"n", ()⟩, .int)], output := .int,
      body := some (.app default (.op default ⟨"ghost", ()⟩ (some (.arrow .int .int)))
        (.fvar default ⟨"n", ()⟩ (some .int))),
      attr := #[.inline] }]

/-- `assert [a]: wrap(m) == m;`. -/
def body : List Statement :=
  [Statement.assert "a"
    (.eq default (.app default (.op default ⟨"wrap", ()⟩ (some (.arrow .int .int)))
    (.fvar default ⟨"m", ()⟩ (some .int))) (.fvar default ⟨"m", ()⟩ (some .int))) .empty]

-- Simplify expands the call, which brings in `ghost`.
/--
info: [assert [a]: ghost(m) == m;

 -- Errors encountered during conversion:
 Unsupported construct in handleUnaryOps: unknown operation, rendering as generic call: ghost
 Context: Global scope:
   freeVars: [m]]
-/
#guard_msgs (whitespace := lax) in
#eval (sweptBody (Ctx.ofFactory factory []) default body).map Std.format

-- The check fails on that output, so the installed body is the original.
#guard !gateOK factory body (sweptBody (Ctx.ofFactory factory []) default body)

/--
info: [assert [a]: wrap(m) == m;

 -- Errors encountered during conversion:
 Unsupported construct in handleUnaryOps: unknown operation, rendering as generic call: wrap
 Context: Global scope:
   freeVars: [m]]
-/
#guard_msgs (whitespace := lax) in
#eval (checkedBody (Ctx.ofFactory factory []) default body).map Std.format

/-! ## The annotation check

The gate also asks every free-variable annotation in the output to agree with its
declaration in scope or, for a variable the input reads without declaring, with the
input's annotation (`Block.annotsAgreeB`). It can say no. -/

/-- `assert [a]: x == x;`, with both occurrences of `x` annotated `ty`. -/
private def assertEq (x : String) (ty : LMonoTy) : Statement :=
  Statement.assert "a" (.eq default (.fvar default ⟨x, ()⟩ (some ty))
    (.fvar default ⟨x, ()⟩ (some ty))) .empty

/-- `var x : ty;`, without a value. -/
private def declare (x : String) (ty : LMonoTy) : Statement :=
  Statement.init ⟨x, ()⟩ (.forAll [] ty) .nondet .empty

/-- The check, on Core statements. -/
private def agree (ss ss' : List Statement) : Bool :=
  Block.annotsAgreeB (P := Expression) (C := Command) ss ss'

-- An output annotated as its input passes.
#guard agree [assertEq "m" .int] [assertEq "m" .int]
-- An output annotating an input variable at another type fails.
#guard !agree [assertEq "m" .int] [assertEq "m" .bool]
-- An output reading a variable the input does not read fails.
#guard !agree [assertEq "m" .int] [assertEq "k" .int]
-- An input annotating one variable two ways fails.
#guard !agree [assertEq "m" .int, assertEq "m" .bool] [assertEq "m" .int]
-- A local declaration types the uses after it.
#guard agree [] [declare "t" .int, assertEq "t" .int]
#guard !agree [] [declare "t" .int, assertEq "t" .bool]

end Core.Simplify.FallbackTest

end
