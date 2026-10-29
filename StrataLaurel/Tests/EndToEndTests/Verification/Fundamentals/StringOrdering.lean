/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end verification tests for the `string` overloads of `<`, `<=`, `>`, `>=`.

Core has exactly TWO ordering operators on `string` — `Str.Lt` and `Str.Le`
(`Core/Factory.lean`), lowered to the SMT string theory's `str.<` / `str.<=`
(`Core/SMTEncoder.lean`). The prelude (`CoreDefinitionsForLaurel.lean`) exposes
them as `$strLt`/`$strLe` delegates plus four overloads of the comparison
operators; `$gt`/`$ge` are defined by SWAPPING the operands, since Core has no
`Str.Gt`/`Str.Ge`.

**Literals are NOT constant-folded on this path**, which is worth stating because
the opposite is true one layer down. `Str.Lt`/`Str.Le` carry a concrete evaluator,
so a DIRECT Core application to two literals folds (`StrataTest/Languages/Core/
Examples/String.lean`'s `lt_concrete_true` prints `Obligation: true`). A Laurel
comparison does not reach the operator directly: it goes through the overload
wrapper, which is lifted to an internal function, so the obligation for
`assert "a" < "b"` is `$ov…$$lt("a", "b")` and the literals are discharged by the
SMT string theory. Therefore §1 is backend coverage; the evaluator's coverage
lives in `Execution/.../PrimitiveTypes/String.lean`.

What this encoding could be and is not is an **uninterpreted function**. A
congruence-only encoding would discharge reflexive-shaped facts and nothing else:
it could not PROVE transitivity (§3.3) and could not DISPROVE `(a < b) | (b < a)`
(§4.2) — a UF admits a model where both disjuncts are false and `a != b`. Both
happen, over SYMBOLIC operands, so the operator reaching the solver is the real
string order. That is why §2–§4 use symbolic operands throughout.

**Solver split, measured.** The three order laws in §3 TIME OUT under the default
solver (cvc5 1.3.4): antisymmetry at 60 s, totality and transitivity at 30 s. The
same three are discharged by z3 4.12.6 in well under a second, so those blocks
name `solver := "z3"` explicitly. Everything else in this file — including every
DISPROOF in §4 — holds under the default solver, so the split is narrow and the
negative controls do not depend on it.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-- Options for the three §3 laws the default solver cannot discharge. -/
private def z3Options : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    verifyOptions := { defaultLaurelTestOptions.verifyOptions with solver := "z3" } }

/-! ## 1. Literal operands, both directions.

These reach the solver as `$ov…$$lt("a", "b")` (see the header), so they pin the
SMT string theory's verdict on concrete code-point pairs — including a strict
prefix and ASCII case order, which is where a byte order or a case-folding order
would disagree. 1b is the control: the false direction is reported, so the row
above is not a constant `true`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p() opaque {
  assert "a" < "b";
  assert "ab" < "abc";
  assert "A" < "a";
  assert "a" <= "a";
  assert "b" > "a";
  assert "a" >= "a"
};
#end

/-! ### 1b. The false direction is reported. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p() opaque {
  assert "b" < "a"
//^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## 2. Symbolic operands, under the DEFAULT solver.

Each of these is a property of the string order that a fresh uninterpreted
function would not have. §2.5 in particular relates `<` to `^`: it needs
`Str.Concat` and `Str.Lt` to be the *same* theory's operators. -/

/-! ### 2.1 Irreflexivity of `<`, reflexivity of `<=`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string) opaque {
  assert !(a < a);
  assert a <= a;
  assert !(a > a);
  assert a >= a
};
#end

/-! ### 2.2 `<` refines `<=`, and `<=` decomposes into `<` or `==`.

The second assert is the one that cannot hold for a UF: it forces `str.<` and
polymorphic equality to agree on the same sort. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a < b) ==> (a <= b);
  assert (a <= b) == ((a < b) | (a == b))
};
#end

/-! ### 2.3 The operand swap that defines `>` and `>=` is exact.

`$gt`/`$ge` at `string` are `$strLt(y, x)` / `$strLe(y, x)` because Core has no
`Str.Gt`/`Str.Ge`. These two asserts are that definition observed from the
outside, so a future change to the swap cannot pass silently. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a > b) == (b < a);
  assert (a >= b) == (b <= a)
};
#end

/-! ### 2.4 Ordering survives a procedure boundary, in a contract.

`requires`/`ensures` over `<` reach the solver as assumptions and obligations, not
just as asserts in a body. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure smaller(a: string, b: string) returns (r: string)
  requires a < b
  opaque
  ensures r <= b
{
  return a
};
procedure p(x: string, y: string)
  requires x < y
  opaque
{
  var z: string := smaller(x, y);
  assert z <= y
};
#end

/-! ### 2.5 `<` and `^` are the same theory: a string is strictly below any
extension of itself by a non-empty suffix. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string) opaque {
  assert a < (a ^ "x")
};
#end

/-! ## 3. The three order laws, under z3.

Measured: cvc5 1.3.4 times out on all three (see the header). They are kept
because they are the laws that distinguish a real order from a UF.

### 3.1 Antisymmetry. -/

#eval testLaurelVerification (options := z3Options) <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a < b) ==> !(b < a)
};
#end

/-! ### 3.2 Totality. -/

#eval testLaurelVerification (options := z3Options) <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a < b) | (b < a) | (a == b)
};
#end

/-! ### 3.3 Transitivity, over three symbolic operands. -/

#eval testLaurelVerification (options := z3Options) <|
#strata
program Laurel;
procedure p(a: string, b: string, c: string) opaque {
  assert ((a < b) & (b < c)) ==> (a < c)
};
#end

/-! ## 4. Disproofs — each is a REAL countermodel, not an `unknown`.

`does not hold` is emitted only when the obligation is reachable AND false
(`Core/Verifier.lean`); an `unknown` renders as `could not be proved`. So every
annotation below is evidence the solver built a counterexample over symbolic
strings. All four hold under the DEFAULT solver.

### 4.1 `<` is not symmetric. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a < b) ==> (b < a)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 4.2 `<` is not total on its own — equality is a third case.

This is the control for §3.2: dropping the `a == b` disjunct must break it. A
congruence-only encoding could not report this. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a < b) | (b < a)
//^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 4.3 Extending by the EMPTY suffix is not a strict increase.

Control for §2.5: it is `"x"` being non-empty that makes that block true, not
anything about `^` in general. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string) opaque {
  assert a < (a ^ "")
//^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 4.4 `>=` is not `>`.

Control for §2.3's second assert: the swap is on `Str.Le`, not `Str.Lt`, so
`a >= b` must admit `a == b`. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(a: string, b: string) opaque {
  assert (a >= b) == (b < a)
//^^^^^^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ### 4.5 A precondition that does not hold over all inputs is reported.

§2.4 passes its own `requires` on; this block drops it, so `smaller`'s
precondition becomes a genuine obligation and fails. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure smaller(a: string, b: string) returns (r: string)
  requires a < b
  opaque
  ensures r <= b
{
  return a
};
procedure p(x: string, y: string) opaque {
  var z: string := smaller(x, y);
//^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: precondition does not hold
  assert z <= y
};
#end

/-! ## 5. The rest of the overload set is unchanged.

`string` is disjoint from `int`, `real` and every `bv n`, so the four new arms
cannot capture an existing call. §5.2 is the one shape that IS ambiguous: a type
variable selects no overload, so the diagnostic is a property of the overload
set, not of its size.

### 5.1 `int`, `real` and `bv 32` comparisons still resolve. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure p(x: int, y: int, u: real, v: real) opaque {
  assert (x > y) == (y < x);
  assert (u >= v) == (v <= u);
  assert (x <= x) & (u <= u)
};
#end

/-! ### 5.2 A comparison at a TYPE VARIABLE is still ambiguous. -/

#eval testLaurelVerification <|
#strata
program Laurel;
procedure f<T>(a: T, b: T) : bool { return a > b };
//                                         ^^^^^ error: ambiguous call to '$gt'
procedure p() opaque {
  assert true
};
#end
