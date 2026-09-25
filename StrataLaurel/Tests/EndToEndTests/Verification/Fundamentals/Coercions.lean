/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
End-to-end verification tests for the proof-relevant coercion judgment (`coerce`), its realization
into Core, and the frontend `toBool` truthiness hook.

`coerceTo` realizes a `coerce` verdict onto the term via the frontend's `realizeCoercion`. Two
verdicts are realized without any frontend hook:

  * `refl`   — identical types, no-op.
  * `upcast` — nominal subtype ≤ supertype. Representation-preserving, so the realizer is identity;
               native Laurel emits no term and the value flows through unchanged.

§1–§2 drive `upcast` — the one non-`refl` verdict native Laurel realizes — through translate +
resolve + SMT, checking the coerced value carries real semantics into Core. §4 puts that same
widening at one position of a multi-target assignment, §5 reaches the same slot through a
dispatcher, and §6 pins that a position needing a runtime term is rejected rather than silently
losing it. §3 covers the `toBool` truthiness hook, which is a boolean-CONTEXT coercion (not
subtyping, so not part of `coerce`): native Laurel leaves it `none`, so it is exercised here by
installing a hook via `translateOptions.toBool`, exactly as a language frontend (e.g. Python) does.

The gradual-top `inject`/`project` verdicts are decided at resolution level in
`Resolution/Types/Coercions.lean`; realizing the box/unbox is the frontend's job (Python's `Any`
prelude), out of scope for native Laurel.
-/

import StrataLaurel.Tests.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## 1. `upcast` realized end-to-end: the coerced field value reaches the postcondition.

`var a: Animal := d` where `d : Dog` and `Dog extends Animal` drives `coerce Dog Animal ⇒ upcast`.
`upcast` is representation-preserving, so `coerceTo` realizes it as identity — no frontend hook.
The upcast reference then reads the field written on the `Dog`, and the postcondition is discharged
by the solver: the coercion carries real semantics into Core, it is not an opaque cast. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure p() returns (r: int)
  opaque
  ensures r == 4
{
  var d: Dog := new Dog;
  d#legs := 4;
  var a: Animal := d;
  return a#legs
};
#end

/-! ## 2. Verification through the coerced slot is sound: a false property IS caught.

Same `upcast`, but the asserted value is wrong. If the coercion were an information-losing black
box the assertion could spuriously pass; instead the verifier reports it, confirming the field
value survives the upcast into Core with its real value. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure p() returns (r: int)
  opaque
{
  var d: Dog := new Dog;
  d#legs := 4;
  var a: Animal := d;
  assert a#legs == 5
//^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
#end

/-! ## 3. The `toBool` truthiness hook, realized end-to-end.

Truthiness is a boolean-context coercion, not subtyping (`int` is not `<: bool`), so it is NOT a
`coerce` verdict: it fires through the separate `toBool` hook at bool-context slots
(`if`/`assert`/`assume`/bool-ops). Native Laurel leaves `toBool = none`, so without a hook an `int`
in a bool slot is a strict type error — this is the ONLY path that exercises the option, by
installing a hook exactly as a frontend does.

The hook below models Python-style integer truthiness (`n` is truthy iff `n != 0`): it maps an
`int` operand `e` to `e != 0`. It is installed via `translateOptions.toBool` on `testLaurelVerification`'s
options, threaded onto the `TypeLattice` and fired at the bool-context slot inside `resolveStmtExpr`
(the subsumption fallback). Because the realized `!= 0` term carries the operand's real value into
the verification condition, the two blocks below prove the hook is not an opaque bool coercion:

  * §3a — `assert 1` (a truthy int) verifies: the hook rewrites it to `1 != 0`, which the solver
           proves. Without the hook this is `expected 'bool', got 'int'`.
  * §3b — `assert 0` (a falsy int) FAILS: the hook rewrites it to `0 != 0`, which is false, so the
           assertion is correctly reported — the operand value survives into the VC. -/

/-- A self-contained `toBool` hook modelling integer truthiness: `int` operand `e` ↦ `e != 0`;
    any other type passes through unchanged. Mirrors how the Python frontend installs
    `pythonToBool`, but with no runtime dependency — `!= 0` is a primitive comparison, so the
    realized term is translation-ready without a coercion prelude. -/
private def intTruthinessToBool : Laurel.HighType → Laurel.StmtExprMd → Laurel.StmtExprMd :=
  fun ty e =>
    match ty with
    | .TInt =>
      let zero : Laurel.StmtExprMd := { val := .LiteralInt 0, source := e.source }
      { val := .StaticCall (Laurel.mkId Laurel.Operation.Neq.procName) [e, zero], source := e.source }
    | _ => e

private def toBoolOptions : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    translateOptions := { defaultLaurelTestOptions.translateOptions with
      toBool := some intTruthinessToBool } }

/-! ### 3a. A truthy int in a bool slot verifies once the hook rewrites it to `!= 0`. -/

#eval testLaurelVerification (options := toBoolOptions) <|
#strata
program Laurel;
procedure p()
  opaque
{
  assert 1
};
#end

/-! ### 3b. A falsy int is correctly reported: the hook's `0 != 0` is false, so the assert fails. -/

#eval testLaurelVerification (options := toBoolOptions) <|
#strata
program Laurel;
procedure p()
  opaque
{
  assert 0
//^^^^^^^^ error: assertion does not hold
};
#end

/-! ## 4. §1's widening, at one position of a multi-target assignment.

On its own the `(Dog, int)` → `(Animal, int)` pair coerces as §1's `upcast`; inside a tuple the
verdict is the whole tuple's `refl` and the position's `upcast` is DISCARDED (no tuple `Coercion`
constructor exists to carry it). So this is the end-to-end check that discarding it loses nothing —
which only the Core lowering can show. Hence it reads `legs` back off `q`, and 4b asserts the wrong
value to show the slot is not an opaque box. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure f() returns (r: Dog, i: int) opaque ensures r#legs == 4 ensures i == 1 {
  r := new Dog; r#legs := 4; i := 1
};
procedure p() opaque {
  var q: Animal; var j: int;
  assign q, j := f();
  assert q#legs == 4;
  assert j == 1
};
#end

/-! ### 4b. Must-fail twin of §4. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal { var legs: int }
composite Dog extends Animal { }
procedure f() returns (r: Dog, i: int) opaque ensures r#legs == 4 ensures i == 1 {
  r := new Dog; r#legs := 4; i := 1
};
procedure p() opaque {
  var q: Animal; var j: int;
  assign q, j := f();
  assert q#legs == 5
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## 5. §4's widening, reached through a DISPATCHER.

`Sub3.m`'s `(Dog3, int)` overrides `Base3.m`'s `(Animal3, int)`, and the dispatcher's branch assigns
the override's call into the base's output list — so the widened position is coerced on a slot the
program never names, rather than at a user-written assignment. `outputSignatureCompatible` admits
covariance at every position, so the family is lowered with no shape of its own; what this pins is
that the lowered form then VERIFIES. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal3 { var a: int }
composite Dog3 extends Animal3 { var d: int }
composite Base3 { procedure m(self: Base3) returns (r: Animal3, i: int) opaque ensures i >= 0 { r := new Animal3; i := 0 }; }
composite Sub3 extends Base3 { procedure m(self: Sub3) returns (r: Dog3, i: int) opaque ensures i == 1 ensures r is Dog3 { r := new Dog3; i := 1 }; }
procedure p() opaque {
  var b: Base3 := new Sub3;
  assign var q: Animal3, var j: int := b#m();
  assert j == 1;
  assert q is Dog3
};
#end

/-! ### 5b. Must-fail twin of §5.

`assert j == 1` verifying only rules out a fallthrough to `Base3$m$impl`, whose `i >= 0` cannot
prove it. Contradictory dispatcher posts would prove `j == 0` just as happily, so asserting the
value `Base3`'s own body produces — which its contract only bounds — has to fail. -/

#eval testLaurelVerification <|
#strata
program Laurel;
composite Animal3 { var a: int }
composite Dog3 extends Animal3 { var d: int }
composite Base3 { procedure m(self: Base3) returns (r: Animal3, i: int) opaque ensures i >= 0 { r := new Animal3; i := 0 }; }
composite Sub3 extends Base3 { procedure m(self: Sub3) returns (r: Dog3, i: int) opaque ensures i == 1 ensures r is Dog3 { r := new Dog3; i := 1 }; }
procedure p() opaque {
  var b: Base3 := new Sub3;
  assign var q: Animal3, var j: int := b#m();
  assert j == 0
//^^^^^^^^^^^^^ error: assertion could not be proved
};
#end

/-! ## 6. NO UNREALIZED WIDEN at a tuple position.

With a realizer installed — which is what a frontend supplies, the way §3 installs `toBool` —
`coerce int real` is `widen`, a conversion someone has to emit. The per-position test is
`isConsistent ∨ isSubtype`, which does not relate `int` to `real` at all, so the tuple is REJECTED
and the diagnostic names the position.

Written instead as `(coerce …).isSome` per position, the arm admits this tuple and emits the tuple's
own `refl`, dropping the `int_to_real`: the untouched `int` reaches a `real` slot in Core and
translation fails with `Type checking error … Impossible to unify int with real`, well past the
point that could have diagnosed it. That is what this block rejects.

The annotation is a RESOLUTION diagnostic, so this would sit in `Resolution/Types/Coercions.lean`;
it is here only because `realizeCoercion` arrives through `translateOptions`, which the verification
harness takes and `testLaurelResolution` does not.

No converse control pairs with it: native Laurel has no int-to-real conversion for a realizer to
insert, so a BARE `int` into `real` under the identity realizer below also fails rather than being
admitted. Read this as pinning the rejection, not as bracketing it. -/

/-- A realizer, installed the way §3 installs its `toBool` hook. Identity is enough here: the point
    is that a `widen` verdict becomes REACHABLE, not what it realizes to. -/
private def realizerOptions : Laurel.LaurelVerifyOptions :=
  { defaultLaurelTestOptions with
    translateOptions := { defaultLaurelTestOptions.translateOptions with
      realizeCoercion := some (fun _ e => e) } }

#eval testLaurelVerification (options := realizerOptions) <|
#strata
program Laurel;
procedure f() returns (r: int, i: int) opaque { r := 0; i := 0 };
procedure p() opaque {
  var q: real; var j: int;
  assign q, j := f()
//               ^^^ error: expected '(real, int)', got '(int, int)'
};
#end
