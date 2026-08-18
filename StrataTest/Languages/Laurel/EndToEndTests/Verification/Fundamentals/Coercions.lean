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
resolve + SMT, checking the coerced value carries real semantics into Core. §3 covers the `toBool`
truthiness hook, which is a boolean-CONTEXT coercion (not subtyping, so not part of `coerce`):
native Laurel leaves it `none`, so it is exercised here by installing a hook via
`translateOptions.toBool`, exactly as a language frontend (e.g. Python) does.

The gradual-top `inject`/`project` verdicts are decided at resolution level in
`Resolution/Types/Coercions.lean`; realizing the box/unbox is the frontend's job (Python's `Any`
prelude), out of scope for native Laurel.
-/

import StrataTest.Util.TestLaurel

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
//^^^^^^^^^^^^^^^^^^ error: assertion could not be proved
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
