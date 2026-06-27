/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that exercise the GRADUAL-TYPING path of resolution (`Laurel.resolve`
called with a `GradualConfig`). The rest of the Laurel resolution suite runs in
strict mode (no config), so these are the only tests that drive gradual
elaboration: coercion insertion across the `Any` boundary, and the fail-loud
diagnostic for an un-coerced dynamic-into-native boundary.

The dynamic type here is `Core Any` (i.e. `HighType.TCore "Any"`), which the
consistency relation treats as gradual (consistent with everything). A minimal
`GradualConfig` is constructed per-test; the only knobs that matter are whether
an unbox coercion exists for the native target.
-/

import StrataTest.Util.TestLaurel

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- Substring containment. -/
private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

/-- A minimal gradual config for tests. The dynamic type is `Core Any`.
    `unboxName` controls whether an `Any → native` unbox coercion exists:
    `some n` materializes a call to `n`; `none` leaves the boundary uncovered
    (so the fail-loud path fires).
    `boxName` controls whether a `native → Any` box coercion exists (the other
    coercion direction); `none` (the default) leaves boxing off.
    `elaborate` is wired into `shouldElaborate`: when `false`, gradual
    elaboration is gated off for every procedure, so no coercion is inserted and
    the boundary falls back to the permissive consistency check.
    Prelude operators are unused here. -/
private def testGradualConfig (unboxName : Option String)
    (boxName : Option String := none) (elaborate : Bool := true) : GradualConfig where
  dynamic := .TCore "Any"
  isDynamic := fun t => match t with | .TCore "Any" => true | _ => false
  box := fun _ => boxName
  unbox := fun _ => unboxName
  toBool := "Any_to_bool"
  opPrelude := fun _ => none
  shouldElaborate := fun _ => elaborate

/-- Resolve with a gradual config, printing each diagnostic message on its own
    line (or `no errors`), then whether the resolved program contains a call to
    the named coercion function (evidence that a coercion was inserted). -/
private def resolveGradual (unboxName : Option String) (coercionProbe : String)
    (program : StrataDDM.Program)
    (boxName : Option String := none) (elaborate : Bool := true) : IO Unit := do
  let laurelProgram ← translateLaurel program
  let result := resolve laurelProgram
    (gradual := some (testGradualConfig unboxName boxName elaborate))
  if result.errors.isEmpty then
    IO.println "no errors"
  else
    for e in result.errors do
      IO.println e.message
  let formatted := toString (Std.Format.pretty (Std.ToFormat.format result.program))
  IO.println s!"coercion '{coercionProbe}' inserted: {containsSubstr formatted coercionProbe}"

/-! ## Coercion insertion (gradual path is live)

With an unbox mapping available, an `Any`-typed value flowing into a native
`int` slot is rewritten to an explicit unbox call. This confirms the gradual
elaboration actually runs (strict resolution would never insert a call). -/

/--
info: no errors
coercion 'unbox_to_int' inserted: true
-/
#guard_msgs in
#eval! resolveGradual (some "unbox_to_int") "unbox_to_int"
#strata
program Laurel;
function unbox_to_int(x: Core Any): int;
procedure useAny(a: Core Any)
  returns (r: int)
{
  r := a;
  return
};
#end

/-! ## Fail-loud at an un-coerced dynamic → native boundary (L3/L8/P4)

With NO unbox mapping, the same `Any`-into-`int` position is no longer silently
accepted (the consistency relation would treat `Core Any` as consistent with
`int`). It now raises a resolution error demanding an explicit cast, and inserts
no coercion. -/

/--
info: no coercion from dynamic 'Core Any' into native 'int' at this boundary; an explicit cast is required
coercion 'unbox_to_int' inserted: false
-/
#guard_msgs in
#eval! resolveGradual none "unbox_to_int"
#strata
program Laurel;
procedure useAnyBad(a: Core Any)
  returns (r: int)
{
  r := a;
  return
};
#end

/-! ## Multi-valued operand under gradual config (L1 gradual-path coverage)

A multi-output call (`returns (a, b)`) used in operator-operand position is an
internal `MultiValuedExpr` pseudo-type with no Core lowering. The gradual
elaboration path must report the clean position-oriented diagnostic for it
rather than letting it slip through to a later pass that crashes as a
`StrataBug`. This exercises the gradual operator path specifically (the strict
counterpart lives in `ResolutionTypeCheckTests`), confirming the multi-valued
guard fires even when a `GradualConfig` is threaded through. -/

/--
info: multi-output call cannot be used as a value here; it returns multiple values. Unpack it into separate variables first
coercion 'unused' inserted: false
-/
#guard_msgs in
#eval! resolveGradual (some "unbox_to_int") "unused"
#strata
program Laurel;
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
};
#end

/-! ## A. Gradual gating / inertness (`shouldElaborate := false`)

Even with a perfectly good unbox mapping available (`unbox ↦ "unbox_to_int"`),
gating elaboration off (the config's `shouldElaborate` returns `false` for every
procedure) must leave the `Any → int` position untouched: no coercion is
inserted, and the boundary falls back to the permissive consistency check (which
treats `Core Any` as consistent with `int`, so no error). This pins that gradual
elaboration is genuinely gated by `shouldElaborate` — the same `r := a` position
that gets an `unbox_to_int` coercion in the first test above gets none here. The
prelude function is intentionally *not* declared, so the probe matches only an
actually-inserted coercion call (gating off ⇒ no call ⇒ `false`). -/

/--
info: no errors
coercion 'unbox_to_int' inserted: false
-/
#guard_msgs in
#eval! resolveGradual (some "unbox_to_int") "unbox_to_int" (elaborate := false)
#strata
program Laurel;
procedure useAny(a: Core Any)
  returns (r: int)
{
  r := a;
  return
};
#end

/-! ## B. Truthiness coercion (`toBool`) at a condition position

An `Any`-typed value used in a boolean-guard position (here a `while`
condition, checked against `bool`) is rewritten to the config's `toBool`
coercion (`Any_to_bool`). This holds independently of whether an unbox mapping
exists (`unboxName` is `none` here), since the `.TBool` arm of `tryCoerce` is
served by `toBool`, not `unbox`. -/

/--
info: no errors
coercion 'Any_to_bool' inserted: true
-/
#guard_msgs in
#eval! resolveGradual none "Any_to_bool"
#strata
program Laurel;
function Any_to_bool(x: Core Any): bool;
procedure loopAny(a: Core Any)
{
  while (a) { }
};
#end

/-! ## C. Box coercion (native → dynamic)

The other coercion direction: a native `int` flowing into a `Core Any` slot is
rewritten to an explicit box call (`box_int`) supplied via the config's `box`
mapping. Confirms the dynamic-expected / native-actual arm of `tryCoerce`. -/

/--
info: no errors
coercion 'box_int' inserted: true
-/
#guard_msgs in
#eval! resolveGradual none "box_int" (boxName := some "box_int")
#strata
program Laurel;
function box_int(x: int): Core Any;
procedure useInt(i: int)
  returns (r: Core Any)
{
  r := i;
  return
};
#end

/-! ## D. Native operator over native operands (no coercion)

A native operator (`+`) over native (`int`) operands resolves to the native
operator with no coercion inserted: the gradual path only rewrites operators
when some operand is already dynamic, so an all-native operation is left exactly
as strict resolution would leave it (no unbox call, no error). -/

/--
info: no errors
coercion 'unbox_to_int' inserted: false
-/
#guard_msgs in
#eval! resolveGradual (some "unbox_to_int") "unbox_to_int"
#strata
program Laurel;
procedure addInts(x: int, y: int)
  returns (r: int)
{
  r := x + y;
  return
};
#end

/-! ## D (cont.). Fail-loud restricted to native scalar targets

The dynamic → native fail-loud only fires for a *native scalar* target
(`int/bool/str/real/float64/bv`). A dynamic value flowing into a non-scalar
*nominal* target (here a `datatype`) is the gradual-top case: it falls through
to the permissive consistency check WITHOUT the fail-loud diagnostic, exactly as
before gradual elaboration existed. There is no unbox mapping (`unboxName` is
`none`) and no coercion is inserted; the absence of the
`no coercion from dynamic ... into native ...` error confirms the diagnostic is
correctly scoped to native sorts and does not over-fire on nominal slots. -/

/--
info: no errors
coercion 'unbox_to_color' inserted: false
-/
#guard_msgs in
#eval! resolveGradual none "unbox_to_color"
#strata
program Laurel;
datatype Color { Red, Green, Blue }
procedure useAnyNominal(a: Core Any)
  returns (r: Color)
{
  r := a;
  return
};
#end

end Strata.Laurel
