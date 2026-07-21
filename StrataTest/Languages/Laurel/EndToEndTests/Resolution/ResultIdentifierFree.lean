/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Resolution tests that `result` is free as a user identifier.

The short `: T` return form auto-generates a procedure's single output
parameter. That output used to be named literally `result` and lived in the
procedure's identifier scope, so any user parameter or local named `result`
collided with it ("Duplicate definition 'result'"). The auto-output is now the
reserved `$result`, which cannot be written as a surface identifier, so `result`
is free for user code. (To refer to the return value explicitly, use the
named-return form `returns (r: T)`.)

These are pure resolution tests (translate + resolve, no SMT): they take the
exact program shapes that used to raise "Duplicate definition 'result'" — the
short `: T` return form combined with a user identifier named `result` — and
assert they now resolve with no diagnostics.

NOTE: These cases pin `result` specifically because that is the name the short
`: T` form used to reserve; `result` is not otherwise special. Any identifier
should be admissible in these positions, so per-name cases like these will not
scale. We do not yet have property-based tests; when we add them this should
become a property over arbitrary identifiers rather than separate per-name
cases. Until then, covering `result` guards against regressing the specific
collision this change fixed.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## `result` as a parameter of a short-form (`: T`) return procedure

The exact shape that previously produced "Duplicate definition 'result'": the
`: int` return auto-generates the single output while the parameter is also
named `result`. It now resolves cleanly. The `#guard_msgs in` pins that
resolution emits *no* diagnostics (not merely that it did not crash). -/

#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure echo(result: int): int
{
  return result
};
#end

/-! ## `result` in an `ensures` clause of a short-form (`: T`) return procedure

Postconditions previously implicitly referenced the return value via `result`.
With the `\result` grammar atom removed, `ensures result > 0` resolves the
user-scoped parameter `result` (not the internal `$result` auto-output) — the
position most likely to regress. It must resolve cleanly, with no diagnostics. -/

#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure ensuresResult(result: int): int
  opaque
  ensures result > 0
{
  return result
};
#end

/-! ## `result` as a local variable of a short-form (`: T`) return procedure

Covers `result` in a second position — a local rather than a parameter — to show
the identifier is free wherever a user name may appear, not just as a parameter.
This local also used to collide with the auto-generated `result` output. -/

#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure pick(): int
{
  var result: int := 3;
  return result
};
#end

/-! ## Negative control: a genuine `result` collision is still reported

Guards against the positive cases passing *vacuously*: if `result` resolution
were broken (or the test blind), this would matter. Two parameters both named
`result` must still fail with "Duplicate definition 'result'". This proves the
resolution test has teeth for exactly this name — so the clean resolutions above
genuinely demonstrate that the short-form auto-output no longer collides with a
user `result`, rather than that collisions go unnoticed.

The inline `// ^^^` annotation pins the *exact* diagnostic (message + location):
`testLaurelResolution` throws if it does not fire, so a regression that stopped
reporting the collision would break the build. The `#guard_msgs in` on top pins
that the annotated run is otherwise silent (the annotation matched), so this
control cannot pass vacuously. -/

#guard_msgs in
#eval testLaurelResolution
#strata
program Laurel;
procedure clash(result: int, result: bool): int
//                           ^^^^^^ error: Duplicate definition 'result' is already defined in this scope
{
  return 0
};
#end

