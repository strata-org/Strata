/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
Test accepted and rejected procedure signature forms in Boole.

Boole supports two procedure syntaxes:
- `procedure f(...) returns (...) spec { ... } { ... };`  (boole_procedure)
- `procedure f(...)             spec { ... } { ... };`  (command_procedure, no returns)

The `out`/`inout` parameter modifiers are Core-only syntax and must be rejected
when they appear in Boole programs (which parse as `command_procedure`).
-/

open Strata

private def helper (p : Strata.Program) : Except String (List String) := do
  let prog ← (Boole.getProgram p).mapError toString
  let cp ← (Boole.toCoreProgram prog p.globalContext).mapError
    fun e => toString (e.format none)
  return cp.decls.filterMap fun d =>
    match d with
    | .proc p _ =>
      let ins := p.header.inputs.toList.map fun (id, _) => id.name
      let outs := p.header.outputs.toList.map fun (id, _) => id.name
      some s!"{p.header.name.name}(in: {ins}, out: {outs})"
    | _ => none

/-! ## Accepted: `procedure f(...) returns (...)` -/

private def withReturns :=
#strata
program Boole;
var g : int;
procedure foo(x : int) returns (y : int)
spec { modifies g; ensures y == x + g; }
{ y := x + g; };
#end

/-- info: Except.ok ["foo(in: [g, x], out: [g, y])"] -/
#guard_msgs in #eval helper withReturns

/-! ## Accepted: `procedure f(...) returns ()` — no output params -/

private def withEmptyReturns :=
#strata
program Boole;
var g : int;
procedure bar(x : int) returns ()
spec { modifies g; ensures g == x; }
{ g := x; };
#end

/-- info: Except.ok ["bar(in: [g, x], out: [g])"] -/
#guard_msgs in #eval helper withEmptyReturns

/-! ## Accepted: `procedure f(...)` — no `returns` clause -/

private def withoutReturns :=
#strata
program Boole;
var g : int;
procedure baz(x : int)
spec { modifies g; ensures g == x; }
{ g := x; };
#end

/-- info: Except.ok ["baz(in: [g, x], out: [g])"] -/
#guard_msgs in #eval helper withoutReturns

/-! ## Rejected: `out` modifier in Boole procedure (Core-only syntax) -/

private def withOut :=
#strata
program Boole;
procedure bad(x : int, out y : int)
spec { ensures y == x; }
{ y := x; };
#end

private def containsSubstr (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length > 1

#guard match helper withOut with
  | .error e => containsSubstr e "'out' modifier on parameter 'y' is not supported"
  | .ok _ => false

/-! ## Rejected: `inout` modifier in Boole procedure (Core-only syntax) -/

private def withInout :=
#strata
program Boole;
procedure bad2(inout x : int)
spec { ensures x == old x + 1; }
{ x := x + 1; };
#end

#guard match helper withInout with
  | .error e => containsSubstr e "'inout' modifier on parameter 'x' is not supported"
  | .ok _ => false

/-! ## Call statements -/

/-! ### Accepted: `call f(args)` — unit call (no outputs) -/

private def unitCall :=
#strata
program Boole;
procedure foo(x : int) returns ()
{ assume true; };
procedure bar() returns ()
{ call foo(1); };
#end

/-- info: Except.ok ["foo(in: [x], out: [])", "bar(in: [], out: [])"] -/
#guard_msgs in #eval helper unitCall

/-! ### Accepted: `call lhs := f(args)` — Boole call with outputs -/

private def lhsCall :=
#strata
program Boole;
procedure foo(x : int) returns (y : int)
spec { ensures y == x; }
{ y := x; };
procedure bar() returns ()
{ var z : int;
  call z := foo(1); };
#end

/-- info: Except.ok ["foo(in: [x], out: [y])", "bar(in: [], out: [])"] -/
#guard_msgs in #eval helper lhsCall

/-! ### Rejected: `call f(out x)` — Core-only syntax -/

private def callWithOut :=
#strata
program Boole;
procedure foo(x : int) returns (y : int)
spec { ensures y == x; }
{ y := x; };
procedure bar() returns ()
{ var z : int;
  call foo(1, out z); };
#end

#guard match helper callWithOut with
  | .error e => containsSubstr e "'out' argument 'z' in call to 'foo' is not supported in Boole"
  | .ok _ => false

/-! ### Rejected: `call f(inout x)` — Core-only syntax -/

private def callWithInout :=
#strata
program Boole;
var g : int;
procedure foo(inout x : int) returns ()
{ x := x + 1; };
procedure bar() returns ()
{ call foo(inout g); };
#end

#guard match helper callWithInout with
  | .error e => containsSubstr e "is not supported in Boole"
  | .ok _ => false
