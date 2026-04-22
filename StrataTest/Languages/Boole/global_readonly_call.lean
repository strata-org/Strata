/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.MetaVerifier

/-!
Test that read-only globals are correctly threaded through procedure headers
and call sites.
-/

namespace Strata

/-! ## Header shape: read-only globals appear as inputs -/

private def headerHelper (p : Strata.Program) : Except String (List String) := do
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

private def readOnlyGlobalPgm :=
#strata
program Boole;

// Declared in reverse-alphabetical order to exercise deterministic sorting.
var z : int;
var g : int;
var a : int;

procedure inc(x : int) returns ()
spec
{
  modifies g;
  ensures g == old(g) + x + a + z;
}
{
  g := g + x + a + z;
};

#end

-- Read-only globals `a` and `z` appear sorted despite `z` being declared first.
/-- info: Except.ok ["inc(in: [g, a, z, x], out: [g])"] -/
#guard_msgs in #eval headerHelper readOnlyGlobalPgm

/-! ## Call-site encoding and verification -/

private def fmtCallArg : Core.CallArg Core.Expression → String
  | .inArg e => s!"in({Std.format e})"
  | .inoutArg id => s!"inout({id.name})"
  | .outArg id => s!"out({id.name})"

private def callHelper (p : Strata.Program) : Except String (List String) := do
  let prog ← (Boole.getProgram p).mapError toString
  let cp ← (Boole.toCoreProgram prog p.globalContext).mapError
    fun e => toString (e.format none)
  return cp.decls.filterMap fun d =>
    match d with
    | .proc p _ =>
      p.body.findSome? fun
        | .block _ stmts _ => stmts.findSome? fun
          | .cmd (.call pname args _) =>
            some s!"call {pname}({", ".intercalate (args.map fmtCallArg)})"
          | _ => none
        | .cmd (.call pname args _) =>
          some s!"call {pname}({", ".intercalate (args.map fmtCallArg)})"
        | _ => none
    | _ => none

private def callerPgm :=
#strata
program Boole;

// `z` declared before `g` to exercise sorting.
var z : int;
var g : int;

procedure inc(x : int) returns ()
spec
{
  modifies g, z;
  requires z > 0;
  ensures g == old(g) + x + z;
}
{
  g := g + x + z;
};

procedure main_caller() returns ()
spec
{
  modifies g, z;
  requires z == 10;
  requires g == 0;
  ensures g == 15;
}
{
  call inc(5);
};

#end

-- Global var `z` sorts after `g` in the call-site prefix.
/-- info: Except.ok ["call inc(inout(g), inout(z), in(5))"] -/
#guard_msgs in #eval callHelper callerPgm

/--
info:

[DEBUG] Boole program:
 var z : int;
 var g : int;
 procedure inc (x : int) returns ()
spec {
  modifies g, z;
  requires z > 0;
  ensures g == old g + x + z;
  } {
  g := g + x + z;
};
 procedure main_caller () returns ()
spec {
  modifies g, z;
  requires z == 10;
  requires g == 0;
  ensures g == 15;
  } {
  call inc(5);
};

[Strata.Core] Type checking succeeded.


VCs:
Label: inc_ensures_1_2418
Property: assert
Assumptions:
inc_requires_0_2400: z > 0
Obligation:
g + x + z == g + x + z + x + z

Label: callElimAssert_inc_requires_0_2400_6
Property: assert
Assumptions:
main_caller_requires_2_2534: z@2 == 10
main_caller_requires_3_2554: g@2 == 0
Obligation:
z@2 > 0

Label: main_caller_ensures_4_2573
Property: assert
Assumptions:
main_caller_requires_2_2534: z@2 == 10
main_caller_requires_3_2554: g@2 == 0
callElimAssume_inc_ensures_1_2418_7: g@4 == g@2 + 5 + z@4
Obligation:
g@4 == 15

---
info:
Obligation: inc_ensures_1_2418
Property: assert
Result: ❌ fail
Model:
(g, 0) (x, 0) (z, 1) 

Obligation: callElimAssert_inc_requires_0_2400_6
Property: assert
Result: ✅ pass

Obligation: main_caller_ensures_4_2573
Property: assert
Result: ❓ unknown
Model:
(g@4, 5) (z@2, 10) (g@2, 0) (z@4, 0)
-/
#guard_msgs in
#eval Strata.Boole.verify "cvc5" callerPgm

end Strata
