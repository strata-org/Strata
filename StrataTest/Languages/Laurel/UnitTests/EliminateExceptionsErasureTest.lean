/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
The erasure invariant of `EliminateExceptions`: after the pass, no exceptional
construct remains.

Three downstream passes depend on it — `LaurelToCoreSchemaPass` reports a
`strata-bug` for a `Throw`/`Try` it encounters, and `HeapParameterization` and
`LiftImperativeExpressions` describe those nodes as unreachable — but the assumption
was unchecked, so an arm of `lowerStmt` that forgot to recurse would only surface far
downstream, as an internal error naming the wrong pass.

`exceptionalNodeCount` is a total measurement of what must be gone: `throw` and `try`
nodes plus the declared `throws` type, the name it bound for the thrown value, and each
`throwsOn` case's postconditions. It is now also a runtime backstop inside the pass.
This test pins it over one program that exercises every construct the pass lowers, and
checks the count is non-zero *before* the pass, so it cannot pass by measuring nothing.

(A case's guard and frame targets are excluded by design: the pass leaves them for
`ModifiesClauses`, which lowers them after heap parameterization.)
-/

meta import Strata.Languages.Laurel
meta import Strata.Languages.Laurel.EliminateExceptions

meta section

open Strata
open Strata.Laurel

/-- Every construct the pass has to erase: a `throws` signature with a bound thrown
    value and a `throwsOn` case, a direct `throw`, a throwing call, `try`/`catch` with a
    guard, a `finally`, a nested `try`, a `return` unwinding through a `finally`, and an
    `exit` leaving a `try`. -/
private def source : String := "
composite Exception {}
composite NotFound extends Exception {}
composite Invalid extends Exception {}

procedure fetch(id: int) returns (r: int)
  throws (e: NotFound)
  opaque
  throwsOn id <= 0 {
    ensures e is NotFound
  }
{
  if id <= 0 then {
    var nf: NotFound := new NotFound;
    throw nf
  };
  r := id
};

procedure handles(id: int) returns (out: int)
  throws (e: Exception)
  opaque
{
  out := 0;
  try {
    out := fetch(id);
    try {
      var iv: Invalid := new Invalid;
      throw iv
    } finally {
      out := out + 1
    }
  } catch e when e is NotFound {
    out := -1;
    return
  } catch e {
    var iv2: Invalid := new Invalid;
    throw iv2
  } finally {
    out := out + 2
  }
};

procedure exits(id: int) returns (out: int)
  opaque
{
  out := 0;
  {
    try {
      if id > 0 then { exit done }
    } finally {
      out := 1
    }
  } done;
  out := out + 1
};
"

private def totalCount (procs : List Procedure) : Nat :=
  (procs.map exceptionalNodeCount).foldl (· + ·) 0

/-- info: before: 11, after: 0, diagnostics: 0 -/
#guard_msgs in
#eval do
  let parsed ← (Strata.parseLaurelText "<erasure-test>" source : IO Program)
  let resolved := resolve parsed
  let before := totalCount resolved.program.staticProcedures
  let (lowered, diags) := eliminateExceptionsTransform resolved.model resolved.program
  let after := totalCount lowered.staticProcedures
  IO.println s!"before: {before}, after: {after}, diagnostics: {diags.length}"

end
