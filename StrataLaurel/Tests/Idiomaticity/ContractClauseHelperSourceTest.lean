/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
/-
Tests that each `$pre`/`$post` helper the contract pass (`lowerContracts`) generates carries its
own clause's source on its name, so a diagnostic Core reports at the helper's declaration lands on
the clause the user wrote.

The helper's body assigns its clause to `$result`, and that assignment has the clause's source, so
the test compares the two. For each helper it prints whether the name's source is the clause's,
and whether it differs from the procedure's own. Two clauses of each kind check that each helper
carries its own clause's source, not just the first clause's.
-/

meta import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.ContractPass

open Strata
open StrataTest.Util

namespace Strata.Laurel

/-- The source of the `$result := <clause>` assignment in a helper's body. -/
private meta def clauseSource? (proc : Procedure) : Option FileRange :=
  match proc.body with
  | .Transparent ⟨.Block stmts _ _ _, _⟩ =>
    stmts.findSome? fun s => match s.val with
      | .Assign _ _ => some s.source
      | _ => none
  | _ => none

/-- Print, for each generated helper, whether its name carries its clause's source and not the
    procedure's. -/
private meta def renderHelperSources (procName : String) (p : LaurelProgram) : IO Unit := do
  let some owner := p.staticProcedures.find? (·.name.text == procName)
    | IO.println s!"no procedure '{procName}'"
  for proc in p.staticProcedures do
    if proc.name.text.startsWith s!"{procName}$" then
      let atClause := clauseSource? proc == some proc.name.source
      let notAtProc := proc.name.source != owner.name.source
      IO.println s!"{proc.name.text}: at its clause {atClause}, not at the procedure {notAtProc}"

/-- Parse, resolve, run `contractPass`, print the helpers' name sources. `prelude := false`, as in
    `ContractPassConditionModeTest`: the clauses are bare `bool` parameters, so no operator wrapper
    is needed. -/
private meta def printHelperSources (procName : String) :=
  runPassForIdiomaticityCore contractPass (fun p _ => p) (renderHelperSources procName)
    (prelude := false) (options := {})

/--
info: callee$pre0: at its clause true, not at the procedure true
callee$pre1: at its clause true, not at the procedure true
callee$post0: at its clause true, not at the procedure true
callee$post1: at its clause true, not at the procedure true
-/
#guard_msgs in
#eval printHelperSources "callee" <|
#strata
program Laurel;
procedure callee(a: bool, b: bool) returns (r: bool)
  requires a
  requires b
  opaque
  ensures a
  ensures r
{
  r := true
};
#end

end Strata.Laurel
