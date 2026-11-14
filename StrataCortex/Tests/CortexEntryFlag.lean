/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
meta import StrataLaurel.Tests.Util.TestLaurel
meta import StrataCortex.Implementation.Cli

/-!
# The `--entry` flag of `cortexInterpretBinary`

`runEntry` does what the command does with `--entry <name>`: it selects the
entry with `Cortex.Cli.selectLaurelEntry` and runs the program on the Cortex
interpreter. The command reads a Laurel program as Ion, so the tests call the
functions that it calls.
-/

open StrataTest.Util
open Strata

namespace Cortex.CliTest

private meta def runEntry (name : String) (block : StrataDDM.SourcedProgram) : IO Unit := do
  match Cortex.Cli.selectLaurelEntry (← translateLaurel block.program) name with
  | .error msg => IO.println s!"rejected: {msg}"
  | .ok (program, target) =>
    match Cortex.interpretEntries program with
    | .error msg => IO.println s!"error: {msg}"
    | .ok outcome =>
      IO.println s!"{target}: diagnostics {outcome.diagnostics.map (·.message)}, errors {outcome.errors}"

-- A target with a body runs, and its failed assertion is reported.
/-- info: failing: diagnostics #[assertion does not hold], errors #[] -/
#guard_msgs in
#eval runEntry "failing" <|
#strata
program Laurel;
procedure lib() opaque;
procedure failing()
  opaque
{
    var a: int := 1;
    lib();
    assert a == 2
};
#end

-- A target without a body is rejected: the entry's call to it would return at
-- once, and the run would report nothing.
/-- info: rejected: entry procedure 'lib' has no body -/
#guard_msgs in
#eval runEntry "lib" <|
#strata
program Laurel;
procedure lib() opaque;
procedure failing()
  opaque
{
    assert 1 == 2
};
#end

/-- info: rejected: entry procedure 'absent' not found -/
#guard_msgs in
#eval runEntry "absent" <|
#strata
program Laurel;
procedure lib() opaque;
#end

-- A target with inputs is rejected for its inputs, with or without a body.
/--
info: rejected: entry procedure 'withInput' cannot take inputs or type parameters: an entry point is invoked with no arguments
-/
#guard_msgs in
#eval runEntry "withInput" <|
#strata
program Laurel;
procedure withInput(x: int) opaque;
#end

end Cortex.CliTest
