/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core
public meta import StrataDDM
public meta import StrataDDM.BuiltinDialects

meta section

public section

/-! # Reading Core source text in tests

One way to read a `program Core;` source, shared by the tests that read one from a
file or a string. -/

namespace Strata.Core.TestUtils

open Strata.CoreDDM StrataDDM in
/-- Parse the text of a `program Core;` source, named `name` in diagnostics, the
    way the `strata` CLI does (`Strata.Cli.readStrataProgram`): header-aware, via a
    dialect file map. -/
def parseCoreText (name : String) (text : ByteArray) : IO StrataDDM.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[initDialect, Core]
  let fm ← StrataDDM.DialectFileMap.new dialects
  match ← StrataDDM.readStrataText fm name text with
  | .program pgm => pure pgm
  | .dialect _ => throw (IO.userError s!"expected a program: {name}")

/-- Parse a `program Core;` source file (`parseCoreText`). -/
def parseCoreFile (path : System.FilePath) : IO StrataDDM.Program := do
  parseCoreText path.toString (← IO.FS.readBinFile path)

end Strata.Core.TestUtils

end
