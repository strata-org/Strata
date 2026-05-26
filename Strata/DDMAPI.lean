/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO
import Strata.DDM.BuiltinDialects

/-! ## Strata DDM API

File I/O for reading and writing Strata programs in textual or Ion format.
-/

public section

namespace Strata

/-! ### DialectFileMap construction -/

/--
Build a `DialectFileMap` preloaded with the given dialects (plus the built-in
DDM dialects: `init`, `header`, and `StrataDDL`). Use this to construct a
`DialectFileMap` opaquely without touching DDM internals.
-/
def mkDialectFileMap (dialects : Array Strata.Dialect := #[])
    : IO Strata.DialectFileMap := do
  let mut loaded := Strata.Elab.LoadedDialects.builtin
  for d in dialects do
    loaded := loaded.addDialect! d
  Strata.DialectFileMap.new loaded

/--
Register a directory to search for dialect definition files
(`.dialect.st` / `.dialect.st.ion`). Returns an updated `DialectFileMap`.
-/
def DialectFileMap.addSearchPath (fm : Strata.DialectFileMap)
    (dir : System.FilePath) : EIO String Strata.DialectFileMap :=
  fm.add dir

/-! ### File I/O -/

/--
Parse a Strata dialect or program in textual format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
def readStrataText :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readStrataText

/--
Parse a Strata dialect or program in Ion format, possibly loading other
dialects as needed along the way. The `DialectFileMap` indicates where to find
the definitions of other dialects. The `FilePath` indicates the name of the file
to be parsed. And the `ByteArray` includes the contents of that file. TODO:
should it take just a file name and read it directly?
-/
def readStrataIon :
  Strata.DialectFileMap →
  System.FilePath →
  ByteArray →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readStrataIon

/--
Parse a Strata dialect or program in either textual or Ion format, possibly
loading other dialects as needed along the way. The `DialectFileMap` indicates
where to find the definitions of other dialects. The `FilePath` indicates the name
of the file to be loaded.
-/
def readStrataFile :
  Strata.DialectFileMap →
  System.FilePath →
  IO Strata.Util.DialectOrProgram :=
  Strata.Util.readFile

/--
Read a Strata file (text or Ion) and require it to be a program. Fails if the
file defines a dialect.
-/
def readStrataProgramFile (fm : Strata.DialectFileMap) (path : System.FilePath)
    : IO Strata.Program := do
  match ← Strata.Util.readFile fm path with
  | .program pgm => pure pgm
  | .dialect _ => throw (IO.userError s!"Expected a program file, got a dialect: {path}")

/--
Read a Strata file (text or Ion) and require it to be a dialect. Fails if the
file defines a program.
-/
def readStrataDialectFile (fm : Strata.DialectFileMap) (path : System.FilePath)
    : IO Strata.Dialect := do
  match ← Strata.Util.readFile fm path with
  | .dialect d => pure d
  | .program _ => throw (IO.userError s!"Expected a dialect file, got a program: {path}")

/--
Serialize a Strata program in textual format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataText : Strata.Program → ByteArray
| pgm => String.toByteArray pgm.toString

/--
Serialize a Strata program in Ion format. Returns a byte array rather than
writing directly to a file.
-/
def writeStrataIon : Strata.Program → ByteArray
| pgm => pgm.toIon

end Strata

end -- public section
