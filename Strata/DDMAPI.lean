/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Util.IO
public import Strata.DDM.Ion

/-! ## Strata DDM API

File I/O for reading and writing Strata programs in textual or Ion format.
-/

public section

namespace Strata

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
