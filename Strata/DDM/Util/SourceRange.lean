/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean.Data.Position

public section
namespace Strata

/--
Source location information in the DDM is defined
by a range of bytes in a UTF-8 string with the input
Line/column information can be constructed from a
`Lean.FileMap`

As an example, in the string `"123abc\ndef"`, the string
`"abc"` has the position `{start := 3, stop := 6 }` while
`"def"` has the position `{start := 7, stop := 10 }`.
-/
structure SourceRange where
  /-- The starting offset of the source range. -/
  start : String.Pos.Raw
  /-- One past the end of the range. -/
  stop : String.Pos.Raw
deriving DecidableEq, Inhabited, Repr

namespace SourceRange

def none : SourceRange := { start := 0, stop := 0 }

def isNone (loc : SourceRange) : Bool := loc.start = 0 ∧ loc.stop = 0

instance : Std.ToFormat SourceRange where
 format fr := f!"{fr.start}-{fr.stop}"

/-- Format a SourceRange as a string using a FileMap for line:column conversion.
    Renders location information in a format VSCode understands.
    Returns "path:line:col-col" if on same line, otherwise "path:line:col". -/
def format (loc : SourceRange) (path : System.FilePath) (fm : Lean.FileMap) : String :=
  let spos := fm.toPosition loc.start
  let epos := fm.toPosition loc.stop
  if spos.line == epos.line then
    s!"{path}:{spos.line}:{spos.column+1}-{epos.column+1}"
  else
    s!"{path}:{spos.line}:{spos.column+1}"

end Strata.SourceRange
end
