/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import StrataDDM.Util.SourceRange
public import Lean.Data.Position
public import Lean.ToExpr

open Std (Format)

public section
namespace Strata
export StrataDDM (SourceRange)

abbrev SourceRange.none := StrataDDM.SourceRange.none

inductive Uri where
  | file (path: String)
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : Std.ToFormat Uri where
 format fr := private match fr with | .file path => path

instance : Hashable SourceRange where
  hash sr := mixHash (hash sr.start) (hash sr.stop)

structure FileRange where
  file: Uri
  range: SourceRange
  deriving DecidableEq, Repr, Inhabited, Hashable

instance : Std.ToFormat FileRange where
 format fr := private f!"{fr.file}:{fr.range}"

structure File2dRange where
  file: Uri
  start: Lean.Position
  ending: Lean.Position
  deriving DecidableEq, Repr

instance : Std.ToFormat File2dRange where
 format fr := private
    let baseName := match fr.file with
                    | .file path => (path.splitToList (· == '/')).getLast!
    f!"{baseName}({fr.start.line}, {fr.start.column})-({fr.ending.line}, {fr.ending.column})"

instance : Std.ToFormat FileRange where
 format fr := f!"{fr.file}:{fr.range}"

/-- A sentinel file range indicating no real source location is available.

Do not add new uses: propagate a real source location from the context instead
(e.g. the procedure name, or the expression being transformed). Where the type
only needs *some* `FileRange` to satisfy an `Inhabited` obligation, use
`default` — `FileRange` derives `Inhabited`, and `default` reads as "placeholder"
rather than as a location worth reporting.

The uses that remain are all migrations still in flight:
- `Identifier.source`'s default, until every `mkId` call site supplies a range.
- The `Option FileRange`-to-`FileRange` bridges in Core (`getD`), until Core's
  metadata carries a `FileRange` unconditionally.
- `Message.fromString`/`fromFormat`, for diagnostics not yet located. -/
def FileRange.unknown : FileRange :=
  { file := .file "<unknown>", range := SourceRange.none }

/-- Format a file range using a FileMap to convert byte offsets to line/column positions. -/
def FileRange.format (fr : FileRange) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let baseName := match fr.file with
                  | .file path => (path.splitToList (· == '/')).getLast!
  match fileMap with
  | some fm =>
    if fr.range.isNone then f!"" else
    -- Lean's InputContext may have a fileMap which has an empty source and
    -- position. This can happen when InputContext is assigned Inhabited.default.
    if fm.source.isEmpty ∧ fm.positions.isEmpty then f!"" else
    let startPos := fm.toPosition fr.range.start
    let endPos := fm.toPosition fr.range.stop
    if includeEnd? then
      if startPos.line == endPos.line then
        f!"{baseName}({startPos.line}, ({startPos.column}-{endPos.column}))"
      else
        f!"{baseName}(({startPos.line}, {startPos.column})-({endPos.line}, {endPos.column}))"
    else
      f!"{baseName}({startPos.line}, {startPos.column})"
  | none =>
    if fr.range.isNone then
      f!""
    else
      f!"{baseName}({fr.range.start}-{fr.range.stop})"

end Strata
end
