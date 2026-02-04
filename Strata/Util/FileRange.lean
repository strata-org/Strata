/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DDM.Util.SourceRange
public import Lean.Data.Position

open Std (Format)

public section
namespace Strata

inductive Uri where
  | file (path: String)
  deriving DecidableEq, Repr, Inhabited

instance : Std.ToFormat Uri where
 format fr := private match fr with | .file path => path

structure FileRange where
  file: Uri
  range: SourceRange
  deriving DecidableEq, Repr, Inhabited

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

/-- A default file range for errors without source location.
This should only be used for generated nodes that are guaranteed to be correct. -/
def FileRange.unknown : FileRange :=
  { file := .file "<unknown>", range := SourceRange.none }

/-- Format a file range using a FileMap to convert byte offsets to line/column positions. -/
def FileRange.format (fr : FileRange) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let baseName := match fr.file with
                  | .file path => (path.splitToList (· == '/')).getLast!
  match fileMap with
  | some fm =>
    let startPos := fm.toPosition fr.range.start
    let endPos := fm.toPosition fr.range.stop
    if includeEnd? then
      if startPos.line == endPos.line then
        f!"{baseName}({startPos.line},({startPos.column}-{endPos.column}))"
      else
        f!"{baseName}(({startPos.line},{startPos.column})-({endPos.line},{endPos.column}))"
    else
      f!"{baseName}({startPos.line}, {startPos.column})"
  | none =>
    if fr.range.isNone then
      f!""
    else
      f!"{baseName}({fr.range.start}-{fr.range.stop})"

/-- A diagnostic model that holds a file range and a message.
    This can be converted to a formatted string using a FileMap. -/
structure DiagnosticModel where
  fileRange : FileRange
  message : String
  deriving Repr, BEq, Inhabited

instance : Inhabited DiagnosticModel where
  default := { fileRange := FileRange.unknown, message := "" }

/-- Create a DiagnosticModel from just a message (using default location).
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.fromMessage (msg : String) : DiagnosticModel :=
  { fileRange := FileRange.unknown, message := msg }

/-- Create a DiagnosticModel from a Format (using default location).
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.fromFormat (fmt : Std.Format) : DiagnosticModel :=
  { fileRange := FileRange.unknown, message := toString fmt }

/-- Create a DiagnosticModel with source location. -/
def DiagnosticModel.withRange (fr : FileRange) (msg : Format) : DiagnosticModel :=
  { fileRange := fr, message := toString msg }

/-- Format a DiagnosticModel using a FileMap to convert byte offsets to line/column positions. -/
def DiagnosticModel.format (dm : DiagnosticModel) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  let rangeStr := dm.fileRange.format fileMap includeEnd?
  if dm.fileRange.range.isNone then
    f!"{dm.message}"
  else
    f!"{rangeStr} {dm.message}"

/-- Format just the file range portion of a DiagnosticModel. -/
def DiagnosticModel.formatRange (dm : DiagnosticModel) (fileMap : Option Lean.FileMap) (includeEnd? : Bool := true) : Std.Format :=
  dm.fileRange.format fileMap includeEnd?

/-- Update the file range of a DiagnosticModel if it's currently unknown.
This should not be called, it only exists temporarily to enable incrementally
migrating code without error locations -/
def DiagnosticModel.withRangeIfUnknown (dm : DiagnosticModel) (fr : FileRange) : DiagnosticModel :=
  if dm.fileRange.range.isNone then
    { dm with fileRange := fr }
  else
    dm

instance : ToString DiagnosticModel where
  toString dm := dm.format none |> toString

end Strata
end
