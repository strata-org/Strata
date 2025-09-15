/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab.SyntaxElab

open Strata.Parser (DeclParser ParsingContext)

namespace Strata.Elab

/--
Map from dialect names to all the declaration parsers brought into
scope for that dialect.
-/
abbrev DialectParsers := Std.HashMap DialectName (Array DeclParser)

namespace DialectParsers

def addDialect! (pm : DialectParsers) (pctx : ParsingContext) (dialect : Dialect) : DialectParsers :=
  match pctx.mkDialectParsers dialect with
  | .error msg =>
    @panic _ ⟨pm⟩ s!"Could not add open dialect: {eformat msg |>.pretty}"
  | .ok parsers => pm.insert dialect.name parsers

end DialectParsers

/--
Information about dialects.
-/
structure LoadedDialects where
  /--- Map from dialect names to the dialect definition. -/
  dialects : DialectMap
  /-- Parsers for dialects in map. -/
  dialectParsers : DialectParsers
  /--/ Map for elaborating operations and functions. -/
  syntaxElabMap : SyntaxElabMap
  deriving Inhabited

def initParsers : Parser.ParsingContext where
  fixedParsers := .ofList [
    (q`Init.Ident, Parser.identifier),
    (q`Init.Num, Parser.numLit),
    (q`Init.Decimal, Parser.decimalLit),
    (q`Init.Str, Parser.strLit)
  ]

namespace LoadedDialects

def empty : LoadedDialects where
  dialects := {}
  dialectParsers := {}
  syntaxElabMap := {}

def addDialect! (loader : LoadedDialects) (d : Dialect) : LoadedDialects :=
  assert! d.name ∉ loader.dialects
  match initParsers.mkDialectParsers d with
  | .error msg =>
    @panic _ ⟨loader⟩ s!"Could not add open dialect: {eformat msg |>.pretty}"
  | .ok parsers =>
    {
      dialects := loader.dialects.insert! d
      dialectParsers := loader.dialectParsers.insert d.name parsers
      syntaxElabMap := loader.syntaxElabMap.addDialect d
    }

def ofDialects! (ds : Array Dialect) : LoadedDialects :=
  ds.foldl (init := .empty) (·.addDialect! ·)

end LoadedDialects

abbrev LoadDialectCallback := LoadedDialects → DialectName → BaseIO (LoadedDialects × Except String Dialect)

end Elab

inductive DialectFileMap.Encoding
| ion
| text

/--
The dialect file mapping maintains a mapping from dialect names to the
file to read for loading this dialect.

It is used to identify where to find dialects that have not yet been
loaded into `LoadedDialects`.

The general principal of the map is
-/
structure DialectFileMap where
  map : Std.HashMap DialectName (IO.FS.SystemTime × DialectFileMap.Encoding × System.FilePath) := {}

namespace DialectFileMap

def strata_dialect_ext : String := ".dialect.st"

def strata_ion_dialect_ext : String := ".dialect.st.ion"

def matchExt (path : String) (ext : String) : Option String :=
  if path.endsWith ext then
    some (path.dropRight ext.length)
  else
    none

def addEntry (m : DialectFileMap) (stem : DialectName) (enc : Encoding) (path : System.FilePath) : BaseIO DialectFileMap := do
  let modTime ←
    match ← path.metadata |>.toBaseIO with
    | .error _ => return m
    | .ok md => pure md.modified
  pure <| {
    map := m.map.alter stem fun o =>
      let isNewer :=
            match o with
            | none => true
            | some (prevTime, _) => modTime > prevTime
      if isNewer then
        some (modTime, enc, path)
      else
        o
  }

def add (m : DialectFileMap) (dir : System.FilePath) : EIO String DialectFileMap := do
  let entries ←
    match ← dir.readDir |>.toBaseIO with
    | .error e => throw s!"Could not read {dir}: {e}"
    | .ok e => pure e
  entries.foldlM (init := m) fun m entry => do
    if let some stem := matchExt entry.fileName strata_dialect_ext then
      m.addEntry stem .text entry.path
    else if let some stem := matchExt entry.fileName strata_ion_dialect_ext then
      m.addEntry stem .ion entry.path
    else do
      let _ ← IO.eprintln s!"Skipping {dir / entry.fileName}" |>.toBaseIO
      pure m

def ofDirs (dirs : Array System.FilePath) : EIO String DialectFileMap :=
  dirs.foldlM (init := {}) fun m dir => m.add dir

def findPath (m : DialectFileMap) (name : DialectName) : Option System.FilePath :=
  match m.map[name]? with
  | none => none
  | some (_, _, path) => pure path

end DialectFileMap
