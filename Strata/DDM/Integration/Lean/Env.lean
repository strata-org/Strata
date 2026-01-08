/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Lean.Environment
public import Strata.DDM.Elab.LoadedDialects
import Strata.DDM.BuiltinDialects

namespace Strata

open Lean Parser

public structure PersistentDialect where
  leanName : Lean.Name
  name : DialectName
  -- Names of dialects that are imported into this dialect
  imports : Array DialectName
  declarations : Array Decl

namespace PersistentDialect

def ofDialect (leanName : Name) (d : Dialect) : PersistentDialect where
  leanName := leanName
  name := d.name
  imports := d.imports
  declarations := d.declarations

def dialect (pd : PersistentDialect) : Dialect :=
  Dialect.ofArray pd.name pd.imports pd.declarations

end PersistentDialect

public structure DialectState where
  loaded : Elab.LoadedDialects
  nameMap : Std.HashMap DialectName Name
  newDialects : Array (Name × Dialect)
deriving Inhabited

namespace DialectState

instance : EmptyCollection DialectState where
  emptyCollection := {
    loaded := .builtin,
    nameMap := .ofList [
      (initDialect.name, ``initDialect),
      (headerDialect.name, ``headerDialect),
      (StrataDDL.name, ``StrataDDL),
    ],
    newDialects := #[]
  }

public def addDialect! (s : DialectState) (d : Dialect) (name : Name) (isNew : Bool) : DialectState where
  loaded :=
    assert! d.name ∉ s.loaded.dialects
    s.loaded.addDialect! d
  nameMap :=
    assert! d.name ∉ s.nameMap
    s.nameMap.insert d.name name
  newDialects := if isNew then s.newDialects.push (name, d) else s.newDialects

end DialectState

def mkImported (e : Array (Array PersistentDialect)) : ImportM DialectState :=
  return e.foldl (init := {}) fun s a => a.foldl (init := s) fun s d =>
    if d.name ∈ s.loaded.dialects then
      @panic _ ⟨s⟩ s!"Multiple dialects named {d.name} found in imports."
    else
      s.addDialect! d.dialect d.leanName (isNew := false)

def exportEntries (s : DialectState) : Array PersistentDialect :=
  s.newDialects.map fun (n, d) => .ofDialect n d

public initialize dialectExt : PersistentEnvExtension PersistentDialect (Name × Dialect) DialectState ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := mkImported
    addEntryFn    := fun s (leanName, d) =>
      assert! d.name ∉ s.loaded.dialects
      DialectState.addDialect! s d leanName (isNew := true)
    exportEntriesFn := exportEntries
  }

end Strata
