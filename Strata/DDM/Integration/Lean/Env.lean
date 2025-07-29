/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/

import Lean.Environment
import Strata.DDM.Elab

namespace Strata

open Lean Parser

structure PersistentDialect where
  name : DialectName
  -- Names of dialects that are imported into this dialect
  imports : Array DialectName
  declarations : Array Decl

namespace PersistentDialect

def ofDialect (d : Dialect) : PersistentDialect where
  name := d.name
  imports := d.imports
  declarations := d.declarations

def dialect (pd : PersistentDialect) : Dialect :=
  Dialect.ofArray pd.name pd.imports pd.declarations

end PersistentDialect

structure DialectState where
  loaded : Elab.LoadedDialects := Elab.DeclState.initDeclState.loader
  newDialects : Array Dialect := #[]
  deriving Inhabited

namespace DialectState

def addDialect! (s : DialectState) (d : Dialect) (isNew : Bool) : DialectState where
  loaded :=
    assert! d.name ∉ s.loaded.dialects
    s.loaded.addDialect! d
  newDialects := if isNew then s.newDialects.push d else s.newDialects

end DialectState

def mkImported (e : Array (Array PersistentDialect)) : ImportM DialectState :=
  return e.foldl (init := {}) fun s a => a.foldl (init := s) fun s d =>
    if d.name ∈ s.loaded.dialects then
      @panic _ ⟨s⟩ s!"Multiple dialects named {d.name} found in imports."
    else
      s.addDialect! d.dialect (isNew := false)

def exportEntries (s : DialectState) : Array PersistentDialect :=
  s.newDialects.map .ofDialect

initialize dialectExt : PersistentEnvExtension PersistentDialect Dialect DialectState ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := mkImported
    addEntryFn    := fun s d =>
      assert! d.name ∉ s.loaded.dialects
      DialectState.addDialect! s d (isNew := true)
    exportEntriesFn := exportEntries
  }

end Strata
