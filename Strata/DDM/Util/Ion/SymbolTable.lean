/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.Ion.AST
meta import Lean.Elab.Command
meta import Strata.DDM.Util.Lean

public section
namespace Ion

structure SymbolTable where
  array : Array String
  map : Std.HashMap String SymbolId
  locals : Array String
deriving Inhabited

namespace SymbolTable

instance : GetElem? SymbolTable SymbolId String (fun tbl idx => idx.value < tbl.array.size) where
  getElem tbl idx p := tbl.array[idx.value]
  getElem! tbl idx := assert! idx.value < tbl.array.size; tbl.array[idx.value]!
  getElem? tbl idx := tbl.array[idx.value]?

def symbolId! (sym : String) (tbl : SymbolTable) : SymbolId :=
  match tbl.map[sym]? with
  | some i => i
  | none => panic! s!"Unbound symbol {sym}"

/--
Intern a string into a symbol.
-/
def intern (sym : String) (tbl : SymbolTable) : SymbolId × SymbolTable :=
  match tbl.map[sym]? with
  | some i => (i, tbl)
  | none =>
    let i : SymbolId := .mk (tbl.array.size)
    let tbl := {
      array := tbl.array.push sym,
      map := tbl.map.insert sym i,
      locals := tbl.locals.push sym
    }
    (i, tbl)

def ionSharedSymbolTableEntries : Array String := #[
  "$ion", "$ion_1_0", "$ion_symbol_table", "name", "version",
  "imports", "symbols", "max_id", "$ion_shared_symbol_table"
]

/--
Minimal system symbol table.
-/
def system : SymbolTable where
  array := #[""] ++ ionSharedSymbolTableEntries
  map := ionSharedSymbolTableEntries.size.fold (init := {}) fun i _ m =>
    m.insert ionSharedSymbolTableEntries[i] (.mk (i+1))
  locals := #[]

def ofLocals (locals : Array String) : SymbolTable :=
  locals.foldl (init := .system) (fun tbl sym => tbl.intern sym |>.snd)

public instance : Lean.Quote SymbolTable where
  quote st := Lean.Syntax.mkCApp ``SymbolTable.ofLocals #[Lean.quote st.locals]

end SymbolTable

namespace SymbolId

def systemSymbolId! (sym : String) : SymbolId := SymbolTable.system |>.symbolId! sym

-- Use metaprogramming to declare `{sym}SymbolId : SymbolId` for each system symbol.
section
open Lean
open Elab.Command

-- Declare all system symbol ids as constants
run_cmd do
  for sym in SymbolTable.ionSharedSymbolTableEntries do
    -- To simplify name, strip out non-alphanumeric characters.
    let simplifiedName : String := .ofList <| sym.toList.filter (·.isAlphanum)
    let leanName := Lean.mkLocalDeclId simplifiedName
    let cmd : TSyntax `command ← `(command|
      public def $(leanName) : SymbolId := systemSymbolId! $(Lean.Syntax.mkStrLit sym)
    )
    elabCommand cmd

end

end SymbolId

end Ion
