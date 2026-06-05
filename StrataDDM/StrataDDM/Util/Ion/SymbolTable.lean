/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataDDM.Util.Ion.AST

public section
namespace Ion

structure SymbolTable where
  private mk ::
  private array : Array String
  private map : Std.HashMap String SymbolId
  locals : Array String
deriving Inhabited

namespace SymbolTable

def size (tbl : SymbolTable) : Nat := tbl.array.size

instance : GetElem? SymbolTable SymbolId String (fun tbl idx => idx.value < tbl.size) where
  getElem tbl idx p := private tbl.array[idx.value]
  getElem! tbl idx := private tbl.array[idx.value]!
  getElem? tbl idx := private tbl.array[idx.value]?

/-- Lookup symbol and return `SymbolId.zero` if not defined. -/
def symbolId (sym : String) (tbl : SymbolTable) : SymbolId :=
  tbl.map.getD sym .zero

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

instance : Lean.Quote SymbolTable where
  quote st := Lean.Syntax.mkCApp ``SymbolTable.ofLocals #[Lean.quote st.locals]

end SymbolTable

end Ion
