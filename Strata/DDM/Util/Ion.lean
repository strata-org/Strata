/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
A standalone Ion serialization file.
-/
import Strata.DDM.Util.Fin
import Strata.DDM.Util.Ion.Deserialize
import Strata.DDM.Util.Ion.JSON
import Strata.DDM.Util.Ion.Serialize
import Strata.DDM.Util.Lean
import Lean.Elab.Command

namespace Ion

structure SymbolTableImport where
  name : String
  version : Nat
  max_id : Option Nat

structure SymbolTable where
  array : Array String
  map : Std.HashMap String SymbolId
  locals : Array String
deriving Inhabited

namespace SymbolTable

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

def ofLocals (locals : Array String) : SymbolTable :=
  locals.foldl (init := .system) (fun tbl sym => tbl.intern sym |>.snd)

instance : Lean.Quote SymbolTable where
  quote st := Lean.Syntax.mkCApp ``SymbolTable.ofLocals #[Lean.quote st.locals]

end SymbolTable

namespace SymbolId

def systemSymbolId! (sym : String) : SymbolId := SymbolTable.system |>.symbolId! sym

-- Use metaprogramming to declare `{sym}SymbolId : SymbolId` for each system symbol.
section
open Lean
open Elab.Command

syntax (name := declareSystemSymbolIds) "#declare_system_symbol_ids" : command -- declare the syntax

@[command_elab declareSystemSymbolIds]
def declareSystemSymbolIdsImpl : CommandElab := fun _stx => do
  for sym in SymbolTable.ionSharedSymbolTableEntries do
    -- To simplify name, strip out non-alphanumeric characters.
    let simplifiedName : String := .mk <| sym.data.filter (·.isAlphanum)
    let leanName := Lean.mkLocalDeclId simplifiedName
    let cmd : TSyntax `command ← `(command|
      def $(leanName) : SymbolId := systemSymbolId! $(Lean.Syntax.mkStrLit sym)
    )
    elabCommand cmd

#declare_system_symbol_ids

end

end SymbolId

structure Position where
  indices : Array Nat := #[]
 deriving Repr

namespace Position

def root : Position := {}

def push (p : Position) (index : Nat) : Position where
  indices := p.indices.push index

def ofList (l : List Nat) : Position where
  indices := l.toArray

instance : ToString Position where
  toString p :=
    let l := p.indices |>.map toString |>.toList
    .intercalate "." ("root" :: l)

end Position

#guard toString Position.root = "root"
#guard toString (Position.root |>.push 0) = "root.0"
#guard toString (Position.root |>.push 0 |>.push 1) = "root.0.1"

namespace SymbolTable

/-- Create value-/
def localSymbolTableValue (tbl : SymbolTable) : Ion SymbolId :=
  .annotation #[SymbolId.ionsymboltable] <| .struct #[
    (.imports, .symbol .ionsymboltable),
    (.symbols, .list <| tbl.locals |>.map .string)
  ]

instance : Repr SymbolTable where
  reprPrec tbl _ := repr tbl.localSymbolTableValue

def ofLocalSymbolTable (v : Ion SymbolId) : Except (Position × String) SymbolTable := do
  let throwAt {α : Type} p s : Except _ α := throw (p, s)
  let .annotation #[a] s := v
    | throwAt .root "Expected annotation."
  if a ≠ SymbolId.ionsymboltable then
    throwAt .root "Expected ionsymboltable annotation."
  let spos : Position := .root |>.push 0
  let .struct e := s
    | throwAt spos "Expected struct"
  let mut importsSeen : Bool := false
  let mut locals : Array String := #[]
  for i in Fin.range e.size do
    let (nm, v) := e[i]
    let p := spos |>.push i.val
    if nm = .imports then
      if importsSeen then
        throwAt p s!"Multiple imports"
      importsSeen := true
    else if nm = .symbols then
      let .list localVals := v
        | throwAt p s!"Expected locals"
      for i in Fin.range localVals.size do
        let .string s := localVals[i]
          | throwAt (p.push i) "Expected string"
        locals := locals.push s
  pure <| .ofLocals locals

end SymbolTable

/--
Monad for constructing local symbol table for values.
-/
def InternM := StateM SymbolTable
  deriving Monad

def runIntern (act : InternM α) (symbols : SymbolTable := .system) : SymbolTable × α :=
  let (v, tbl) := act symbols
  (tbl, v)

def internSymbol (s : String) : InternM SymbolId := SymbolTable.intern s

namespace Ion

/--
Resolve string symbols to symbol ids by constructing local symbol table.
-/
def mapSymbolM [Monad m] (f : α → m β) : Ion α → m (Ion β)
| .null tp => pure <| .null tp
| .bool x => pure <| .bool x
| .int x => pure <| .int x
| .float f => pure <| .float f
| .decimal d => pure <| .decimal d
| .string s => pure <| .string s
| .symbol s => .symbol <$> f s
| .list a => .list <$> a.attach.mapM fun ⟨a, _⟩ => a.mapSymbolM f
| .sexp a => .sexp <$> a.attach.mapM fun ⟨a, _⟩ => a.mapSymbolM f
| .struct a => .struct <$> a.attach.mapM fun ⟨(nm, v), p⟩ =>
    have : sizeOf v < sizeOf (nm, v) := by decreasing_trivial
    have : sizeOf (nm, v) < sizeOf a + 1 := by decreasing_trivial
    return (← f nm, ←v.mapSymbolM f)
| .annotation l v => do
  let l ← l.mapM f
  return .annotation l (←v.mapSymbolM f)

/--
Resolve string symbols to symbol ids by constructing local symbol table.
-/
def intern : Ion String → InternM (Ion SymbolId) := mapSymbolM internSymbol

def unintern (tbl : SymbolTable) (v : Ion SymbolId) : Ion String := Id.run do
  v.mapSymbolM (fun s => pure (tbl[s]!))

end Ion

def intern (values : List (Ion String)) (symbols : SymbolTable := .system) : Array (Ion SymbolId) :=
  let (tbl , v) := runIntern (symbols := symbols) (values.mapM (·.intern))
  (tbl.localSymbolTableValue :: v).toArray

/--
Write values
-/
def internAndSerialize (values : List (Ion String)) (symbols : SymbolTable := .system) : ByteArray :=
  _root_.Ion.serialize <| intern (symbols := symbols) values

/--
Write a list of Ion values to file.
-/
def writeBinaryFile (path : System.FilePath) (values : List (Ion String)) (symbols : SymbolTable := system): IO Unit := do
  IO.FS.writeBinFile path (internAndSerialize values symbols)
