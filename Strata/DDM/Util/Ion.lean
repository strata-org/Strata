/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DDM.Util.Ion.AST
public import Strata.DDM.Util.Ion.Deserialize
public import Strata.DDM.Util.Ion.Serialize
public import Strata.DDM.Util.Ion.SymbolTable

import all Strata.DDM.Util.ByteArray
import all Strata.DDM.Util.Fin
import Strata.DDM.Util.Ion.Deserialize
import Strata.DDM.Util.Ion.JSON

public section
namespace Ion

/--
Returns true if this starts with the Ion binary version marker.
-/
def isIonFile (bytes : ByteArray) : Bool := bytes.startsWith binaryVersionMarker

structure Position where
  indices : Array Nat := #[]
 deriving Repr

namespace Position

private def root : Position := {}

private def push (p : Position) (index : Nat) : Position where
  indices := p.indices.push index

private def ofList (l : List Nat) : Position where
  indices := l.toArray

public instance : ToString Position where
  toString p :=
    let l := p.indices |>.map toString |>.toList
    .intercalate "." ("root" :: l)

end Position

namespace SymbolTable

/-- Create value-/
def localSymbolTableValue (tbl : SymbolTable) : Ion SymbolId :=
  .annotation #[SymbolId.ionsymboltable] <| .struct #[
    (.imports, .symbol .ionsymboltable),
    (.symbols, .list <| tbl.locals |>.map .string)
  ]

private instance : Repr SymbolTable where
  reprPrec tbl _ := repr tbl.localSymbolTableValue

def ofLocalSymbolTable (v : Ion SymbolId) : Except (Position × String) SymbolTable := do
  let throwAt {α : Type} p s : Except _ α := throw (p, s)
  let .annotation as s := v.app
    | throwAt .root "Expected annotation."
  let .isTrue asz := inferInstanceAs (Decidable (as.size = 1))
    | throwAt .root "Expected single element"
  let a := as[0]
  if a ≠ SymbolId.ionsymboltable then
    throwAt .root "Expected ionsymboltable annotation."
  let spos : Position := .root |>.push 0
  let .struct e := s.app
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
      let .list localVals := v.app
        | throwAt p s!"Expected locals"
      for i in Fin.range localVals.size do
        let .string s := localVals[i].app
          | throwAt (p.push i) "Expected string"
        locals := locals.push s
  pure <| .ofLocals locals

end SymbolTable

/--
Monad for constructing local symbol table for values.
-/
@[expose] def InternM := StateM SymbolTable
  deriving Monad

def runIntern (act : InternM α) (symbols : SymbolTable := .system) : SymbolTable × α :=
  let (v, tbl) := act symbols
  (tbl, v)

def internSymbol (s : String) : InternM SymbolId := SymbolTable.intern s

namespace Ion

/--
Resolve string symbols to symbol ids by constructing local symbol table.
-/
def mapSymbolM {m α β} [Monad m] (f : α → m β) : Ion α → m (Ion β)
| .null tp => pure <| .null tp
| .bool x => pure <| .bool x
| .int x => pure <| .int x
| .float f => pure <| .float f
| .decimal d => pure <| .decimal d
| .string s => pure <| .string s
| .symbol s => .symbol <$> f s
| .blob s => pure <| .blob s
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
def writeBinaryFile (path : System.FilePath) (values : List (Ion String)) (symbols : SymbolTable := .system): IO Unit := do
  IO.FS.writeBinFile path (internAndSerialize values symbols)

end Ion
end
