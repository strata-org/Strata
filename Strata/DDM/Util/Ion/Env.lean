/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Lean.Environment
import Lean.ToExpr

namespace Ion

open Lean

inductive SymbolTableEntry where
| string (s : String)
| record (name : Lean.Name)
deriving DecidableEq, Hashable, Repr

instance : Coe String SymbolTableEntry where
  coe := .string

instance : ToExpr SymbolTableEntry where
  toTypeExpr :=  mkConst ``SymbolTableEntry
  toExpr
  | .string s =>  mkApp (mkConst ``SymbolTableEntry.string) (toExpr s)
  | .record n =>  mkApp (mkConst ``SymbolTableEntry.record) (toExpr n)

structure NameSymbols where
  name : Lean.Name
  entries : Array SymbolTableEntry

structure SymbolTableEntries where
  array : Array SymbolTableEntry := #[]
  names : Std.HashMap SymbolTableEntry Nat := {}

def SymbolTableEntries.push (a : SymbolTableEntries) (e : SymbolTableEntry) :=
  if e ∈ a.names then
    a
  else
    let sz := a.array.size
    { array := a.array.push e, names := a.names.insert e sz }

def SymbolTableEntries.ofArray (a : Array SymbolTableEntry) : SymbolTableEntries where
  array := a
  names := a.size.fold (init := {}) fun i lt m => m.insert a[i] i

structure IonTypeState where
  map₁   : Std.HashMap Name (Array SymbolTableEntry) := {}
  map₂   : Lean.PHashMap Name SymbolTableEntries := {}
  scope : Option (Name × Expr) := .none
  deriving Inhabited

namespace IonTypeState

def addType (s : IonTypeState) (d : NameSymbols) : IonTypeState where
  map₁ := s.map₁
  map₂ := s.map₂.insert d.name (.ofArray d.entries)
  scope := s.scope

def getEntries? (s : IonTypeState) (name : Lean.Name) : Option (Array SymbolTableEntry) :=
  match s.map₂.find? name with
  | some e => some e.array
  | none => s.map₁[name]?

def getEntries (s : IonTypeState) (name : Lean.Name) : Array SymbolTableEntry :=
  match s.map₂.find? name with
  | some e => e.array
  | none => s.map₁.getD name #[]

def getIndexOf (s : IonTypeState) (name : Lean.Name) (entry : SymbolTableEntry) : Nat :=
  if name ∈ s.map₁ then
    panic! "Cannot extend imported names"
  else
    match s.map₂.find? name with
    | none => panic! s!"Cannot find {name}"
    | some e => e.names.getD entry e.array.size

def addEntry (s : IonTypeState) (name : Lean.Name) (entry : SymbolTableEntry) : IonTypeState :=
  if name ∈ s.map₁ then
    panic! "Cannot extend imported names"
  else
    let { map₁ := map₁, map₂ := map₂, scope := scope } := s
    let a : SymbolTableEntries := map₂.findD name {}
    let map₂ := map₂ |>.insert name {} |>.insert name (a.push entry)
    { map₁ := map₁, map₂ := map₂, scope := scope }

def exportEntries (s : IonTypeState) : Array NameSymbols :=
  s.map₂.foldl (init := #[]) fun a nm v => a.push ⟨nm, v.array⟩

def mkImported (e : Array (Array NameSymbols)) : ImportM IonTypeState :=
  return {
      map₁ := e.foldl (init := {}) fun m a =>
        a.foldl (init := m) fun m e => m.insert e.name e.entries
      map₂ := {}
  }

end IonTypeState

initialize ionDialectExt : PersistentEnvExtension NameSymbols NameSymbols IonTypeState ←
  registerPersistentEnvExtension {
    mkInitial := pure {},
    addImportedFn := IonTypeState.mkImported
    addEntryFn    := IonTypeState.addType
    exportEntriesFn := IonTypeState.exportEntries
  }

end Ion
