/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
This file provides type classes that work together with a Lean environment
extension to create high performance Ion serialization and deserialization.
-/
import Strata.DDM.Util.Ion
import Strata.DDM.Util.Ion.Env
import Lean.Meta.Eval

namespace Ion

open Lean Elab

/--
Stores tables used to efficiently serialize values.
-/
structure SymbolIdCache where
  /-- Global array for entries -/
  globalCache : Array Nat
  /-- Offset into global array for this type. -/
  offset : Nat

namespace SymbolIdCache

def id! (refs : SymbolIdCache) (i : Nat) : SymbolId :=
  if p : refs.offset + i < refs.globalCache.size then
   .mk refs.globalCache[refs.offset + i]
  else
    panic! s!"Invalid string id {refs.offset} + {i} (max = {refs.globalCache.size})"

/-
Returns the symbol id cache for the given type and index.
-/
def ref! (refs : SymbolIdCache) (tp : String) (i : Nat) : SymbolIdCache where
  globalCache := refs.globalCache
  offset :=
    if p : refs.offset + i < refs.globalCache.size then
      refs.globalCache[refs.offset + i]
    else
      panic! s!"{tp} has invalid symbol ref {refs.offset} + {i} (max = {refs.globalCache.size})"

end SymbolIdCache

structure LeanSymbolTableMap where
  symtab : Ion.SymbolTable := .system
  nameMap : Std.HashMap Lean.Name Nat := {}
  entries : Array Nat := #[]
deriving Inhabited

namespace LeanSymbolTableMap

def addEntry : SymbolTableEntry → StateM LeanSymbolTableMap Nat
| .record nm, tbl =>
  match tbl.nameMap[nm]? with
  | none => panic! s!"Unknown name {nm}"
  | some n => (n, tbl)
| .string s, tbl =>
  let symtab := tbl.symtab
  let tbl := { tbl with symtab := default }
  let (sym, symtab) := symtab.intern s
  (sym.value, { tbl with symtab := symtab })

def addRecord (tbl : LeanSymbolTableMap) (name : Lean.Name) (entries : Array SymbolTableEntry) : Nat × LeanSymbolTableMap :=
  let (entries, tbl) := entries.mapM addEntry tbl
  let thisIdx := tbl.entries.size
  let tbl := { tbl with
    nameMap := tbl.nameMap.insert name thisIdx
    entries := tbl.entries ++ entries
  }
  (thisIdx, tbl)

partial def addToSymbolTable (s : IonTypeState) (name : Name) : StateT LeanSymbolTableMap (Except String) Nat := do
  match (← get).nameMap[name]? with
  | some n => return n
  | none => pure ()
  match s.getEntries? name with
  | none =>
    pure 0
  | some entries =>
    let thisIdx := (←get).entries.size
    modify fun tbl => { tbl with
        nameMap := tbl.nameMap.insert name thisIdx
        entries := entries.size.repeat (·.push 0) tbl.entries
      }
    let entries ← entries.mapM fun e =>
      match e with
      | .record nm => do
        pure <| (← addToSymbolTable s nm)
      | .string s => do
        let symtab := (←get).symtab
        modify fun tbl => { tbl with symtab := default }
        let (sym, symtab) := symtab.intern s
        modify fun tbl => { tbl with symtab := symtab }
        pure <| sym.value
    modify fun tbl =>
      assert! tbl.entries.size ≥ thisIdx + entries.size
      { tbl with
        entries := entries.size.fold (init := tbl.entries) (fun i p e => e.set! (thisIdx + i) entries[i])
      }
    pure thisIdx

end LeanSymbolTableMap

structure FromIonCache where
  entries : Array String
  cache : SymbolIdCache

class FromIon (α : Type _) where
  fromIon : FromIonCache → Ion SymbolId → α

class CachedToIon (α : Type _) where
  cachedToIon : SymbolIdCache → α → InternM (Ion SymbolId)

namespace CachedToIon

instance [h : CachedToIon α] : CachedToIon (Array α) where
  cachedToIon refs a := .list <$> a.mapM (cachedToIon refs)

instance [h : CachedToIon α] : CachedToIon (List α) where
  cachedToIon refs a := .list <$> a.toArray.mapM (cachedToIon refs)

end CachedToIon

private def resolveGlobalDecl {m : Type → Type} [AddMessageContext m] [Monad m] [MonadResolveName m] [MonadEnv m] [MonadError m] [MonadLog m] [MonadOptions m] (tp : Syntax) : m Name := do
  let cs ← resolveGlobalName tp.getId
  match cs with
  | [(tpName, [])] =>
    return tpName
  | _ =>
    throwErrorAt tp s!"Could not identify unique type for {tp}."

def resolveEntry (stx : Syntax) (entry : SymbolTableEntry) : TermElabM (Lean.Expr × Lean.Expr) := do
  let s := Ion.ionDialectExt.getState (← getEnv)
  match s |>.scope with
  | .none =>  throw <| .error stx m!"Mising scope: Use ionScope!"
  | some (name, r) =>
    let idx := Ion.ionDialectExt.getState (← getEnv) |>.getIndexOf name entry
    modifyEnv fun env => Ion.ionDialectExt.modifyState env (·.addEntry name entry)
    return (r, mkNatLit idx)

syntax (name := declareIonScope) "ionScope!" ident term ":" term : term -- declare the syntax

@[term_elab declareIonScope]
def declareIonScopeImpl : Elab.Term.TermElab := fun stx expectedType =>
  match stx with
  | `(ionScope! $tp $r : $e) => do
    match Ion.ionDialectExt.getState (← getEnv) |>.scope with
    | .none => pure ()
    | some _ =>
      throw <| .error stx m!"Already inside scope"
    let tpName ← resolveGlobalDecl tp
    let rt ← Term.elabTerm r (some (.const ``SymbolIdCache []))
    if (Ion.ionDialectExt.getState (←getEnv)).map₂.contains tpName then
      throw <| .error tp m!"{tpName} already defined."
    modifyEnv fun env => Ion.ionDialectExt.modifyState env fun s =>
      { s with
        map₂ := s.map₂.insert tpName {}
        scope := some (tpName, rt)
      }
    let r ← Term.elabTerm e expectedType
    modifyEnv fun env => Ion.ionDialectExt.modifyState env fun s =>
      { s with scope := none }
    return r
  | _ =>
    throwUnsupportedSyntax

syntax:max (name := declareIonSymbol) "ionSymbol!" str : term -- declare the syntax

@[term_elab declareIonSymbol]
def declareIonSymbolImpl : Elab.Term.TermElab := fun stx _ =>
  match stx with
  | `(ionSymbol! $fld) => do
    let (r, e) ← resolveEntry stx (.string fld.getString)
    return mkApp2 (.const ``SymbolIdCache.id! []) r e
  | _ =>
    throwUnsupportedSyntax

def typeOf {α : Type u} (_ : α) : Type u := α

initialize Lean.registerTraceClass `Strata.ionTypeOf

syntax (name := declareIonTypeOf) "ionTypeOf!" term : term -- declare the syntax

@[term_elab declareIonTypeOf]
def declareIonTypeOfImpl : Elab.Term.TermElab := fun stx _ =>
  match stx with
  | `(ionTypeOf! $fld) => do
    let fldName ← do
          let fldExpr ← Term.elabTerm fld none
          let fldType ← instantiateMVars =<< Meta.inferType fldExpr
          match fldType with
          | .const fldName [] => pure fldName
          | .app (.const ``Array [_]) (.const fldName []) => pure fldName
          | .app (.const ``List [_]) (.const fldName []) => pure fldName
          | _ =>
            throw <| .error fld m!"Expected a named type instead of {repr fldType}"
    trace[Strata.ionTypeOf] "Type is {fldName}"
    return toExpr fldName
  | _ =>
    throwUnsupportedSyntax


syntax (name := declareIonRefEntry) "ionRefEntry!" term : term -- declare the syntax

@[term_elab declareIonRefEntry]
unsafe def declareIonRefCacheImpl : Elab.Term.TermElab := fun stx _ =>
  match stx with
  | `(ionRefEntry! $fldNameStx) => do
    let nameType : Expr := .const `Lean.Name []
    let fldNameExpr ← Term.elabTerm fldNameStx (expectedType? := some nameType)
    let fldName ← Lean.Meta.evalExpr Name nameType fldNameExpr
    let (r, e) ← resolveEntry stx (.record fldName)
    return mkApp3 (.const ``SymbolIdCache.ref! []) r (toExpr fldName.toString) e
  | _ =>
    throwUnsupportedSyntax

notation "ionRef!" s => CachedToIon.cachedToIon (ionRefEntry! (ionTypeOf! s)) s

syntax (name := getIonEntries) "ionEntries!" "(" ident ")" : term -- declare the syntax

@[term_elab getIonEntries]
def getIonEntriesImpl : Lean.Elab.Term.TermElab := fun stx _ =>
  match stx with
  | `(ionEntries!($tp)) => do
    let name := tp.getId
    let a := Ion.ionDialectExt.getState (← getEnv) |>.getEntries name
    return toExpr a
  | _ =>
    throwUnsupportedSyntax

private def mkIdent (si : SourceInfo) (n : Name) : TSyntax `ident := ⟨.ident si n.toString.toSubstring n []⟩

syntax (name := declareIonSymbolTable) "#declareIonSymbolTable" ident : command -- declare the syntax

@[command_elab declareIonSymbolTable]
def declareIonSymbolTableImpl : Command.CommandElab := fun stx =>
  match stx with
  | `(#declareIonSymbolTable $tp) => do
    let name ← resolveGlobalDecl tp
    let s := ionDialectExt.getState (← getEnv)
    let (tblIdx, tbl) ←
      match LeanSymbolTableMap.addToSymbolTable s name {} with
      | .ok r => pure r
      | .error msg => throwErrorAt stx msg
    let si := stx.getInfo?.getD .none
    let name := `_root_ ++ name
    let ionSymbolCache : TSyntax `ident := mkIdent si (.str name "ionSymbolCache")
    let ionSymbolTable : TSyntax `ident := mkIdent si (.str name "ionSymbolTable")
    let toIonPair : TSyntax `ident := mkIdent si (.str name "toIonValues")
    let toIon : TSyntax `ident := mkIdent si (.str name "toIon")
    Command.elabCommand =<< `(
      def $ionSymbolCache : SymbolIdCache := { globalCache := $(quote tbl.entries), offset := $(quote tblIdx) }
    )
    Command.elabCommand =<< `(
      def $ionSymbolTable : SymbolTable := $(quote tbl.symtab)
    )
    let toIonImplDef ← ``(fun v =>
          runIntern (symbols := $ionSymbolTable) (CachedToIon.cachedToIon $ionSymbolCache v)
    )
    Command.elabCommand =<< `(
      def $toIonPair : $tp → SymbolTable × Ion SymbolId := $toIonImplDef
    )
    Command.elabCommand =<< `(
      def $toIon (x : $tp) : ByteArray :=
        let (tbl, v) := $toIonPair x
        _root_.Ion.serialize #[tbl.localSymbolTableValue, v]
    )
  | _ =>
    throwUnsupportedSyntax

end Ion
