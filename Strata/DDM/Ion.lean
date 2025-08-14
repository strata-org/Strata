/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.DDM.Util.Ion.Lean

namespace Strata

open _root_.Lean
open Elab Command

open _root_.Ion

inductive StringOrSexp (v : Ion SymbolId) where
| string (s : String)
| sexp (a : Array (Ion SymbolId)) (p : sizeOf a < sizeOf v)

structure StructArgMap (size : Nat) where
  map : Std.HashMap String (Fin size) := {}

namespace StructArgMap

instance : Membership String (StructArgMap size) where
  mem m nm := nm ∈ m.map

instance : GetElem? (StructArgMap size) String (Fin size) (fun m nm => nm ∈ m) where
  getElem m nm p := m.map[nm]
  getElem! m nm := m.map[nm]!
  getElem? m nm := m.map[nm]?

def fromList! (as : List String) : StructArgMap as.length :=
  let size := as.length
  let m := as.foldl (init := {}) fun m nm =>
    if nm ∈ m then
      panic! s!"Duplicate name {nm}"
    else if p : m.size < size then
      m.insert nm ⟨m.size, p⟩
    else
      panic! "Invalid index"
  { map := m }

end StructArgMap

structure FromIonContext where
  symbols : Ion.SymbolTable

def FromIonM := ReaderT FromIonContext (Except String)
  deriving Monad

namespace FromIonM

instance : MonadExcept String FromIonM :=
  inferInstanceAs (MonadExcept _ (ReaderT _ _))

instance : MonadReader FromIonContext FromIonM :=
  inferInstanceAs (MonadReader _ (ReaderT _ _))

def readSymbolTable : FromIonM Ion.SymbolTable :=
  return (← read).symbols

protected def lookupSymbol (sym : SymbolId) : FromIonM String := do
  let some fullname := (←readSymbolTable)[sym]?
    | throw s!"Could not find symbol {sym.value}"
  pure fullname

protected def asSymbolString (v : Ion SymbolId) : FromIonM String :=
  match v.app with
  | .symbol sym => .lookupSymbol sym
  | .string name => pure name
  | _ => throw s!"Expected {repr v} to be a string."

protected def asInt (v : Ion SymbolId) : FromIonM Int :=
  match v.app with
  | .int x => pure x
  | .string s =>
    match s.toInt? with
    | some x => pure x
    | none => throw s!"Expected {s} to be an int."
  | _ => throw s!"Expected {repr v} to be an int."

protected def asNat (v : Ion SymbolId) : FromIonM Nat :=
  match v.app with
  | .int x =>
    if x < 0 then
      throw s! "Expected {x} to be a nat."
    else
      pure x.toNat
  | .string s =>
    match s.toNat? with
    | some x => pure x
    | none => throw s!"Expected {s} to be a nat."
  | _ => throw s!"Expected {repr v} to be a nat."

protected def asString (v : Ion SymbolId) : FromIonM String :=
  match v with
  | .string s => return s
  | _ => throw s!"Expected string."

protected def asList (v : Ion SymbolId) : FromIonM { a : Array (Ion SymbolId) // sizeOf a < sizeOf v} :=
  match v with
  | .mk (.list args) =>
    return .mk args (by simp; omega)
  | _ => throw s!"Expected list"

protected def asSexp (v : Ion SymbolId) : FromIonM ({ a : Array (Ion SymbolId) // a.size > 0 ∧ sizeOf a < sizeOf v}) :=
  match v with
  | .mk (.sexp args) | .mk (.list args) =>
    if p : args.size > 0 then
      pure <| .mk args ⟨p,  by decreasing_tactic⟩
    else
      throw s!"Expected non-empty expression"
  | _ => throw s!"Expected sexpression."

protected def asSymbolOrSexp (v : Ion SymbolId) : FromIonM (StringOrSexp v) :=
  match v with
  | .symbol s => .string <$> .lookupSymbol s
  | .string s => return .string s
  | .mk (.sexp args) | .mk (.list args) => pure (.sexp args (by decreasing_tactic))
  | _ => throw s!"Expected symbol or sexpression."

def checkArgCount (name : String) (args : Array Size) (n : Nat) : FromIonM (PLift (args.size = n)) := do
    if p : args.size = n then
      pure ⟨p⟩
    else
      throw s!"{name} expects {n} arguments"

def asArray (v : Ion SymbolId) : FromIonM (Array (Ion SymbolId)) :=
  match v with
  | .list a => pure a
  | _ => throw "Expected a list"

def asStruct0 (v : Ion SymbolId) : FromIonM (Array (SymbolId × Ion SymbolId)) := do
  match v with
  | .mk (.struct args) => pure args
  | _ => throw "Expected a struct"

def asStruct  (v : Ion SymbolId) : FromIonM { a : Array (SymbolId × Ion SymbolId) // sizeOf a < sizeOf v } := do
  match v with
  | .mk (.struct args) => pure ⟨args, by decreasing_tactic ⟩
  | _ => throw "Expected a struct"

private def sizeOfListLowerBound [h : SizeOf α] (l : List α) : sizeOf l > l.length := by
  match l with
  | [] =>
    simp
  | h :: r =>
    have p := sizeOfListLowerBound r
    decreasing_tactic

private def sizeOfArrayLowerBound [h : SizeOf α] (a : Array α) : sizeOf a ≥ 2 + a.size := by
  match a with
  | ⟨l⟩ =>
    have p := sizeOfListLowerBound l
    decreasing_tactic

def mapFields {size} (args : Array (SymbolId × Ion SymbolId)) (m : StructArgMap size) :
  FromIonM (Vector (Ion SymbolId) size) := do
  -- We use an assigned vector below to check
  if q : args.size ≠ size then
    throw s!"Unexpected number of arguments to struct."
  else if p : args.size = 0 then
    return ⟨#[], by simp; omega⟩
  else
  --  have szu : sizeOf v = sizeOf args + 2 := by simp [veq]; omega
    let init : Ion SymbolId :=
      have p : sizeOf args[0].snd < sizeOf args[0] := by
        match args[0] with
        | ⟨fld, v⟩ => decreasing_tactic
      have q : sizeOf args[0] < sizeOf args := by decreasing_tactic
      args[0].snd
    let a := Vector.replicate size init
    let assigned := Vector.replicate size false
    let (a, assigned) ← args.attach.foldlM (init := (a, assigned)) fun (a, assigned) ⟨(fldIdx, arg), argp⟩ => do
      let fld ← .lookupSymbol fldIdx
      let some idx := m[fld]?
        | throw s!"Unknown field {fld} ({fldIdx.value}): {m.map.keys}"
      if assigned[idx] then
        throw s!"Field {fld} already assigned."
      let assigned := assigned.set idx true
      have szp : sizeOf arg < sizeOf (fldIdx, arg) := by decreasing_tactic
      have szq : sizeOf (fldIdx, arg) < sizeOf args := Array.sizeOf_lt_of_mem argp
      let a := a.set idx arg
      pure (a, assigned)
    pure a

def asFieldStruct {size} (v : Ion SymbolId) (m : StructArgMap size) : FromIonM (Vector (Ion SymbolId) size) := do
  let ⟨args, _⟩ ← asStruct v
  mapFields args m

def deserializeValue {α} (bs : ByteArray) (act : Ion SymbolId → FromIonM α) : Except String α := do
  let a ←
    match Ion.deserialize bs with
    | .error (off, msg) =>
      throw s!"Error reading Ion: {msg} (offset = {off})"
    | .ok a => pure a
  let .isTrue p := inferInstanceAs (Decidable (a.size = 1))
    | throw s!"Expected single Ion value."
  let entries := a[0]
  let .isTrue p := inferInstanceAs (Decidable (entries.size = 2))
    | throw s!"Expected symbol table and value in dialect."
  let symbols ←
        match SymbolTable.ofLocalSymbolTable entries[0] with
        | .error (p, msg) => throw s!"Error at {p}: {msg}"
        | .ok symbols => pure symbols
  let ionv : Ion SymbolId := entries[1]!
  match act ionv { symbols := symbols }with
  | .error msg =>
    throw s!"Error decoding {msg}"
  | .ok res =>
    pure res


end FromIonM

class FromIon (α : Type) where
  fromIon : Ion SymbolId → FromIonM α

export Strata.FromIon (fromIon)

namespace FromIon

def deserialize {α} [FromIon α] (bs : ByteArray) : Except String α :=
  FromIonM.deserializeValue bs FromIon.fromIon

end FromIon

instance : FromIon String where
  fromIon := .asString

instance : FromIon Nat where
  fromIon := .asNat

instance [FromIon α] : FromIon (Array α) where
  fromIon v := .asArray v >>= Array.mapM fromIon

namespace QualifiedIdent

protected def toIon (d : QualifiedIdent) : Ion.InternM (Ion SymbolId) := do
  .symbol <$> internSymbol d.fullName

def fromIonStringSymbol (fullname : String) : FromIonM QualifiedIdent := do
  let pos := fullname.find (·='.')
  if pos < fullname.endPos then
    let dialect := fullname.extract 0 pos
    -- . is one byte
    let name := fullname.extract (pos + '.') fullname.endPos
    return { dialect,  name }
  else
    throw s!"Invalid symbol {fullname}"

def fromIonSymbol (sym : SymbolId) : FromIonM QualifiedIdent := do
  fromIonStringSymbol (← .lookupSymbol sym)

instance : FromIon QualifiedIdent where
  fromIon v := fromIonStringSymbol =<< .asSymbolString v

end QualifiedIdent

private def _root_.Ion.Ion.addArgs {α} (f : Ion α) (ra : Array (Ion α)) : Ion α :=
  if ra.isEmpty then
    f
  else
    .sexp (ra |>.push f |>.reverse)

namespace SyntaxCat

def toIon : SyntaxCat → Array (Ion SymbolId) → Ion.InternM (Ion SymbolId)
| (.atom sym), a =>
  return (← sym.toIon) |>.addArgs a
| .app f x, a => do
  f.toIon <| a.push <| ←x.toIon #[]

instance : CachedToIon SyntaxCat where
  cachedToIon _ c := c.toIon #[]

protected def fromIon (v : Ion SymbolId) : FromIonM SyntaxCat := do
  match ← .asSymbolOrSexp v with
  | .string s =>
    .atom <$> QualifiedIdent.fromIonStringSymbol s
  | .sexp args p => do
    let args ← args.attach.mapM fun ⟨u, _⟩ =>
      have r : sizeOf u < sizeOf args := by decreasing_tactic
      SyntaxCat.fromIon u
    if p : args.size = 0 then
      throw s!"Expected arguments to sexp"
    else do
      return args.foldl (start := 1) .app (init := args[0])
  termination_by v

instance : FromIon SyntaxCat where
  fromIon := SyntaxCat.fromIon

end SyntaxCat

namespace TypeExpr

def flattenArrow : Array TypeExpr → TypeExpr → Array TypeExpr
| a, .arrow l r => flattenArrow (a.push l) r
| a, r => a.push r

theorem flattenArrow_size (args : Array TypeExpr) (r : TypeExpr) :
  sizeOf (flattenArrow args r) = 1 + sizeOf args + sizeOf r := by
  unfold flattenArrow
  split
  case h_1 =>
    rename_i l r
    simp [flattenArrow_size _ r]
    omega
  case h_2 =>
    decreasing_tactic
  termination_by r

protected def toIon (refs : SymbolIdCache) (tpe : TypeExpr) : InternM (Ion SymbolId) :=
  ionScope! TypeExpr refs :
    match p : tpe with
    | .ident name a => do
      let v ← name.toIon
      if a.isEmpty then
        pure v
      else
        Ion.sexp <$> a.attach.mapM_off (init := #[v]) fun ⟨e, ep⟩ =>
          e.toIon refs
    -- A bound type variable with the given index.
    | .bvar vidx =>
      return Ion.sexp #[ionSymbol! "bvar", .int vidx]
    | .fvar idx a => do
      let s : Array (Ion SymbolId) := #[ionSymbol! "fvar", .int idx]
      let s ← a.attach.mapM_off (init := s) fun ⟨e, _⟩ =>
        e.toIon refs
      return Ion.sexp s
    | .arrow l r => do
      let fv := flattenArrow #[] r
      let res : Array (Ion SymbolId) := Array.mkEmpty (2 + fv.size)
      let res := res.push (.symbol ionSymbol! "arrow")
      let res := res.push (← l.toIon refs)
      have fvp := flattenArrow_size #[] r
      let res ← fv.attach.mapM_off (init := res) fun ⟨v, vp⟩ =>
        have q := Array.sizeOf_lt_of_mem_strict vp
        have : sizeOf fv ≤ sizeOf l + sizeOf r + 3 := by
          simp [fv, flattenArrow_size]
          omega
        v.toIon refs
      return Ion.sexp res
  termination_by tpe
  decreasing_by
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · simp; omega

instance : CachedToIon TypeExpr where
  cachedToIon refs tp := tp.toIon refs

def fromIon (v : Ion SymbolId) : FromIonM TypeExpr := do
  match ← .asSymbolOrSexp v with
  | .string s =>
    return .ident (← QualifiedIdent.fromIonStringSymbol s) #[]
  | .sexp args ap => do
    if p : args.size = 0 then
      throw s!"Expected arguments to sexp"
    else
      match ← .asSymbolString args[0] with
      | "arrow" => do
        if p : args.size < 3 then
          throw s!"arrow expects at least three arguments."
        else
          have r : sizeOf args[args.size - 1] < sizeOf args := by decreasing_tactic
          let init ← TypeExpr.fromIon args[args.size - 1]
          args.attach.foldrM (start := 1) (stop := args.size - 1) (init := init) fun ⟨v, _⟩ r =>
            have _ : sizeOf v < sizeOf args := by decreasing_tactic
            (.arrow · r) <$> TypeExpr.fromIon v
      | "bvar" =>
        if p : args.size ≠ 2 then
          throw s!"bvar exprects two arguments."
        else
          .bvar <$> .asNat args[1]
      | "fvar" =>
        if p : args.size < 2 then
          throw s!"fvar exprects two arguments."
        else
          let idx ← .asNat args[1]
          let a ← args.attach.mapM_off (start := 2) fun ⟨e, _⟩ =>
            have p : sizeOf e < sizeOf args := by decreasing_tactic
            TypeExpr.fromIon e
          pure <| .fvar idx a
      | sym => do
        let a ← args.attach.mapM_off (start := 1) fun ⟨v, _⟩ =>
          have _ : sizeOf v < sizeOf args := by decreasing_tactic
          TypeExpr.fromIon v
        pure <| .ident (← QualifiedIdent.fromIonStringSymbol sym) a
  termination_by v

instance : FromIon TypeExpr where
  fromIon := TypeExpr.fromIon

end TypeExpr

namespace MetadataArg

protected def toIon (refs : SymbolIdCache) (a : MetadataArg) : InternM (Ion SymbolId) :=
  ionScope! MetadataArg refs :
    match a with
    | .bool b =>
      return .sexp #[ionSymbol! "bool", .bool b]
    | .catbvar idx =>
      return .sexp #[ionSymbol! "category", .int idx]
    | .num v =>
      return .sexp #[ionSymbol! "num", .int v]
    | .option ma =>
      match ma with
      | some a => return .sexp #[ionSymbol! "some", ← a.toIon refs]
      | none => return .sexp #[ionSymbol! "none"]

instance : CachedToIon MetadataArg where
  cachedToIon := MetadataArg.toIon

protected def fromIon (v : Ion SymbolId) : FromIonM MetadataArg := do
  let ⟨args, argp⟩ ← .asSexp v
  match ← .asSymbolString args[0] with
  | "category" =>
    let ⟨p⟩ ← .checkArgCount "category" args 2
    .catbvar <$> .asNat args[1]
  | "num" =>
    let ⟨p⟩ ← .checkArgCount "num" args 2
    .num <$> .asNat args[1]
  | "some" => do
    let ⟨p⟩ ← .checkArgCount "some" args 2
    have _ : sizeOf args[1] < sizeOf args := by decreasing_tactic
    (.option ∘ some) <$> MetadataArg.fromIon args[1]
  | "none" => return .option none
  | s => throw s!"Unexepected arg {s}"

instance : FromIon MetadataArg where
  fromIon := MetadataArg.fromIon

end MetadataArg

namespace MetadataAttr

instance : CachedToIon MetadataAttr where
  cachedToIon refs md := ionScope! MetadataAttr refs : do
    let args : Array (Ion SymbolId) := .mkEmpty (1 + md.args.size)
    let args := args.push (←md.ident.toIon)
    let args ← md.args.mapM_off (init := args) fun a => ionRef! a
    return .sexp args

instance : FromIon MetadataAttr where
  fromIon v := do
    let ⟨args, argsp⟩ ← .asSexp v
    return {
      ident := ← fromIon args[0],
      args := ← args.mapM_off (start := 1) fromIon
    }

end MetadataAttr

namespace Metadata

instance : CachedToIon Metadata where
  cachedToIon refs md := ionScope! Metadata refs : ionRef! md.toArray

instance : FromIon Metadata where
  fromIon v := .ofArray <$> fromIon v

end Metadata

namespace PreType

def flattenArrow : Array PreType → PreType → Array PreType
| a, .arrow l r => PreType.flattenArrow (a.push l) r
| a, r => a.push r

theorem flattenArrow_size (args : Array PreType) (r : PreType) :
  sizeOf (flattenArrow args r) = 1 + sizeOf args + sizeOf r := by
  unfold flattenArrow
  split
  case h_1 =>
    rename_i l r
    simp [flattenArrow_size _ r]
    omega
  case h_2 =>
    decreasing_tactic
  termination_by r

protected def toIon (refs : SymbolIdCache) (tpe : PreType) : InternM (Ion SymbolId) :=
  ionScope! PreType refs :
    match tpe with
    | .ident name a => do
      let v ← name.toIon
      if a.isEmpty then
        pure v
      else
        .sexp <$> a.attach.mapM_off (init := #[v]) fun ⟨e, _⟩ =>
          e.toIon refs
    -- A bound type variable with the given index.
    | .bvar vidx =>
      return Ion.sexp #[ionSymbol! "bvar", .int vidx] |>.addArgs #[]
    | .fvar idx a => do
      let s : Array (Ion SymbolId) := #[ionSymbol! "fvar", .int idx]
      let s ← a.attach.mapM_off (init := s) fun ⟨e, ep⟩ => e.toIon refs
      return Ion.sexp s
    | .arrow l r => do
      let fv := r.flattenArrow #[]
      let res : Array (Ion SymbolId) := Array.mkEmpty (2 + fv.size)
      let res := res.push (.symbol ionSymbol! "arrow")
      let res := res.push (← l.toIon refs)
      have fvp := flattenArrow_size #[] r
      let res ← fv.attach.mapM_off (init := res) fun ⟨v, vp⟩ =>
        have q := Array.sizeOf_lt_of_mem_strict vp
        have : sizeOf fv ≤ sizeOf l + sizeOf r + 3 := by
          simp [fv, flattenArrow_size]
          omega
        v.toIon refs
      return Ion.sexp res
    | .funMacro i r =>
      return Ion.sexp <| #[.symbol ionSymbol! "funMacro", .int i, ← r.toIon refs]
  termination_by tpe
  decreasing_by
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · simp; omega
    · decreasing_tactic

instance : CachedToIon PreType where
  cachedToIon refs tp := tp.toIon refs

def fromIon (v : Ion SymbolId) : FromIonM PreType := do
  match ← .asSymbolOrSexp v with
  | .string s =>
    return .ident (← QualifiedIdent.fromIonStringSymbol s) #[]
  | .sexp args ap => do
    if args_ne : args.size = 0 then
      throw s!"Expected arguments to sexp"
    else
      match ← .asSymbolString args[0] with
      | "arrow" => do
        if p : args.size < 3 then
          throw s!"arrow expects at least three arguments."
        else
          let init ← PreType.fromIon args[args.size - 1]
          args.attach.foldrM (start := 1) (stop := args.size - 1) (init := init) fun ⟨e, emem⟩ r =>
            (.arrow · r) <$> PreType.fromIon e
      | "bvar" =>
        if p : args.size ≠ 2 then
          throw s!"bvar exprects two arguments."
        else
          .bvar <$> .asNat args[1]
      | "fvar" =>
        if p : args.size < 2 then
          throw s!"fvar exprects two arguments."
        else
          let idx ← .asNat args[1]
          let a ← args.attach.mapM_off (start := 2) fun ⟨e, _⟩ =>
            PreType.fromIon e
          pure <| .fvar idx a
      | sym => do
        let a ← args.attach.mapM_off (start := 1) fun ⟨v, _⟩ =>
          PreType.fromIon v
        pure <| .ident (← QualifiedIdent.fromIonStringSymbol sym) a
  termination_by v
  decreasing_by
    · have _ : sizeOf args[args.size - 1] < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have _ : sizeOf e < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have _ : sizeOf e < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have _ : sizeOf v < sizeOf args := by decreasing_tactic
      decreasing_tactic

instance : FromIon PreType where
  fromIon := PreType.fromIon

end PreType

namespace DeclBindingKind

instance : CachedToIon DeclBindingKind where
  cachedToIon refs tpc := ionScope! DeclBindingKind refs :
  match tpc with
  | .cat k =>
    return .sexp #[ionSymbol! "category", ← CachedToIon.cachedToIon refs k]
  | .expr tp =>
    return .sexp #[ionSymbol! "expr", ← ionRef! tp]

protected def fromIon (v : Ion SymbolId) : FromIonM DeclBindingKind := do
  let ⟨args, argsp⟩ ← .asSexp v
  match ← .asSymbolString args[0] with
  | "category" => do
    let ⟨p⟩ ← .checkArgCount "category" args 2
    .cat <$> fromIon args[1]
  | "expr" => do
    let ⟨p⟩ ← .checkArgCount "expr" args 2
    .expr <$> fromIon args[1]
  | s =>
    throw s!"Unexpected binding kind {s}"

instance : FromIon DeclBindingKind where
  fromIon := DeclBindingKind.fromIon

end DeclBindingKind

namespace DeclBinding

instance : CachedToIon DeclBinding where
  cachedToIon refs b := ionScope! DeclBinding refs :
    return .struct #[
      (ionSymbol! "name", .string b.ident),
      (ionSymbol! "type", ←ionRef! b.kind),
      (ionSymbol! "metadata", ←ionRef! b.metadata)
    ]

instance : FromIon DeclBinding where
  fromIon v := do
    let ⟨args, p⟩ ← .asFieldStruct (size := 3) v (.fromList! ["name", "type", "metadata"])
    pure {
        ident := ← fromIon args[0],
        kind := ← fromIon args[1],
        metadata := ← fromIon args[2],
    }

end DeclBinding

namespace SyntaxDefAtom

protected def toIon (refs : SymbolIdCache) (a : SyntaxDefAtom) : InternM (Ion SymbolId) :=
  ionScope! SyntaxDefAtom refs :
    match a with
    | .ident idx prec =>
      return .sexp #[ .symbol ionSymbol! "ident", .int idx, .int prec ]
    | .str v =>
      return .sexp #[ .symbol ionSymbol! "str", .string v ]
    | .indent n args =>
      return .sexp <| #[.symbol ionSymbol! "indent", .int n]
          ++ (← args.attach.mapM (fun ⟨a, _⟩  => a.toIon refs))

instance : CachedToIon SyntaxDefAtom where
  cachedToIon := SyntaxDefAtom.toIon

protected def fromIon (v : Ion SymbolId) : FromIonM SyntaxDefAtom := do
  let ⟨args, argsp⟩ ← .asSexp v
  match ← .asSymbolString args[0] with
  | "ident" => do
    let ⟨p⟩ ← .checkArgCount "ident" args 3
    .ident <$> fromIon args[1] <*> fromIon args[2]
  | "str" => do
    let ⟨p⟩ ← .checkArgCount "expr" args 2
    .str <$> fromIon args[1]
  | "indent" => do
    .indent <$> fromIon args[1]!
            <*> args.attach.mapM_off (start := 2) fun ⟨u, _⟩ =>
                  have p : sizeOf u < sizeOf args := by decreasing_tactic
                  SyntaxDefAtom.fromIon u
  | s =>
    throw s!"Unexpected binding kind {s}"

instance : FromIon SyntaxDefAtom where
  fromIon := SyntaxDefAtom.fromIon

end SyntaxDefAtom

namespace SyntaxDef

instance : CachedToIon SyntaxDef where
  cachedToIon refs d := ionScope! SyntaxDef refs :
    return .struct #[
      (ionSymbol! "atoms", .list (←d.atoms.mapM (fun (a : SyntaxDefAtom) => ionRef! a))),
      (ionSymbol! "prec", .int d.prec)
    ]

instance : FromIon SyntaxDef where
  fromIon v := do
    let ⟨args, p⟩ ← .asFieldStruct (size := 2) v (.fromList! ["atoms", "prec"])
    pure {
        atoms := ← fromIon args[0],
        prec := ← fromIon args[1],
    }

end SyntaxDef

namespace MetadataArgType

protected def toIon (refs : SymbolIdCache) (tp : MetadataArgType) : Ion SymbolId :=
  ionScope! MetadataArgType refs :
    match tp with
    | .bool => ionSymbol! "bool"
    | .num => ionSymbol! "num"
    | .ident => ionSymbol! "ident"
    | .opt tp => .sexp #[ ionSymbol! "opt", tp.toIon refs]

instance : CachedToIon MetadataArgType where
  cachedToIon refs tp := return tp.toIon refs

protected def fromIon (v : Ion SymbolId) : FromIonM MetadataArgType := do
  match ← .asSymbolOrSexp v with
  | .string s =>
    match s with
    | "bool" => pure .bool
    | "num" => pure .num
    | "ident" => pure .ident
    | _ => throw s!"Unknown type {s}"
  | .sexp args ap => do
    let .isTrue p := inferInstanceAs (Decidable (args.size ≥ 2))
      | throw s!"Expected arguments to sexp"
    match ← .asSymbolString args[0] with
    | "opt" =>
      have p : sizeOf args[1] < sizeOf args := by decreasing_tactic
      .opt <$> MetadataArgType.fromIon args[1]
    | s => throw s!"Unknown sexp arg {s}"
  termination_by v

instance : FromIon MetadataArgType where
  fromIon := MetadataArgType.fromIon

end MetadataArgType

namespace MetadataArgDecl

instance : CachedToIon MetadataArgDecl where
  cachedToIon refs d := ionScope! MetadataArgDecl refs :
    return .sexp #[.string d.ident, ← ionRef! d.type ]

instance : FromIon MetadataArgDecl where
  fromIon v := do
    let ⟨args, argsp⟩ ← .asSexp v
    let ⟨p⟩ ← .checkArgCount "category" args 2
    pure { ident := ← fromIon args[0], type := ← fromIon args[1] }

end MetadataArgDecl

namespace SynCatDecl

instance  : CachedToIon SynCatDecl where
  cachedToIon refs d := ionScope! SynCatDecl refs :
    return .struct #[
      (ionSymbol! "type", ionSymbol! "syncat"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "arguments", .list (.string <$> d.argNames))
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM SynCatDecl := do
  let args ← .mapFields fields (.fromList! ["type", "name", "arguments"])
  pure {
    name := ← fromIon args[1],
    argNames := ← fromIon args[2],
  }

end SynCatDecl

namespace OpDecl

instance : CachedToIon OpDecl where
  cachedToIon refs d := ionScope! OpDecl refs :
    return .struct #[
      (ionSymbol! "type", ionSymbol! "op"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "bindings", ← CachedToIon.cachedToIon (ionRefEntry! d.argDecls[0]!) d.argDecls),
      (ionSymbol! "category", ← d.category.toIon),
      (ionSymbol! "syntax",   ← ionRef! d.syntaxDef),
      (ionSymbol! "metadata", ← ionRef! d.metadata)
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM OpDecl := do
  let m := .fromList! ["type", "name", "bindings", "category", "syntax", "metadata"]
  let args ← .mapFields fields m
  pure {
    name := ← fromIon args[1]
    argDecls := ← fromIon args[2]
    category := ← fromIon args[3]
    syntaxDef := ← fromIon args[4]
    metadata := ← fromIon args[5]
  }

end OpDecl

namespace TypeDecl

instance : CachedToIon TypeDecl where
  cachedToIon refs d := ionScope! TypeDecl refs :
    return .struct #[
      (ionSymbol! "type", ionSymbol! "type"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "argNames", .list (d.argNames |>.map .string))
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM TypeDecl := do
  let m := .fromList! ["type", "name", "argNames"]
  let args ← .mapFields fields m
  pure {
    name := ← fromIon args[1]
    argNames := ← fromIon args[2]
  }

end TypeDecl

namespace FunctionDecl

instance : CachedToIon FunctionDecl where
  cachedToIon refs d := ionScope! FunctionDecl refs :
    return .struct #[
      (ionSymbol! "type", ionSymbol! "fn"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "bindings", ← CachedToIon.cachedToIon (ionRefEntry! d.argDecls[0]!) d.argDecls),
      (ionSymbol! "result", ← ionRef! d.result),
      (ionSymbol! "schema", ← ionRef! d.syntaxDef),
      (ionSymbol! "metadata", ← ionRef! d.metadata)
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM FunctionDecl := do
  let m := .fromList! ["type", "name", "bindings", "result", "schema", "metadata"]
  let args ← .mapFields fields m
  pure {
    name := ← fromIon args[1]
    argDecls := ← fromIon args[2]
    result := ← fromIon args[3]
    syntaxDef := ← fromIon args[4]
    metadata := ← fromIon args[5]
  }

end FunctionDecl

namespace MetadataDecl

instance : CachedToIon MetadataDecl where
  cachedToIon refs d := ionScope! MetadataDecl refs :
    return .struct #[
      (ionSymbol! "type", ionSymbol! "metadata"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "args", ← ionRef! d.args)
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM MetadataDecl := do
  let m := .fromList! ["type", "name", "args"]
  let args ← .mapFields fields m
  pure {
    name := ← fromIon args[1]
    args := ← fromIon args[2]
  }

end MetadataDecl

namespace Decl

instance : CachedToIon Decl where
  cachedToIon refs d := ionScope! Decl refs :
  match d with
  | .syncat d   => ionRef! d
  | .op d       => ionRef! d
  | .type d     => ionRef! d
  | .function d => ionRef! d
  | .metadata d => ionRef! d

def fromIonFields (typeVal : String) (fields : Array (SymbolId × Ion SymbolId)) : FromIonM Decl := do
  match typeVal with
  | "syncat" => .syncat <$> SynCatDecl.fromIon fields
  | "op" => .op <$> OpDecl.fromIon fields
  | "type" => .type <$> TypeDecl.fromIon fields
  | "fn" => .function <$> FunctionDecl.fromIon fields
  | "metadata" => .metadata <$> MetadataDecl.fromIon fields
  | typeVal => throw s!"Unknown type {typeVal}"


def fromIon (typeId : SymbolId) (v : Ion SymbolId) : FromIonM Decl := do
  let fields ← .asStruct0 v
  let some (_, val) := fields.find? (·.fst == typeId)
    | throw "Could not find type"
  fromIonFields (← .asSymbolString val) fields

end Decl

private inductive Header
| dialect : DialectName → Header
| program : DialectName → Header

def Header.fromIon (v : Ion SymbolId) : FromIonM Header := do
  let ⟨hdr, _⟩ ← .asSexp v
  let .isTrue ne := inferInstanceAs (Decidable (hdr.size ≥ 2))
    | throw s!"Expected header to have two elements."
  match ← .asSymbolString hdr[0] with
  | "dialect" => .dialect <$> .asString hdr[1]
  | "program" => .program <$> .asString hdr[1]
  | op => throw s!"Expected 'program' or 'dialect' instead of {op}."

namespace Dialect

instance : CachedToIon Dialect where
  cachedToIon refs d := ionScope! Dialect refs : do
    let c := ionSymbol! "dialect"
    let hdr := .sexp #[ c, .string d.name ]
    let mut a : Array (Ion SymbolId) := #[ hdr ]
    for i in d.imports do
      a := a.push <| .struct #[(ionSymbol! "type", ionSymbol! "import"),
                               (ionSymbol! "name", .string i)]
    for decl in d.declarations do
      a := a.push <| (← ionRef! decl)
    return .list a

def fromIonDecls (dialect : DialectName) (args : Array (Ion SymbolId)) (start : Nat := 0) : FromIonM Dialect := do
  let tbl ← .readSymbolTable
  let typeId := tbl.symbolId! "type"
  let nameId := tbl.symbolId! "name"
  let (imports, decls) ← args.foldlM (init := (#[], #[])) (start := start) fun (imports, decls) v => do
    let fields ← .asStruct0 v
    let some (_, val) := fields.find? (·.fst == typeId)
      | throw "Could not find type"
    match ← .asSymbolString val with
    | "import" =>
      let some (_, val) := fields.find? (·.fst == nameId)
        | throw "Could not find import"
      let i ← .asString val
      pure (imports.push i, decls)
    | name =>
      let decl ← Decl.fromIonFields name fields
      pure (imports, decls.push decl)
  return {
    name := dialect
    imports := imports
    declarations :=  decls
  }

instance : FromIon Dialect where
  fromIon v := do
    let ⟨args, _⟩ ← .asList v
    let .isTrue ne := inferInstanceAs (Decidable (args.size ≥ 1))
      | throw s!"Expected header"
    match ← Header.fromIon args[0] with
    | .dialect dialect =>
      fromIonDecls dialect args (start := 1)
    | .program _ =>
      throw s!"Expected dialect"

#declareIonSymbolTable Dialect

end Dialect

mutual

protected def Operation.toIonAux (refs : SymbolIdCache) (op : Operation) : InternM (Ion SymbolId) :=
  ionScope! Operation refs : do
    let argEntry := ionRefEntry! (default : Arg)
    let args ← op.args.attach.mapM fun ⟨a, _⟩ => a.toIon argEntry
    return .sexp <| Array.append #[ ← op.name.toIon ] args

protected def Expr.toIon (refs : SymbolIdCache) (e : Expr) (revArgs : Array (Ion SymbolId)) : InternM (Ion SymbolId) :=
  ionScope! Expr refs :
    match e with
    | .bvar idx => do
      return Ion.sexp #[ ionSymbol! "bvar", .int idx ] |>.addArgs revArgs
    | .fvar idx =>
      return Ion.sexp #[ ionSymbol! "fvar", .int idx ] |>.addArgs revArgs
    | .fn ident =>
      return (← ident.toIon) |>.addArgs revArgs
    | .app f a => do
      let av ← a.toIon (ionRefEntry! a)
      f.toIon refs (revArgs.push av)

protected def Arg.toIon (refs : SymbolIdCache) (arg : Arg) : InternM (Ion SymbolId) :=
  ionScope! Arg refs :
    match arg with
    | .op o     => return .sexp #[ ionSymbol! "op", ← o.toIonAux (ionRefEntry! o) ]
    | .expr e   => return .sexp #[ ionSymbol! "expr", ← e.toIon (ionRefEntry! e) #[] ]
    | .cat c    => return .sexp #[ ionSymbol! "cat", ← ionRef! c ]
    | .type e   => return .sexp #[ ionSymbol! "type", ← ionRef! e ]
    | .ident s  => return .sexp #[ ionSymbol! "ident", ← internSymbol s ]
    | .num n    => return .sexp #[ ionSymbol! "num", .int n ]
    | .decimal d => return .sexp #[ ionSymbol! "decimal", .decimal d]
    | .strlit s => return .sexp #[ ionSymbol! "strlit", .string s]
    | .option o =>
      match o with
      | none => return .sexp #[ ionSymbol! "option" ]
      | some a => return .sexp #[ ionSymbol! "option", ← a.toIon refs ]
    | .seq l => do
      let lv ← l.attach.mapM fun ⟨v, _⟩ => v.toIon refs
      return .sexp <| Array.append #[ ionSymbol! "seq" ] lv
    | .commaSepList l => do
      let lv ← l.attach.mapM fun ⟨v, _⟩ => v.toIon refs
      return .sexp <| Array.append #[ ionSymbol! "commaSepList" ] lv

end

mutual

protected def Operation.fromIon (v : Ion SymbolId) : FromIonM Operation := do
  -- FIXME.  Make sure each command is well-formed with respect to the dialect map.
  let ⟨sexp, sexpP⟩ ← .asSexp v
  let name ← fromIon sexp[0]
  let args ← sexp.attach.mapM_off (start := 1) fun ⟨a, _⟩ =>
    have _ : sizeOf a < sizeOf sexp := by decreasing_tactic
    Strata.Arg.fromIon a
  return { name := name, args := args }
termination_by v

protected def Expr.fromIon (v : Ion SymbolId) : FromIonM Expr := do
  let ⟨sexp, sexpP⟩ ← .asSexp v
  match ← .asSymbolString sexp[0] with
  | "bvar" =>
    let ⟨p⟩ ← .checkArgCount "bvar" sexp 2
    .bvar <$> fromIon sexp[1]
  | "fvar" =>
    let ⟨p⟩ ← .checkArgCount "fvar" sexp 2
    .fvar <$> fromIon sexp[1]
  | s => do
    let ident ← QualifiedIdent.fromIonStringSymbol s
    sexp.attach.foldlM (start := 1) (init := Expr.fn ident) fun f ⟨a, p⟩ =>
      have _ : sizeOf a < sizeOf sexp := by decreasing_tactic
      .app f <$> Strata.Arg.fromIon a
  termination_by v

protected def Arg.fromIon (v : Ion SymbolId) : FromIonM Arg := do
  let ⟨sexp, sexpP⟩ ← .asSexp v
  match ← .asSymbolString sexp[0] with
  | "op" =>
    let ⟨p⟩ ← .checkArgCount "op" sexp 2
    have _ : sizeOf sexp[1] < sizeOf sexp := by decreasing_tactic
    .op <$> Strata.Operation.fromIon sexp[1]
  | "expr" =>
    let ⟨p⟩ ← .checkArgCount "expr" sexp 2
    have _ : sizeOf sexp[1] < sizeOf sexp := by decreasing_tactic
    .expr <$> Strata.Expr.fromIon sexp[1]
  | "cat" =>
    let ⟨p⟩ ← .checkArgCount "cat" sexp 2
    .cat <$> fromIon sexp[1]
  | "type" =>
    let ⟨p⟩ ← .checkArgCount "type" sexp 2
    .type <$> fromIon sexp[1]
  | "ident" =>
    let ⟨p⟩ ← .checkArgCount "ident" sexp 2
    .ident <$> fromIon sexp[1]
  | "intlit" =>
    let ⟨p⟩ ← .checkArgCount "intlit" sexp 2
    .num <$> fromIon sexp[1]
  | "strlit" =>
    let ⟨p⟩ ← .checkArgCount "strlit" sexp 2
    .strlit <$> fromIon sexp[1]
  | "option" =>
    match p : sexp.size with
    | 1 => return .option none
    | 2 =>
      have _ : sizeOf sexp[1] < sizeOf sexp := by decreasing_tactic
      .option <$> Strata.Arg.fromIon sexp[1]
    | _ => throw "Option expects at most one argument."
  | "seq" => do
    .seq <$> sexp.attach.mapM_off (start := 1) fun ⟨u, _⟩ =>
      have _ : sizeOf u < sizeOf sexp := by decreasing_tactic
      Strata.Arg.fromIon u
  | "commaSepList" => do
    .commaSepList <$> sexp.attach.mapM_off (start := 1) fun ⟨u, _⟩ =>
      have _ : sizeOf u < sizeOf sexp := by decreasing_tactic
      Strata.Arg.fromIon u
  | str =>
    throw s!"Unexpected identifier {str}"
  termination_by v

end

namespace Operation

instance : CachedToIon Operation where
  cachedToIon := Operation.toIonAux

end Operation

#declareIonSymbolTable Operation

namespace Program

instance : CachedToIon Program where
  cachedToIon refs pgm :=
    ionScope! Program refs : do
      let hdr := Ion.sexp #[ ionSymbol! "program", .string pgm.dialect ]
      let l ← pgm.commands.mapM_off (init := #[hdr]) fun cmd => ionRef! cmd
      return .list l

#declareIonSymbolTable Program

def fromIonDecls (dialects : DialectMap) (dialect : DialectName) (args : Array (Ion SymbolId)) (start : Nat := 0) : FromIonM Program := do
  let commands ← args.foldlM (init := #[]) (start := start) fun cmds u => do
    cmds.push <$> Operation.fromIon u
  return {
    dialects := dialects.importedDialects! dialect
    dialect := dialect
    commands := commands
  }

protected def fromIon (dialects : DialectMap) (v : Ion SymbolId) : FromIonM Program := do
  let ⟨args, _⟩ ← .asList v
  let .isTrue ne := inferInstanceAs (Decidable (args.size ≥ 1))
    | throw s!"Expected header"
  match ← Header.fromIon args[0] with
  | .program dialect =>
    fromIonDecls dialects dialect args (start := 1)
  | .dialect _ =>
    throw s!"Expected program"

end Program
