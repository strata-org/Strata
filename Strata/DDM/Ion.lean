/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.AST
import Strata.DDM.Util.Ion.Lean

namespace Ion.Ion

/--
The maximum exponent allowed when converting from a decimal to a
`Nat` or `Int`.

This is added purely for security purposes to prevent a very large
exponent in an untrusted Ion file from generating a number that
consumes available memory.
-/
private def maxDecimalExponent : Nat := 1000

protected def asNat? (v : Ion SymbolId) : Option Nat :=
  match v.app with
  | .int x =>
    if x < 0 then
      none
    else
      some x.toNat
  | .decimal d =>
    if d.mantissa ≥ 0 ∧ d.exponent ≥ 0 ∧ d.exponent ≤ maxDecimalExponent then
      some <| d.mantissa.toNat * 10^d.exponent.toNat
    else
      none
  | .string s =>
    match s.toNat? with
    | some x => some x
    | none => none
  | _ => none

protected def asInt? (v : Ion SymbolId) : Option Int :=
  match v.app with
  | .int x => some x
  | .decimal d =>
    if d.exponent ≥ 0 ∧ d.exponent ≤ maxDecimalExponent then
      some <| d.mantissa * Int.ofNat (10^d.exponent.toNat)
    else
      none
  | .string s =>
    match s.toInt? with
    | some x => some x
    | none => none
  | _ => none

protected def asDecimal? (v : Ion SymbolId) : Option Decimal :=
  match v.app with
  | .int x => some (.ofInt x)
  | .decimal d => some d
  | _ => none

end Ion.Ion

namespace Strata

open _root_.Lean
open Elab Command

open _root_.Ion

inductive StringOrSexp (v : Ion SymbolId) where
| string (s : String)
| sexp (a : Array (Ion SymbolId)) (p : a.size > 0 ∧ sizeOf a < sizeOf v)

inductive Required where
| req
| opt
deriving DecidableEq

structure StructArgMap (size : Nat) where
  map : Std.HashMap String (Fin size) := {}
  required : Array (String × Fin size)
  deriving Inhabited

namespace StructArgMap

instance : Membership String (StructArgMap size) where
  mem m nm := nm ∈ m.map

instance : GetElem? (StructArgMap size) String (Fin size) (fun m nm => nm ∈ m) where
  getElem m nm p := m.map[nm]
  getElem! m nm := m.map[nm]!
  getElem? m nm := m.map[nm]?


def fromList! (as : List String) : StructArgMap as.length :=
  let size := as.length
  let m := { map := {}, required := #[] }
  as.foldl (init := m) fun m name =>
    if name ∈ m.map then
      panic! s!"Duplicate name {name}"
    else if p : m.map.size < size then
      let idx := ⟨m.map.size, p⟩
      { map := m.map.insert name idx
        required := m.required.push (name, idx)
      }
    else
      panic! "Invalid index"

def fromOptList! (as : List (String × Required)) : StructArgMap as.length :=
  let size := as.length
  let m := { map := {}, required := #[] }
  as.foldl (init := m) fun m (name, r) =>
    if name ∈ m.map then
      panic! s!"Duplicate name {name}"
    else if p : m.map.size < size then
      let idx := ⟨m.map.size, p⟩
      { map := m.map.insert name idx
        required :=
          match r with
          | .req => m.required.push (name, idx)
          | .opt => m.required
      }
    else
      panic! "Invalid index"

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

protected def asNat (name : String) (v : Ion SymbolId) : FromIonM Nat :=
  match v.asNat? with
  | some x => pure x
  | none => throw s!"Expected {name} to be a nat instead of {repr v}."

protected def asInt (v : Ion SymbolId) : FromIonM Int :=
  match v.asInt? with
  | some x => pure x
  | none => throw s!"Expected {repr v} to be an int."

protected def asString (name : String) (v : Ion SymbolId) : FromIonM String :=
  match v with
  | .string s => return s
  | _ => throw s!"{name} expected to be a string. {repr v}"

protected def asBytes (name : String) (v : Ion SymbolId) : FromIonM ByteArray :=
  match v with
  | .blob a => return a
  | .list a => ByteArray.ofNatArray <$> a.mapM (.asNat "name element")
  | _ => throw s!"{name} expected to be a string. {repr v}"

protected def asSymbolString (name : String) (v : Ion SymbolId) : FromIonM String :=
  match v.app with
  | .symbol sym => .lookupSymbol sym
  | .string name => pure name
  | _ => throw s!"{name} expected to be a symbol or string."

protected def asList (v : Ion SymbolId) : FromIonM { a : Array (Ion SymbolId) // sizeOf a < sizeOf v} :=
  match v with
  | .mk (.list args) =>
    return .mk args (by simp; omega)
  | _ => throw s!"Expected list"

protected def asSexp (name : String) (v : Ion SymbolId) : FromIonM ({ a : Array (Ion SymbolId) // a.size > 0 ∧ sizeOf a < sizeOf v}) :=
  match v with
  | .mk (.sexp args) | .mk (.list args) =>
    if p : args.size > 0 then
      pure <| .mk args ⟨p,  by decreasing_tactic⟩
    else
      throw s!"{name} expected non-empty expression"
  | _ => throw s!"{name} expected sexpression."

protected def asSymbolOrSexp (v : Ion SymbolId) : FromIonM (StringOrSexp v) :=
  match v with
  | .symbol s => .string <$> .lookupSymbol s
  | .string s => return .string s
  | .mk (.sexp args) | .mk (.list args) =>
    if p : args.size > 0 then
      return .sexp args ⟨p, (by decreasing_tactic)⟩
    else
      throw s!"Expected non-empty expression"
  | _ => throw s!"Expected symbol or sexpression."

def checkArgCount (name : String) (args : Array (Ion SymbolId)) (n : Nat) : FromIonM (PLift (args.size = n)) := do
    if p : args.size = n then
      pure ⟨p⟩
    else
      throw s!"{name} expects {n} arguments has {repr args}"

def checkArgMin (name : String) (args : Array (Ion SymbolId)) (n : Nat) : FromIonM (PLift (args.size ≥ n)) := do
    if p : args.size ≥ n then
      pure ⟨p⟩
    else
      throw s!"{name} expects at least {n} arguments"

/--
Interpret Ion value as an array and applies function to it.
-/
def asListOf {α} (name : String) (v : Ion SymbolId) (f : Ion SymbolId → FromIonM α) : FromIonM (Array α) :=
  match v with
  | .list a => a.mapM f
  | _ => throw s!"{name} expects a list."

def asStruct (type : String) (v : Ion SymbolId) : FromIonM { a : Array (SymbolId × Ion SymbolId) // sizeOf a < sizeOf v } := do
  match v with
  | .mk (.struct args) => pure ⟨args, by decreasing_tactic ⟩
  | v => throw s!"{type} expected a struct: {repr v}"

def asStruct0 (v : Ion SymbolId) : FromIonM (Array (SymbolId × Ion SymbolId)) := do
  match v with
  | .mk (.struct args) => pure args
  | _ => throw "Expected a struct0"

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
  if args.size > size then
    throw s!"Unexpected number of arguments to struct."
  else if p : size = 0 then
    return ⟨#[], p.symm⟩
  else
    let a := Vector.replicate size .null
    let assigned := Vector.replicate size false
    let (a, assigned) ← args.attach.foldlM (init := (a, assigned)) fun (a, assigned) ⟨(fldIdx, arg), argp⟩ => do
      let fld ← .lookupSymbol fldIdx
      let some idx := m[fld]?
        | throw s!"Unknown field {fld} ({fldIdx.value}): {m.map.keys}"
      if assigned[idx] then
        throw s!"Field {fld} already assigned."
      let assigned := assigned.set idx true
      let a := a.set idx arg
      pure (a, assigned)
    for (name, idx) in m.required do
      if !assigned[idx] then
        throw s!"Missing assignment to {name}."
    pure a

def asFieldStruct {size} (v : Ion SymbolId) (type : String) (m : StructArgMap size) : FromIonM (Vector (Ion SymbolId) size) := do
  let ⟨args, _⟩ ← asStruct type v
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
  match act ionv { symbols := symbols } with
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

namespace QualifiedIdent

protected def toIon (d : QualifiedIdent) : Ion.InternM (Ion SymbolId) := do
  .symbol <$> internSymbol d.fullName

def fromIonStringSymbol (fullname : String) : FromIonM QualifiedIdent := do
  let pos := fullname.find (·='.')
  if pos < fullname.endPos then
    let dialect := String.Pos.Raw.extract fullname 0 pos
    -- . is one byte
    let name := String.Pos.Raw.extract fullname (pos + '.') fullname.endPos
    return { dialect,  name }
  else
    throw s!"Invalid symbol {fullname}"

def fromIonSymbol (sym : SymbolId) : FromIonM QualifiedIdent := do
  fromIonStringSymbol (← .lookupSymbol sym)

protected def fromIon (name : String) (v : Ion SymbolId) : FromIonM QualifiedIdent :=
  fromIonStringSymbol =<< .asSymbolString name v

end QualifiedIdent

class ToIon (α : Type) where
  toIon : α → InternM (Ion SymbolId)

open ToIon (toIon)

namespace SyntaxCatF

protected def toIon {α} [ToIon α] (cat : SyntaxCatF α) : Ion.InternM (Ion SymbolId) := do
  let args := #[ ← toIon cat.ann, ← cat.name.toIon ]
  let args ← cat.args.attach.mapM_off (init := args) fun ⟨e, _⟩ => e.toIon
  return .sexp args
decreasing_by
  rw [SyntaxCatF.sizeOf_spec cat]
  decreasing_tactic

protected def fromIon {α} [FromIon α] (v : Ion SymbolId) : FromIonM (SyntaxCatF α) := do
  let ⟨args, _⟩ ← .asSexp "Category reference" v
  let ⟨p⟩ ← .checkArgMin "Category" args 2
  let ann ← fromIon args[0]
  let name ← QualifiedIdent.fromIon "Category name" args[1]
  let args ← args.attach.mapM_off (start := 2) fun ⟨e, _⟩ => SyntaxCatF.fromIon e
  return {
    ann := ann
    name := name
    args := args
  }
termination_by v
decreasing_by
  have p : sizeOf e < sizeOf args := by decreasing_tactic
  decreasing_tactic

instance {α} [FromIon α] : FromIon (SyntaxCatF α)  where
  fromIon := SyntaxCatF.fromIon

end SyntaxCatF

namespace TypeExprF

protected def toIon {α} [ToIon α] (refs : SymbolIdCache) (tpe : TypeExprF α) : InternM (Ion SymbolId) :=
  ionScope! TypeExprF refs :
    match tpe with
    | .ident ann name a => do
      let v ← name.toIon
      let args : Array (Ion SymbolId) := #[ionSymbol! "ident", ← toIon ann, v]
      Ion.sexp <$> a.attach.mapM_off (init := args) fun ⟨e, _⟩ =>
        e.toIon refs
    -- A bound type variable with the given index.
    | .bvar ann vidx =>
      return Ion.sexp #[ionSymbol! "bvar", ← toIon ann, .int vidx]
    | .fvar ann idx a => do
      let s : Array (Ion SymbolId) := #[ionSymbol! "fvar", ← toIon ann, .int idx]
      let s ← a.attach.mapM_off (init := s) fun ⟨e, _⟩ =>
        e.toIon refs
      return Ion.sexp s
    | .arrow ann l r => do
      return Ion.sexp #[
        .symbol ionSymbol! "arrow",
        ← toIon ann,
        ← l.toIon refs,
        ← r.toIon refs
      ]
  termination_by tpe

instance {α} [ToIon α] : CachedToIon (TypeExprF α) where
  cachedToIon refs tp := tp.toIon refs

protected def fromIon {α} [FromIon α] (v : Ion SymbolId) : FromIonM (TypeExprF α) := do
  let ⟨args, ap⟩ ← .asSexp "TypeExpr" v
  match ← .asSymbolString "TypeExpr kind" args[0] with
  | "arrow" => do
    let ⟨p⟩ ← .checkArgCount "Type expression arrow" args 4
    let ann ← fromIon args[1]
    let l ← TypeExprF.fromIon args[2]
    let r ← TypeExprF.fromIon args[3]
    return .arrow ann l r
  | "bvar" =>
    let ⟨p⟩ ← .checkArgCount "Type expression bvar" args 3
    return .bvar
      (← fromIon args[1])
      (← .asNat "Type expression bvar" args[2])
  | "fvar" =>
    let ⟨p⟩ ← .checkArgMin "Type expression free variable" args 3
    let ann ← fromIon args[1]
    let idx ← .asNat "Type expression free variable index" args[2]
    let a ← args.attach.mapM_off (start := 3) fun ⟨e, _⟩ =>
      TypeExprF.fromIon e
    pure <| .fvar ann idx a
  | "ident" =>
    let ⟨p⟩ ← .checkArgMin "TypeExpr identifier" args 3
    let ann ← fromIon args[1]
    let name ← QualifiedIdent.fromIon "Type identifier name" args[2]
    let args ← args.attach.mapM_off (start := 3) fun ⟨e, _⟩ =>
      TypeExprF.fromIon e
    return .ident ann name args
  | s => do
    throw s!"Unexpected type expression {s}"
termination_by v
decreasing_by
  · have p : sizeOf args[2] < sizeOf args := by decreasing_tactic
    decreasing_tactic
  · have p : sizeOf args[3] < sizeOf args := by decreasing_tactic
    decreasing_tactic
  · have p : sizeOf e < sizeOf args := by decreasing_tactic
    decreasing_tactic
  · have p : sizeOf e < sizeOf args := by decreasing_tactic
    decreasing_tactic

instance {α} [FromIon α] : FromIon (TypeExprF α) where
  fromIon := TypeExprF.fromIon

end TypeExprF
mutual

protected def OperationF.toIon {α} [ToIon α] (refs : SymbolIdCache) (op : OperationF α) : InternM (Ion SymbolId) :=
  ionScope! OperationF refs : do
    let argEntry := ionRefEntry! ``ArgF
    let args := #[ ← op.name.toIon, ← ToIon.toIon op.ann ]
    let args ← op.args.attach.mapM_off (init := args) fun ⟨a, _⟩ =>
      a.toIon argEntry
    return .sexp args
termination_by sizeOf op
decreasing_by
  · simp [Strata.OperationF.sizeOf_spec]
    decreasing_tactic

protected def ExprF.toIon {α} [ToIon α] (refs : SymbolIdCache) (e : ExprF α) : InternM (Ion SymbolId) :=
  ionScope! ExprF refs :
    match e with
    | .bvar ann idx => do
      return .sexp #[ ionSymbol! "bvar", ← toIon ann, .int idx ]
    | .fvar ann lvl => do
      return .sexp #[ ionSymbol! "fvar", ← toIon ann, .int lvl ]
    | .fn ann ident =>
      return .sexp #[ ionSymbol! "fn", ← toIon ann, ← ident.toIon ]
    | .app ann f a => do
      return .sexp #[ ionSymbol! "app", ← toIon ann, ← f.toIon refs, ← a.toIon (ionRefEntry! ``Arg) ]
  termination_by sizeOf e
  decreasing_by
    · decreasing_tactic
    · decreasing_tactic

protected def ArgF.toIon {α} [ToIon α] (refs : SymbolIdCache) (arg : ArgF α) : InternM (Ion SymbolId) :=
  ionScope! ArgF refs :
    match arg with
    | .op o =>
      return .sexp #[ ionSymbol! "op", ← o.toIon (ionRefEntry! ``OperationF) ]
    | .expr e =>
      return .sexp #[ ionSymbol! "expr", ← e.toIon (ionRefEntry! ``ExprF) ]
    | .cat c =>
      return .sexp #[ ionSymbol! "cat", ← c.toIon ]
    | .type e =>
      return .sexp #[ ionSymbol! "type", ← e.toIon (ionRefEntry! ``TypeExprF) ]
    | .ident ann s  =>
      return .sexp #[ ionSymbol! "ident", ← toIon ann, ← internSymbol s ]
    | .num ann n    =>
      return .sexp #[ ionSymbol! "num", ← toIon ann, .int n ]
    | .decimal ann d =>
      return .sexp #[ ionSymbol! "decimal", ← toIon ann, .decimal d]
    | .strlit ann s =>
      return .sexp #[ ionSymbol! "strlit", ← toIon ann, .string s]
    | .bytes ann a =>
      return .sexp #[ ionSymbol! "bytes", ← toIon ann, .blob a ]
    | .option ann o => do
      let mut args : Array (Ion _) := #[ ionSymbol! "option", ← toIon ann ]
      match o with
      | none => pure ()
      | some a =>
        args := args.push (← a.toIon refs )
      return .sexp args
    | .seq ann l => do
      let args : Array (Ion _) := #[ ionSymbol! "seq", ← toIon ann ]
      let args ← l.attach.mapM_off (init := args) fun ⟨v, _⟩ => v.toIon refs
      return .sexp args
    | .commaSepList ann l => do
      let args : Array (Ion _) := #[ ionSymbol! "commaSepList", ← toIon ann ]
      let args ← l.attach.mapM_off (init := args) fun ⟨v, _⟩ => v.toIon refs
      return .sexp args
  termination_by sizeOf arg
  decreasing_by
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic
    · decreasing_tactic

end

mutual

protected def OperationF.fromIon {α} [FromIon α] (v : Ion SymbolId) : FromIonM (OperationF α)  := do
  let ⟨sexp, sexpP⟩ ← .asSexp "Operation" v
  let ⟨m⟩ ← .checkArgMin "operation" sexp 2
  let name ← QualifiedIdent.fromIon "Operation name" sexp[0]
  let ann ← fromIon (α := α) sexp[1]
  let args ← sexp.attach.mapM_off (start := 2) fun ⟨a, a_in⟩ =>
    Strata.ArgF.fromIon a
  return { ann := ann, name := name, args := args }
termination_by v
decreasing_by
    have _ : sizeOf a < sizeOf sexp := by decreasing_tactic
    decreasing_tactic

protected def ExprF.fromIon {α} [FromIon α] (v : Ion SymbolId) : FromIonM (ExprF α) := do
  let ⟨sexp, sexpP⟩ ← .asSexp "Expr" v
  match ← .asSymbolString "Expr kind" sexp[0] with
  | "bvar" =>
    let ⟨p⟩ ← .checkArgCount "bvar" sexp 3
    let ann ← fromIon (α := α) sexp[1]
    .bvar ann <$> .asNat "Expr bvar" sexp[2]
  | "fvar" =>
    let ⟨p⟩ ← .checkArgCount "fvar" sexp 3
    let ann ← fromIon (α := α) sexp[1]
    .fvar ann <$> .asNat "Expr fvar" sexp[2]
  | "fn" =>
    let ⟨p⟩ ← .checkArgCount "fn" sexp 3
    let ann ← fromIon (α := α) sexp[1]
    let ident ← QualifiedIdent.fromIon "Expression function identifier" sexp[2]
    return .fn ann ident
  | "app" =>
    let ⟨p⟩ ← .checkArgCount "app" sexp 4
    let ann ← fromIon (α := α) sexp[1]
    let f ← Strata.ExprF.fromIon sexp[2]
    let x ← Strata.ArgF.fromIon sexp[3]
    return .app ann f x
  | str =>
    throw s!"Unexpected identifier {str}"
termination_by v
decreasing_by
  · have _ : sizeOf sexp[2] < sizeOf sexp := by decreasing_tactic
    decreasing_tactic
  · have _ : sizeOf sexp[3] < sizeOf sexp := by decreasing_tactic
    decreasing_tactic

protected def ArgF.fromIon {α} [FromIon α] (v : Ion SymbolId) : FromIonM (ArgF α)  := do
  let ⟨sexp, sexpP⟩ ← .asSexp "Arg" v
  match ← .asSymbolString "Arg kind" sexp[0] with
  | "op" =>
    let ⟨p⟩ ← .checkArgCount "op" sexp 2
    .op <$> Strata.OperationF.fromIon sexp[1]
  | "expr" =>
    let ⟨p⟩ ← .checkArgCount "expr" sexp 2
    .expr <$> Strata.ExprF.fromIon sexp[1]
  | "cat" =>
    let ⟨p⟩ ← .checkArgCount "cat" sexp 2
    .cat <$> fromIon sexp[1]
  | "type" =>
    let ⟨p⟩ ← .checkArgCount "type" sexp 2
    .type <$> fromIon sexp[1]
  | "ident" =>
    let ⟨p⟩ ← .checkArgCount "ident" sexp 3
    .ident <$> fromIon sexp[1]
           <*> .asString "Identifier value" sexp[2]
  | "num" =>
    let ⟨p⟩ ← .checkArgCount "num" sexp 3
    let ann ← fromIon sexp[1]
    let some x := sexp[2].asNat?
      | throw s!"Arg num given {repr sexp}."
    pure <| .num ann x
  | "decimal" =>
    let ⟨p⟩ ← .checkArgCount "num" sexp 3
    let ann ← fromIon sexp[1]
    let some d := sexp[2].asDecimal?
      | throw "decimal arg expects a decimal number."
    pure <| .decimal ann d
  | "strlit" =>
    let ⟨p⟩ ← .checkArgCount "strlit" sexp 3
    .strlit <$> fromIon sexp[1]
            <*> .asString "String literal value" sexp[2]
  | "bytes" =>
    let ⟨p⟩ ← .checkArgCount "bytes" sexp 3
    .bytes <$> fromIon sexp[1]
            <*> .asBytes "byte literal" sexp[2]
  | "option" =>
    let ⟨p⟩ ← .checkArgMin "option" sexp 2
    let ann ← fromIon sexp[1]
    let v ←
      match p : sexp.size with
      | 2 => pure none
      | 3 => some <$> Strata.ArgF.fromIon sexp[2]
      | _ => throw "Option expects at most one value."
    return .option ann v
  | "seq" => do
    let ⟨p⟩ ← .checkArgMin "seq" sexp 2
    let ann ← fromIon sexp[1]
    let args ← sexp.attach.mapM_off (start := 2) fun ⟨u, _⟩ =>
      Strata.ArgF.fromIon u
    return .seq ann args
  | "commaSepList" => do
    let ⟨p⟩ ← .checkArgMin "seq" sexp 2
    let ann ← fromIon sexp[1]
    let args ← sexp.attach.mapM_off (start := 2) fun ⟨u, _⟩ =>
      Strata.ArgF.fromIon u
    return .commaSepList ann args
  | str =>
    throw s!"Unexpected identifier {str}"
termination_by v
decreasing_by
  · have _ : sizeOf sexp[1] < sizeOf sexp := by decreasing_tactic
    decreasing_tactic
  · have _ : sizeOf sexp[1] < sizeOf sexp := by decreasing_tactic
    decreasing_tactic
  · have _ : sizeOf sexp[2] < sizeOf sexp := by decreasing_tactic
    decreasing_tactic
  · have _ : sizeOf u < sizeOf sexp := by decreasing_tactic
    decreasing_tactic
  · have _ : sizeOf u < sizeOf sexp := by decreasing_tactic
    decreasing_tactic

end

namespace OperationF

instance {α} [ToIon α] : CachedToIon (OperationF α)  where
  cachedToIon := OperationF.toIon

end OperationF

namespace SyntaxDefAtom

protected def toIon (refs : SymbolIdCache) (a : SyntaxDefAtom) : InternM (Ion SymbolId) :=
  ionScope! SyntaxDefAtom refs :
    match a with
    | .ident idx prec unwrap =>
      return .sexp #[ .symbol ionSymbol! "ident", .int idx, .int prec, .bool unwrap ]
    | .str v =>
      return .string v
    | .indent n args =>
      return .sexp <| #[.symbol ionSymbol! "indent", .int n]
          ++ (← args.attach.mapM (fun ⟨a, _⟩  => a.toIon refs))

instance : CachedToIon SyntaxDefAtom where
  cachedToIon := SyntaxDefAtom.toIon

protected def fromIon (v : Ion SymbolId) : FromIonM SyntaxDefAtom := do
  match ← .asSymbolOrSexp v with
  | .string v =>
    return .str v
  | .sexp args argsp =>
    match ← .asSymbolString "SyntaxDefAtom kind" args[0] with
    | "ident" => do
      -- Support both formats: 3 args (without unwrap) and 4 args (with unwrap spec)
      if args.size = 3 then
        let level ← .asNat "SyntaxDef ident level" args[1]!
        let prec ← .asNat "SyntaxDef ident prec" args[2]!
        return .ident level prec false
      else
        let ⟨p⟩ ← .checkArgCount "ident" args 4
        let level ← .asNat "SyntaxDef ident level" args[1]!
        let prec ← .asNat "SyntaxDef ident prec" args[2]!
        let unwrap ← match args[3]! with
          | .bool b => pure b
          | _ => throw "Expected boolean for unwrap"
        return .ident level prec unwrap
    | "indent" => do
      .indent <$> .asNat "SyntaxDef indent value" args[1]!
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
    let m := .fromList! ["atoms", "prec"]
    let ⟨args, p⟩ ← .asFieldStruct (size := 2) v "SyntaxDef" m
    pure {
        atoms := ← .asListOf "SyntaxDef atoms" args[0] fromIon,
        prec := ← .asNat "SyntaxDef prec" args[1],
    }

end SyntaxDef

namespace SourceRange

instance : ToIon SourceRange where
  toIon v :=
    pure <|
      if v.start = 0 ∧ v.stop = 0 then
        .null
      else
        .sexp #[.int v.start.byteIdx, .int v.stop.byteIdx ]

instance : FromIon SourceRange where
  fromIon v := do
    match v.app with
    | .null _ =>
      return .none
    | _ =>
      let ⟨exp, _⟩ ← .asSexp "Source rang" v
      let ⟨p⟩ ← .checkArgCount "Source range" exp 2
      return {
          start := ⟨← .asNat "Source range start" exp[0]⟩
          stop := ⟨← .asNat "Source range stop" exp[1]⟩
      }

end SourceRange

namespace MetadataArg

protected def toIon (refs : SymbolIdCache) (a : MetadataArg) : InternM (Ion SymbolId) :=
  ionScope! MetadataArg refs :
    match a with
    | .bool b =>
      return .bool b
    | .catbvar idx =>
      return .sexp #[ionSymbol! "category", .int idx]
    | .num v =>
      return .int v
    | .option ma =>
      match ma with
      | some a => return .sexp #[ionSymbol! "some", ← a.toIon refs]
      | none => return .null

instance : CachedToIon MetadataArg where
  cachedToIon := MetadataArg.toIon

protected def fromIon (v : Ion SymbolId) : FromIonM MetadataArg := do
  if let .null _ := v then
    return .option none
  if let .bool b := v then
    return .bool b
  if let some i := v.asNat? then
    return .num i
  let ⟨args, argp⟩ ← .asSexp "MetadataArg" v
  match ← .asSymbolString "MetadataArg kind" args[0] with
  | "category" =>
    let ⟨p⟩ ← .checkArgCount "MetadataArg category" args 2
    .catbvar <$> .asNat "MetadataArg catbvar" args[1]
  | "some" => do
    let ⟨p⟩ ← .checkArgCount "some" args 2
    have _ : sizeOf args[1] < sizeOf args := by decreasing_tactic
    (.option ∘ some) <$> MetadataArg.fromIon args[1]
  | s => throw s!"Unexpected arg {s}"

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
    let ⟨args, argsp⟩ ← .asSexp "Metadata attribute" v
    return {
      ident := ← QualifiedIdent.fromIon "Metadata attribute name" args[0],
      args := ← args.mapM_off (start := 1) fromIon
    }

end MetadataAttr

namespace Metadata

instance : CachedToIon Metadata where
  cachedToIon refs md := ionScope! Metadata refs : ionRef! md.toArray

instance : FromIon Metadata where
  fromIon v := .ofArray <$> .asListOf "Metadata attributes" v fromIon

end Metadata

namespace PreType

protected def toIon (refs : SymbolIdCache) (tpe : PreType) : InternM (Ion SymbolId) :=
  ionScope! PreType refs :
    match tpe with
    | .ident loc name a => do
      let args : Array (Ion SymbolId) := #[ionSymbol! "ident", ← toIon loc, ← name.toIon]
      .sexp <$> a.attach.mapM_off (init := args) fun ⟨e, _⟩ => e.toIon refs
    -- A bound type variable with the given index.
    | .bvar loc vidx =>
      return Ion.sexp #[ionSymbol! "bvar", ← toIon loc, .int vidx]
    | .fvar loc idx a => do
      let s : Array (Ion SymbolId) := #[ionSymbol! "fvar", ← toIon loc, .int idx]
      let s ← a.attach.mapM_off (init := s) fun ⟨e, _⟩ => e.toIon refs
      return Ion.sexp s
    | .arrow loc l r => do
      return Ion.sexp #[ionSymbol! "arrow", ← toIon loc, ← l.toIon refs, ← r.toIon refs]
    | .funMacro loc i r =>
      return Ion.sexp <| #[ionSymbol! "funMacro", ← toIon loc, .int i, ← r.toIon refs]
  termination_by tpe

instance : CachedToIon PreType where
  cachedToIon refs tp := tp.toIon refs

protected def fromIon (v : Ion SymbolId) : FromIonM PreType := do
  let ⟨args, ap⟩ ← .asSexp "PreType" v
  match ← .asSymbolString "PreType kind" args[0] with
  | "arrow" => do
    let ⟨p⟩ ← .checkArgCount "TypeExpr.arrow" args 4
    let ann ← fromIon args[1]
    let l ← PreType.fromIon args[2]
    let r ← PreType.fromIon args[3]
    return .arrow ann l r
  | "bvar" =>
    let ⟨p⟩ ← .checkArgCount "PreType bvar" args 3
    return PreType.bvar
      (← fromIon args[1])
      (← .asNat "TypeExpr bvar" args[2])
  | "fvar" =>
    let ⟨p⟩ ← .checkArgMin "fvar" args 3
    let ann ← fromIon args[1]
    let idx ← .asNat "fvar" args[2]
    let a ← args.attach.mapM_off (start := 3) fun ⟨e, _⟩ =>
      PreType.fromIon e
    pure <| .fvar ann idx a
  | "ident" =>
    let ⟨p⟩ ← .checkArgMin "ident" args 3
    let ann ← fromIon args[1]
    let name ← QualifiedIdent.fromIon "Pretype identifier" args[2]
    let args ← args.attach.mapM_off (start := 3) fun ⟨e, _⟩ =>
      PreType.fromIon e
    return .ident ann name args
  | "funMacro" =>
    let ⟨p⟩ ← .checkArgCount "PreType funMacro" args 4
    let ann ← fromIon args[1]
    let idx ← .asNat "funMacro idx" args[2]
    let res ← PreType.fromIon args[3]
    return .funMacro ann idx res
  | s => do
    throw s!"Unexpected PreType {s}"
termination_by v
  decreasing_by
    · have p : sizeOf args[2] < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have p : sizeOf args[3] < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have p : sizeOf e < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have p : sizeOf e < sizeOf args := by decreasing_tactic
      decreasing_tactic
    · have p : sizeOf args[3] < sizeOf args := by decreasing_tactic
      decreasing_tactic

instance : FromIon PreType where
  fromIon := PreType.fromIon

end PreType

namespace ArgDeclKind

instance : CachedToIon ArgDeclKind where
  cachedToIon refs tpc := ionScope! ArgDeclKind refs :
  match tpc with
  | .cat k =>
    return .sexp #[ionSymbol! "category", ← k.toIon]
  | .type tp =>
    return .sexp #[ionSymbol! "type", ← ionRef! tp]

protected def fromIon (v : Ion SymbolId) : FromIonM ArgDeclKind := do
  let ⟨args, argsp⟩ ← .asSexp "ArgDeclKind" v
  match ← .asSymbolString "ArgDeclKind kind" args[0] with
  | "category" => do
    let ⟨p⟩ ← .checkArgCount "category" args 2
    .cat <$> fromIon args[1]
  | "type" => do
    let ⟨p⟩ ← .checkArgCount "type" args 2
    .type <$> fromIon args[1]
  | s =>
    throw s!"Unexpected binding kind {s}"

instance : FromIon ArgDeclKind where
  fromIon := ArgDeclKind.fromIon

end ArgDeclKind

namespace ArgDecl

instance : CachedToIon ArgDecl where
  cachedToIon refs b := ionScope! ArgDecl refs : do
    let mut flds := #[
      (ionSymbol! "name", .string b.ident),
      (ionSymbol! "type", ←ionRef! b.kind),
    ]
    if !b.metadata.isEmpty then
      flds := flds.push (ionSymbol! "metadata", ← ionRef! b.metadata)
    return .struct flds

instance : FromIon ArgDecl where
  fromIon v := do
    let m := .fromOptList! [("name", .req), ("type", .req), ("metadata", .opt)]
    let ⟨fldArgs, p⟩ ← .asFieldStruct (size := 3) v "ArgDecl" m

    let metadata ←
          match fldArgs[2] with
          | .null _ => pure .empty
          | v => fromIon v
    pure {
        ident := ← .asString "ArgDecl.ident" fldArgs[0]
        kind := ← fromIon fldArgs[1]
        metadata := metadata
    }

end ArgDecl

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
    match ← .asSymbolString "MetadataArgType kind" args[0] with
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
    let ⟨args, argsp⟩ ← .asSexp "MetadataArgDecl" v
    let ⟨p⟩ ← .checkArgCount "MetadataArgDecl" args 2
    pure {
      ident := ← .asString "MetadataArgDecl identifier" args[0]
      type := ← fromIon args[1]
    }

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
    name := ← .asString "Category name" args[1],
    argNames := ← .asListOf "Category arguments" args[2] (.asString "Category argument name"),
  }

end SynCatDecl

namespace OpDecl

instance : CachedToIon OpDecl where
  cachedToIon refs d := ionScope! OpDecl refs : do
    let mut flds : Array (SymbolId × Ion SymbolId) := #[
      (ionSymbol! "type", ionSymbol! "op"),
      (ionSymbol! "name", .string d.name),
    ]
    if d.argDecls.size > 0 then
      let v ← d.argDecls.toArray.mapM (fun (de : ArgDecl) => ionRef! de)
      flds := flds.push (ionSymbol! "args", .list v)
    flds := flds.push (ionSymbol! "result", ← d.category.toIon)
    flds := flds.push (ionSymbol! "syntax",   ← ionRef! d.syntaxDef)
    if !d.metadata.isEmpty then
      flds := flds.push (ionSymbol! "metadata", ← ionRef! d.metadata)
    return .struct flds

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM OpDecl := do
  let m := .fromOptList! [
      ("type", .req),
      ("name", .req),
      ("args", .opt),
      ("result", .req),
      ("syntax", .opt),
      ("metadata", .opt)
    ]
  let fldArgs ← .mapFields fields m
  let name ← .asString "Op declaration name" fldArgs[1]
  let argDecls ←
        match fldArgs[2] with
        | .null _ => pure .empty
        | v => ArgDecls.ofArray <$> .asListOf "Op declaration arguments" v fromIon
  let category ← QualifiedIdent.fromIon "Op declaration result" fldArgs[3]
  let syntaxDef ←
        match fldArgs[4] with
        | .null _ => pure (.mkFunApp name argDecls.size)
        | v => fromIon v
  let metadata ←
        match fldArgs[5] with
        | .null _ => pure .empty
        | v => fromIon v
  pure {
    name := name
    argDecls := argDecls
    category := category
    syntaxDef := syntaxDef
    metadata := metadata
  }

end OpDecl

namespace TypeDecl

instance : CachedToIon TypeDecl where
  cachedToIon refs d := ionScope! TypeDecl refs : do
    let args ← d.argNames |>.mapM fun a =>
      return .sexp #[← toIon a.ann, .string a.val]
    return .struct #[
      (ionSymbol! "type", ionSymbol! "type"),
      (ionSymbol! "name", .string d.name),
      (ionSymbol! "argNames", .list args)
    ]

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM TypeDecl := do
  let m := .fromList! ["type", "name", "argNames"]
  let args ← .mapFields fields m
  let resolveArg v := do
        let ⟨argPair, _⟩ ← .asSexp "Header" v
        let ⟨eq⟩ ← .checkArgCount "TypeDecl.typenames" argPair 2
        pure {
          ann := ← fromIon argPair[0]
          val := ← .asString "TypeDecl value" argPair[1]
        }
  pure {
    name := ← .asString "TypeDecl name" args[1]
    argNames := ← .asListOf "TypeDecl arguments" args[2] resolveArg
  }

end TypeDecl

namespace FunctionDecl

instance : CachedToIon FunctionDecl where
  cachedToIon refs d := ionScope! FunctionDecl refs : do
    let mut flds : Array (SymbolId × Ion SymbolId) := #[
      (ionSymbol! "type", .symbol ionSymbol! "fn"),
      (ionSymbol! "name", .string d.name),
    ]
    if d.argDecls.size > 0 then
      let v ← d.argDecls.toArray.mapM (fun (de : ArgDecl) => ionRef! de)
      flds := flds.push (ionSymbol! "args", .list v)
    flds := flds.push (ionSymbol! "returns", ← ionRef! d.result)
    flds := flds.push (ionSymbol! "syntax", ← ionRef! d.syntaxDef)
    flds := flds.push (ionSymbol! "metadata", ← ionRef! d.metadata)
    return .struct flds

protected def fromIon (fields : Array (SymbolId × Ion SymbolId)) : FromIonM FunctionDecl := do
  let m := .fromOptList! [
      ("type", .req),
      ("name", .req),
      ("args", .opt),
      ("returns", .req),
      ("syntax", .opt),
      ("metadata", .opt)
    ]
  let fldArgs ← .mapFields fields m
  let name ← .asString "FunctionDecl.name" fldArgs[1]
  let argDecls ←
        match fldArgs[2] with
        | .null _ => pure .empty
        | .list a => ArgDecls.ofArray <$> Array.mapM fromIon a
        | r => throw s!"OpDecl.args expected a list."
  let returns ← fromIon fldArgs[3]
  let syntaxDef ←
        match fldArgs[4] with
        | .null _ => pure (.mkFunApp name argDecls.size)
        | v => fromIon v
  let metadata ←
        match fldArgs[5] with
        | .null _ => pure .empty
        | v => fromIon v
  pure {
    name := name
    argDecls := argDecls
    result := returns
    syntaxDef := syntaxDef
    metadata := metadata
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
    name := ← .asString "MetadataDecl name" args[1]
    args := ← .asListOf "MetadataDecl arguments" args[2] fromIon
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
  fromIonFields (← .asSymbolString "Decl kind" val) fields

end Decl

namespace Ion

/--
This contains information from a partially parsed Ion File.
-/
structure Fragment where
  symbols : Ion.SymbolTable
  values : Array (Ion.Ion Ion.SymbolId)
  offset : Nat

inductive Header
| dialect : DialectName → Header
| program : DialectName → Header

namespace Header

def fromIon (v : Ion SymbolId) : FromIonM Header := do
  let ⟨hdr, _⟩ ← .asSexp "Header" v
  let .isTrue ne := inferInstanceAs (Decidable (hdr.size ≥ 2))
    | throw s!"Expected header to have two elements."
  match ← .asSymbolString "Header kind" hdr[0] with
  | "dialect" => .dialect <$> .asString "Dialect name" hdr[1]
  | "program" => .program <$> .asString "Program name" hdr[1]
  | op => throw s!"Expected 'program' or 'dialect' instead of {op}."

def parse (bytes : ByteArray) : Except String (Header × Fragment) := do
  FromIonM.deserializeValue bytes $ fun v => do
    let tbl := (← read).symbols
    let ⟨args, _⟩ ← .asList v
    let .isTrue ne := inferInstanceAs (Decidable (args.size ≥ 1))
      | throw s!"Expected header"
    return (← fromIon args[0], { symbols := tbl, values := args, offset := 1 })

end Header

end Ion

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

def fromIonFragment (dialect : DialectName) (f : Ion.Fragment) : Except String Dialect := do
  let ctx : FromIonContext := ⟨f.symbols⟩
  let tbl := f.symbols
  let typeId := tbl.symbolId! "type"
  let nameId := tbl.symbolId! "name"
  let (imports, decls) ← f.values.foldlM (init := (#[], #[])) (start := f.offset) fun (imports, decls) v => do
    let fields ← FromIonM.asStruct0 v ⟨f.symbols⟩
    let some (_, val) := fields.find? (·.fst == typeId)
      | throw "Could not find type"
    match ← FromIonM.asSymbolString "Dialect kind" val ctx with
    | "import" =>
      let some (_, val) := fields.find? (·.fst == nameId)
        | throw "Could not find import"
      let i ← FromIonM.asString "Import name" val ctx
      pure (imports.push i, decls)
    | name =>
      let decl ← Decl.fromIonFields name fields ctx
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
    match ← Ion.Header.fromIon args[0] with
    | .dialect dialect => fun ctx =>
      (let f : Ion.Fragment := { symbols := ctx.symbols, values := args, offset := 1 }
      fromIonFragment dialect f)
    | .program _ =>
      throw s!"Expected dialect"

#declareIonSymbolTable Dialect

end Dialect

namespace Program

instance : CachedToIon Program where
  cachedToIon refs pgm :=
    ionScope! Program refs : do
      let hdr := Ion.sexp #[ ionSymbol! "program", .string pgm.dialect ]
      let l ← pgm.commands.mapM_off (init := #[hdr]) fun cmd => cmd.toIon (ionRefEntry! ``OperationF)
      return .list l

#declareIonSymbolTable Program

def fromIonFragmentCommands (f : Ion.Fragment) : Except String (Array Operation) := do
  let ctx : FromIonContext := ⟨f.symbols⟩
  f.values.foldlM (init := #[]) (start := f.offset) fun cmds u => do
    cmds.push <$> OperationF.fromIon u ctx

def fromIonFragment (f : Ion.Fragment)
      (dialects : DialectMap)
      (dialect : DialectName) : Except String Program :=
  return {
    dialects := dialects
    dialect := dialect
    commands := ← fromIonFragmentCommands f
  }

def fromIon (dialects : DialectMap) (dialect : DialectName) (bytes : ByteArray) : Except String Strata.Program := do
  let (hdr, frag) ←
    match Strata.Ion.Header.parse bytes with
    | .error msg =>
      throw msg
    | .ok p =>
      pure p
  match hdr with
  | .dialect _ =>
    throw "Expected a Strata program instead of a dialect."
  | .program name => do
    if name != dialect then
      throw s!"{name} program found when {dialect} expected."
    fromIonFragment frag dialects dialect

end Program
