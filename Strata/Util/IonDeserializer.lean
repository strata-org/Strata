/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public import Strata.DDM.Util.Ion

open Lean Meta Elab Term
open Ion

/-!
# Generic Ion Deserializer

`getIonDeserializer%` is a term-level elaborator that, at compile time,
inspects a Lean inductive or structure type and generates a function
`ByteArray → Except Std.Format α` that deserializes Ion binary data into
values of that type.

## Ion encoding conventions

- **Structures** are encoded as Ion structs whose keys match the Lean field
  names.
- **Single-constructor inductives** are encoded as Ion structs with positional
  field names `_0`, `_1`, …
- **Multi-constructor inductives** are encoded as Ion s-expressions
  `(ConstructorName arg₁ arg₂ …)`.
- **Supported leaf types**: `Nat`, `Int`, `String`, `Bool`.

## Usage

```lean
def myDeserializer : ByteArray → Except Std.Format MyType :=
  getIonDeserializer% MyType
```
-/

public section

namespace Strata.Util.IonDeserializer

def readNat (v : Ion SymbolId) : Except Std.Format Nat :=
  match v.app with
  | .int i => if i ≥ 0 then .ok i.toNat else .error f!"Expected non-negative int, got {repr v}"
  | _ => .error f!"Expected int for Nat, got {repr v}"

def readInt (v : Ion SymbolId) : Except Std.Format Int :=
  match v.app with
  | .int i => .ok i
  | _ => .error f!"Expected int, got {repr v}"

def readString (v : Ion SymbolId) (tbl : SymbolTable) : Except Std.Format String :=
  match v.app with
  | .string s => .ok s
  | .symbol sym => match tbl[sym]? with
    | some s => .ok s
    | none => .error f!"Unknown symbol id {sym.value}"
  | _ => .error f!"Expected string, got {repr v}"

def readBool (v : Ion SymbolId) : Except Std.Format Bool :=
  match v.app with
  | .bool b => .ok b
  | _ => .error f!"Expected bool, got {repr v}"

def resolveSymbol (tbl : SymbolTable) (sym : SymbolId) : Except Std.Format String :=
  match tbl[sym]? with
  | some s => .ok s
  | none => .error f!"Unknown symbol id {sym.value}"

def lookupField (tbl : SymbolTable) (fields : Array (SymbolId × Ion SymbolId))
    (name : String) : Except Std.Format (Ion SymbolId) := do
  for (sym, val) in fields do
    match tbl[sym]? with
    | some s => if s == name then return val
    | none => pure ()
  .error f!"Missing field '{name}'"

def asStruct (v : Ion SymbolId) : Except Std.Format (Array (SymbolId × Ion SymbolId)) :=
  match v.app with
  | .struct fields => .ok fields
  | _ => .error f!"Expected struct, got {repr v}"

def asSexp (v : Ion SymbolId) : Except Std.Format (Array (Ion SymbolId)) :=
  match v.app with
  | .sexp args => .ok args
  | .list args => .ok args
  | _ => .error f!"Expected sexp, got {repr v}"

def deserializeWith {α : Type} (f : Ion SymbolId → SymbolTable → Except Std.Format α)
    (bs : ByteArray) : Except Std.Format α := do
  let entries ← match Ion.deserialize bs with
    | .error (off, msg) => .error f!"Ion parse error at offset {off}: {msg}"
    | .ok a => .ok a
  if h : entries.size = 1 then
    let entry := entries[0]
    if h2 : entry.size = 2 then
      let tbl ← match SymbolTable.ofLocalSymbolTable entry[0] with
        | .error (_, msg) => .error f!"Symbol table error: {msg}"
        | .ok tbl => .ok tbl
      f entry[1] tbl
    else
      .error f!"Expected symbol table and value, got {entry.size} elements"
  else
    .error f!"Expected single Ion top-level value, got {entries.size}"

end Strata.Util.IonDeserializer
end -- public section

private meta def mkLeafRead (fieldType : Expr) (fieldNameLit : TSyntax `str) :
    TermElabM (TSyntax `term) := do
  let fieldType ← whnf fieldType
  match fieldType.getAppFn.constName? with
  | some ``Nat =>
    `(Strata.Util.IonDeserializer.lookupField tbl fields $fieldNameLit >>=
      Strata.Util.IonDeserializer.readNat)
  | some ``Int =>
    `(Strata.Util.IonDeserializer.lookupField tbl fields $fieldNameLit >>=
      Strata.Util.IonDeserializer.readInt)
  | some ``String =>
    `(Strata.Util.IonDeserializer.lookupField tbl fields $fieldNameLit >>=
      (Strata.Util.IonDeserializer.readString · tbl))
  | some ``Bool =>
    `(Strata.Util.IonDeserializer.lookupField tbl fields $fieldNameLit >>=
      Strata.Util.IonDeserializer.readBool)
  | _ => throwError "getIonDeserializer%: unsupported field type {fieldType}"

private meta def mkLeafReadDirect (fieldType : Expr) (idx : Nat) :
    TermElabM (TSyntax `term) := do
  let fieldType ← whnf fieldType
  let idxLit := quote idx
  match fieldType.getAppFn.constName? with
  | some ``Nat =>
    `(if h : $(idxLit) < args.size
      then Strata.Util.IonDeserializer.readNat args[$(idxLit)]
      else .error f!"Missing argument at index {$(idxLit)}")
  | some ``Int =>
    `(if h : $(idxLit) < args.size
      then Strata.Util.IonDeserializer.readInt args[$(idxLit)]
      else .error f!"Missing argument at index {$(idxLit)}")
  | some ``String =>
    `(if h : $(idxLit) < args.size
      then Strata.Util.IonDeserializer.readString args[$(idxLit)] tbl
      else .error f!"Missing argument at index {$(idxLit)}")
  | some ``Bool =>
    `(if h : $(idxLit) < args.size
      then Strata.Util.IonDeserializer.readBool args[$(idxLit)]
      else .error f!"Missing argument at index {$(idxLit)}")
  | _ => throwError "getIonDeserializer%: unsupported field type {fieldType}"

private meta def getCtorFieldTypes (env : Environment) (ctorName : Name) :
    TermElabM (Nat × Nat × Array Expr) := do
  let some (.ctorInfo ci) := env.find? ctorName
    | throwError "getIonDeserializer%: cannot find constructor {ctorName}"
  let mut ty := ci.type
  for _ in List.range ci.numParams do
    match ty with
    | .forallE _ _ b _ => ty := b
    | _ => throwError "getIonDeserializer%: unexpected type shape"
  let mut result := #[]
  for _ in List.range ci.numFields do
    match ty with
    | .forallE _ t b _ =>
      result := result.push t
      ty := b
    | _ => throwError "getIonDeserializer%: unexpected type shape"
  return (ci.numParams, ci.numFields, result)

private meta def mkStructReader (sinfo : StructureInfo) :
    TermElabM (TSyntax `term) := do
  let env ← getEnv
  let fieldNames := sinfo.fieldNames
  let ctorName := sinfo.structName ++ `mk
  let (_, _, fieldTypes) ← getCtorFieldTypes env ctorName
  let ctorId := mkIdent ctorName
  let mut ctorArgs : Array (TSyntax `term) := #[]
  for fieldName in fieldNames do
    ctorArgs := ctorArgs.push (← `($(mkIdent fieldName)))
  let mut body : TSyntax `term ← `(Except.ok ($ctorId $ctorArgs*))
  for i in (List.range fieldNames.size).reverse do
    let fieldName := fieldNames[i]!
    let fieldStr := fieldName.toString (escape := false)
    let fieldLit := Syntax.mkStrLit fieldStr
    let fieldType := fieldTypes[i]!
    let localId := mkIdent fieldName
    let readExpr ← mkLeafRead fieldType fieldLit
    body ← `(Except.bind $readExpr (fun $localId => $body))
  body ← `(Except.bind (Strata.Util.IonDeserializer.asStruct v) (fun fields => $body))
  `(fun v tbl => $body)

private meta def mkSingleCtorReader (ctorName : Name) :
    TermElabM (TSyntax `term) := do
  let (_, numFields, fieldTypes) ← getCtorFieldTypes (← getEnv) ctorName
  let ctorId := mkIdent ctorName
  let mut ctorArgs : Array (TSyntax `term) := #[]
  for i in List.range numFields do
    ctorArgs := ctorArgs.push (← `($(mkIdent (Name.mkSimple s!"_f{i}"))))
  let mut body : TSyntax `term ← `(Except.ok ($ctorId $ctorArgs*))
  for i in (List.range numFields).reverse do
    let fieldLit := Syntax.mkStrLit s!"_{i}"
    let localId := mkIdent (Name.mkSimple s!"_f{i}")
    let readExpr ← mkLeafRead fieldTypes[i]! fieldLit
    body ← `(Except.bind $readExpr (fun $localId => $body))
  body ← `(Except.bind (Strata.Util.IonDeserializer.asStruct v) (fun fields => $body))
  `(fun v tbl => $body)

private meta def mkMultiCtorReader (typeName : Name) (ctors : List Name) :
    TermElabM (TSyntax `term) := do
  let env ← getEnv
  let typeNameStr := typeName.toString
  let mut body : TSyntax `term ←
    `(Except.error (f!"Unknown constructor for {$(Syntax.mkStrLit typeNameStr)}" : Std.Format))
  for ctorName in ctors.reverse do
    let shortName := ctorName.getString!
    let ctorId := mkIdent ctorName
    let (_, numFields, fieldTypes) ← getCtorFieldTypes env ctorName
    let mut ctorArgs : Array (TSyntax `term) := #[]
    for i in List.range numFields do
      ctorArgs := ctorArgs.push (← `($(mkIdent (Name.mkSimple s!"_a{i}"))))
    let mut ctorBody : TSyntax `term ← `(Except.ok ($ctorId $ctorArgs*))
    for i in (List.range numFields).reverse do
      let localId := mkIdent (Name.mkSimple s!"_a{i}")
      let readExpr ← mkLeafReadDirect fieldTypes[i]! (i + 1)
      ctorBody ← `(Except.bind $readExpr (fun $localId => $ctorBody))
    let patLit := Syntax.mkStrLit shortName
    body ← `(if tag == $patLit then $ctorBody else $body)
  body ← `(
    Except.bind (Strata.Util.IonDeserializer.asSexp v) (fun args =>
      if h : args.size < 1 then
        Except.error (f!"Expected non-empty sexp" : Std.Format)
      else
        Except.bind
          (match args[0].app with
           | .symbol sym => Strata.Util.IonDeserializer.resolveSymbol tbl sym
           | .string s => Except.ok s
           | _ => Except.error (f!"Expected symbol or string tag" : Std.Format))
          (fun tag => $body)))
  `(fun v tbl => $body)

private meta def mkReaderSyntax (env : Environment) (typeName : Name) :
    TermElabM (TSyntax `term) := do
  if let some sinfo := getStructureInfo? env typeName then
    mkStructReader sinfo
  else
    let some (.inductInfo indInfo) := env.find? typeName
      | throwError "getIonDeserializer%: {typeName} is not an inductive or structure type"
    if indInfo.ctors.length == 1 then
      mkSingleCtorReader indInfo.ctors.head!
    else
      mkMultiCtorReader typeName indInfo.ctors

public section

/--
`getIonDeserializer%` generates an Ion deserializer for the given type.
The result has type `ByteArray → Except Std.Format T`.

Usage: `getIonDeserializer% MyType`
-/
syntax (name := getIonDeserializerStx) "getIonDeserializer%" ident : term

@[term_elab getIonDeserializerStx]
meta def getIonDeserializerElab : TermElab := fun stx _expectedType? => do
  match stx with
  | `(getIonDeserializer% $typeId) => do
    let typeName ← resolveGlobalConstNoOverload typeId
    let env ← getEnv
    let readerStx ← mkReaderSyntax env typeName
    let resultStx ← `(Strata.Util.IonDeserializer.deserializeWith $readerStx)
    elabTerm resultStx _expectedType?
  | _ => throwUnsupportedSyntax

end
