/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Lean.Elab.Term.TermElabM
public import StrataDDM.Util.Ion
public import StrataDDM.Util.Decimal

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
- **Supported leaf types**: `Nat`, `Int`, `String`, `Bool`, `Float`, `Decimal`.
- **Container types**: `List α`, `Option α`.
- **Nested/recursive types** are supported. Recursive types require the
  enclosing definition to be marked `partial`.

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

def readFloat (v : Ion SymbolId) : Except Std.Format Float :=
  match v.app with
  | .float f => .ok f
  | .int i => .ok (Float.ofInt i)
  | _ => .error f!"Expected float, got {repr v}"

def readDecimal (v : Ion SymbolId) : Except Std.Format StrataDDM.Decimal :=
  match v.app with
  | .decimal d => .ok d
  | .int i => .ok (StrataDDM.Decimal.ofInt i)
  | _ => .error f!"Expected decimal, got {repr v}"

def readList (readElem : Ion SymbolId → SymbolTable → Except Std.Format α)
    (v : Ion SymbolId) (tbl : SymbolTable) : Except Std.Format (List α) := do
  let elems ← match v.app with
    | .list a => .ok a
    | .sexp a => .ok a
    | _ => .error f!"Expected list, got {repr v}"
  let mut result : List α := []
  for elem in elems.reverse do
    result := (← readElem elem tbl) :: result
  .ok result

def readOption (readElem : Ion SymbolId → SymbolTable → Except Std.Format α)
    (v : Ion SymbolId) (tbl : SymbolTable) : Except Std.Format (Option α) :=
  match v.app with
  | .null _ => .ok none
  | _ => (readElem v tbl).map some

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

/-- Leaf type names that should not be treated as nested inductives. -/
private meta def isLeafTypeName (name : Name) : Bool :=
  name == ``Nat || name == ``Int || name == ``String || name == ``Bool || name == ``Float ||
  name == ``StrataDDM.Decimal

/-- Check if a type name refers to a non-leaf inductive or structure in the environment. -/
private meta def isCompoundType (env : Environment) (name : Name) : Bool :=
  !isLeafTypeName name &&
    ((getStructureInfo? env name).isSome ||
      match env.find? name with | some (.inductInfo _) => true | _ => false)

/-- Canonical string key for a fully-applied type expression: "Name arg1 arg2 ...". -/
private meta partial def typeKey (t : Expr) : String :=
  let fn := t.getAppFn
  let args := t.getAppArgs
  let base := match fn.constName? with
    | some n => n.toString (escape := false)
    | none => "?"
  if args.isEmpty then base
  else s!"{base}[{",".intercalate (args.toList.map typeKey)}]"

/-- Generate a unique reader function name for a fully-applied type. -/
private meta def readerNameExpr (t : Expr) : Name :=
  Name.mkSimple s!"_ionRead_{(typeKey t).hash}"

/-- Legacy: reader name from a bare Name (no type args). -/
private meta def readerName (typeName : Name) : Name :=
  readerNameExpr (mkConst typeName)

/--
Generate a read expression for a value of the given type.
`valExpr` is the syntax for the Ion value to read.
Returns syntax of type `Except Std.Format T`.
-/
private meta partial def mkValueRead (fieldType : Expr) (valExpr : TSyntax `term) :
    TermElabM (TSyntax `term) := do
  let fieldType' ← whnf fieldType
  let name := fieldType'.getAppFn.constName?
  match name with
  | some ``Nat => `(Strata.Util.IonDeserializer.readNat $valExpr)
  | some ``Int => `(Strata.Util.IonDeserializer.readInt $valExpr)
  | some ``String => `(Strata.Util.IonDeserializer.readString $valExpr tbl)
  | some ``Bool => `(Strata.Util.IonDeserializer.readBool $valExpr)
  | some ``Float => `(Strata.Util.IonDeserializer.readFloat $valExpr)
  | some ``StrataDDM.Decimal => `(Strata.Util.IonDeserializer.readDecimal $valExpr)
  | some ``List =>
    let args := fieldType'.getAppArgs
    if h : args.size > 0 then
      let elemType := args[0]
      let elemReader ← mkValueRead elemType (← `(_elemVal))
      `(Strata.Util.IonDeserializer.readList (fun _elemVal tbl => $elemReader) $valExpr tbl)
    else throwError "getIonDeserializer%: List without type argument"
  | some ``Option =>
    let args := fieldType'.getAppArgs
    if h : args.size > 0 then
      let elemType := args[0]
      let elemReader ← mkValueRead elemType (← `(_elemVal))
      `(Strata.Util.IonDeserializer.readOption (fun _elemVal tbl => $elemReader) $valExpr tbl)
    else throwError "getIonDeserializer%: Option without type argument"
  | some n =>
    if isCompoundType (← getEnv) n then
      let readerId := mkIdent (readerNameExpr fieldType')
      `($readerId $valExpr tbl)
    else
      throwError "getIonDeserializer%: unsupported field type {fieldType'}"
  | _ => throwError "getIonDeserializer%: unsupported field type {fieldType'}"

/--
Generate a read expression for a field accessed via `lookupField` (struct context).
Supports leaf types and nested inductive/structure types.
-/
private meta def mkFieldRead (fieldType : Expr) (fieldNameLit : TSyntax `str) :
    TermElabM (TSyntax `term) := do
  let valExpr ← `(_fv)
  let readExpr ← mkValueRead fieldType valExpr
  `(Strata.Util.IonDeserializer.lookupField tbl fields $fieldNameLit >>= (fun _fv => $readExpr))

/--
Generate a read expression for a field accessed by index (sexp context).
Supports leaf types and nested inductive/structure types.
-/
private meta def mkIndexRead (fieldType : Expr) (idx : Nat) :
    TermElabM (TSyntax `term) := do
  let idxLit := quote idx
  let valExpr ← `(_iv)
  let readExpr ← mkValueRead fieldType valExpr
  `(if h : $(idxLit) < args.size
    then (fun _iv => $readExpr) args[$(idxLit)]
    else .error f!"Missing argument at index {$(idxLit)}")

private meta def getCtorFieldTypes (env : Environment) (ctorName : Name)
    (typeArgs : Array Expr := #[]) : TermElabM (Nat × Nat × Array Expr) := do
  let some (.ctorInfo ci) := env.find? ctorName
    | throwError "getIonDeserializer%: cannot find constructor {ctorName}"
  let mut ty := ci.type
  for i in List.range ci.numParams do
    match ty with
    | .forallE _ _ b _ =>
      let sub := if h : i < typeArgs.size then typeArgs[i] else mkSort levelZero
      ty := b.instantiate1 sub
    | _ => throwError "getIonDeserializer%: unexpected type shape"
  let mut result := #[]
  for _ in List.range ci.numFields do
    match ty with
    | .forallE _ t b _ =>
      result := result.push t
      ty := b.instantiate1 (mkSort levelZero)
    | _ => throwError "getIonDeserializer%: unexpected type shape"
  return (ci.numParams, ci.numFields, result)

/-- Generate the body of a reader for a struct type. -/
private meta def mkStructReaderBody (sinfo : StructureInfo) (typeArgs : Array Expr := #[]) :
    TermElabM (TSyntax `term) := do
  let env ← getEnv
  let fieldNames := sinfo.fieldNames
  let ctorName := sinfo.structName ++ `mk
  let (_, _, fieldTypes) ← getCtorFieldTypes env ctorName typeArgs
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
    let readExpr ← mkFieldRead fieldType fieldLit
    body ← `(Except.bind $readExpr (fun $localId => $body))
  `(Except.bind (Strata.Util.IonDeserializer.asStruct v) (fun fields => $body))

/-- Generate the body of a reader for a single-constructor inductive. -/
private meta def mkSingleCtorReaderBody (ctorName : Name) (typeArgs : Array Expr := #[]) :
    TermElabM (TSyntax `term) := do
  let (_, numFields, fieldTypes) ← getCtorFieldTypes (← getEnv) ctorName typeArgs
  let ctorId := mkIdent ctorName
  let mut ctorArgs : Array (TSyntax `term) := #[]
  for i in List.range numFields do
    ctorArgs := ctorArgs.push (← `($(mkIdent (Name.mkSimple s!"_f{i}"))))
  let mut body : TSyntax `term ← `(Except.ok ($ctorId $ctorArgs*))
  for i in (List.range numFields).reverse do
    let fieldLit := Syntax.mkStrLit s!"_{i}"
    let localId := mkIdent (Name.mkSimple s!"_f{i}")
    let readExpr ← mkFieldRead fieldTypes[i]! fieldLit
    body ← `(Except.bind $readExpr (fun $localId => $body))
  `(Except.bind (Strata.Util.IonDeserializer.asStruct v) (fun fields => $body))

/-- Generate the body of a reader for a multi-constructor inductive. -/
private meta def mkMultiCtorReaderBody (typeName : Name) (ctors : List Name)
    (typeArgs : Array Expr := #[]) :
    TermElabM (TSyntax `term) := do
  let env ← getEnv
  let typeNameStr := typeName.toString
  let mut body : TSyntax `term ←
    `(Except.error (f!"Unknown constructor for {$(Syntax.mkStrLit typeNameStr)}" : Std.Format))
  for ctorName in ctors.reverse do
    let shortName := ctorName.getString!
    let ctorId := mkIdent ctorName
    let (_, numFields, fieldTypes) ← getCtorFieldTypes env ctorName typeArgs
    let mut ctorArgs : Array (TSyntax `term) := #[]
    for i in List.range numFields do
      ctorArgs := ctorArgs.push (← `($(mkIdent (Name.mkSimple s!"_a{i}"))))
    let mut ctorBody : TSyntax `term ← `(Except.ok ($ctorId $ctorArgs*))
    for i in (List.range numFields).reverse do
      let localId := mkIdent (Name.mkSimple s!"_a{i}")
      let readExpr ← mkIndexRead fieldTypes[i]! (i + 1)
      ctorBody ← `(Except.bind $readExpr (fun $localId => $ctorBody))
    let patLit := Syntax.mkStrLit shortName
    body ← `(if tag == $patLit then $ctorBody else $body)
  `(Except.bind (Strata.Util.IonDeserializer.asSexp v) (fun args =>
      if h : args.size < 1 then
        Except.error (f!"Expected non-empty sexp" : Std.Format)
      else
        Except.bind
          (match args[0].app with
           | .symbol sym => Strata.Util.IonDeserializer.resolveSymbol tbl sym
           | .string s => Except.ok s
           | _ => Except.error (f!"Expected symbol or string tag" : Std.Format))
          (fun tag => $body)))

/-- Generate the body of a reader function for a given (possibly applied) type. -/
private meta def mkReaderBody (env : Environment) (typeExpr : Expr) :
    TermElabM (TSyntax `term) := do
  let typeName := typeExpr.getAppFn.constName?.getD Name.anonymous
  let typeArgs := typeExpr.getAppArgs
  if let some sinfo := getStructureInfo? env typeName then
    mkStructReaderBody sinfo typeArgs
  else
    let some (.inductInfo indInfo) := env.find? typeName
      | throwError "getIonDeserializer%: {typeName} is not an inductive or structure type"
    if indInfo.ctors.length == 1 then
      mkSingleCtorReaderBody indInfo.ctors.head! typeArgs
    else
      mkMultiCtorReaderBody typeName indInfo.ctors typeArgs

/-- Extract fully-applied compound type expressions from a field type, looking through List/Option. -/
private meta partial def extractCompoundExprs (env : Environment) (t : Expr) : TermElabM (Array Expr) := do
  let t ← whnf t
  let name := t.getAppFn.constName?
  match name with
  | some ``List | some ``Option =>
    let args := t.getAppArgs
    if h : args.size > 0 then extractCompoundExprs env args[0]
    else return #[]
  | some n =>
    if isCompoundType env n then
      -- Return the full applied type, and recurse into type arguments
      let mut result := #[t]
      for arg in t.getAppArgs do
        result := result ++ (← extractCompoundExprs env arg)
      return result
    else return #[]
  | none => return #[]

/-- Collect all nested fully-applied type expressions reachable from a type's fields. -/
private meta def collectNestedTypeExprs (env : Environment) (rootExpr : Expr) :
    TermElabM (Array Expr) := do
  let mut visited : Std.HashSet String := {}
  let mut queue : Array Expr := #[rootExpr]
  let mut result : Array Expr := #[]
  while h : queue.size > 0 do
    let typeExpr := queue[0]
    queue := queue.extract 1 queue.size
    let key := typeKey typeExpr
    if visited.contains key then continue
    visited := visited.insert key
    result := result.push typeExpr
    let typeName := typeExpr.getAppFn.constName?.getD Name.anonymous
    let typeArgs := typeExpr.getAppArgs
    let ctors := if let some sinfo := getStructureInfo? env typeName then
      [sinfo.structName ++ `mk]
    else match env.find? typeName with
      | some (.inductInfo indInfo) => indInfo.ctors
      | _ => []
    for ctorName in ctors do
      let some (.ctorInfo ci) := env.find? ctorName | continue
      let mut ty := ci.type
      for i in List.range ci.numParams do
        match ty with
        | .forallE _ _ b _ =>
          let sub := if h2 : i < typeArgs.size then typeArgs[i] else mkSort levelZero
          ty := b.instantiate1 sub
        | _ => break
      for _ in List.range ci.numFields do
        match ty with
        | .forallE _ t b _ =>
          for texpr in ← extractCompoundExprs env t do
            let tkey := typeKey texpr
            if !visited.contains tkey then queue := queue.push texpr
          ty := b.instantiate1 (mkSort levelZero)
        | _ => break
  return result

/-- Build a `let rec` term with multiple mutually-recursive bindings. -/
private meta def mkMutualLetRec (bindings : Array (Ident × TSyntax `term × TSyntax `term))
    (innerBody : TSyntax `term) : TermElabM (TSyntax `term) := do
  if bindings.isEmpty then return innerBody
  let termSuffix := mkNode ``Lean.Parser.Termination.suffix #[mkNullNode, mkNullNode]
  let mut declNodes : Array Syntax := #[]
  for (fnName, type, body) in bindings do
    let letIdDecl ← `(Lean.Parser.Term.letIdDecl| $fnName : $type := $body)
    let letDecl := mkNode ``Lean.Parser.Term.letDecl #[letIdDecl]
    let letRecDecl := mkNode ``Lean.Parser.Term.letRecDecl
      #[mkNullNode, mkNullNode, letDecl, termSuffix]
    declNodes := declNodes.push letRecDecl
  -- Build comma-separated array: [decl0, ",", decl1, ",", decl2, ...]
  let mut sepElems : Array Syntax := #[]
  for i in List.range declNodes.size do
    if i > 0 then sepElems := sepElems.push (mkAtom ",")
    sepElems := sepElems.push declNodes[i]!
  let sepArray := mkNullNode sepElems
  let letRecDecls := mkNode ``Lean.Parser.Term.letRecDecls #[sepArray]
  let letrec := mkNode ``Lean.Parser.Term.letrec
    #[mkNullNode, letRecDecls, mkNullNode, innerBody]
  return ⟨letrec⟩

/-- Convert a type Expr to syntax for use in type annotations. -/
private meta partial def exprToTypeSyntax (e : Expr) : TermElabM (TSyntax `term) := do
  let fn := e.getAppFn
  let args := e.getAppArgs
  if args.isEmpty then
    if let some n := fn.constName? then
      `($(mkIdent n))
    else
      `(_)
  else
    let fnStx ← exprToTypeSyntax fn
    let mut result := fnStx
    for arg in args do
      let argStx ← exprToTypeSyntax arg
      result ← `($result $argStx)
    return result

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
    let rootExpr := Lean.mkConst typeName
    let nestedTypes ← collectNestedTypeExprs env rootExpr
    if nestedTypes.size <= 1 then
      -- Simple case: no nested types, check for compound fields
      let mut hasCompoundFields := false
      let ctors := if let some sinfo := getStructureInfo? env typeName then
        [sinfo.structName ++ `mk]
      else match env.find? typeName with
        | some (.inductInfo indInfo) => indInfo.ctors
        | _ => []
      for ctorName in ctors do
        if let some (.ctorInfo ci) := env.find? ctorName then
          let mut ty := ci.type
          for _ in List.range ci.numParams do
            match ty with | .forallE _ _ b _ => ty := b.instantiate1 (mkSort levelZero) | _ => break
          for _ in List.range ci.numFields do
            match ty with
            | .forallE _ t b _ =>
              if let some n := t.getAppFn.constName? then
                if isCompoundType env n then hasCompoundFields := true
              ty := b.instantiate1 (mkSort levelZero)
            | _ => break
      if !hasCompoundFields then
        let readerBody ← mkReaderBody env rootExpr
        let resultStx ← `(Strata.Util.IonDeserializer.deserializeWith (fun v tbl => $readerBody))
        return ← elabTerm resultStx _expectedType?
    -- Nested/recursive types: generate a single mutual let rec block
    let rootReaderId := mkIdent (readerNameExpr rootExpr)
    let mut bindings : Array (Ident × TSyntax `term × TSyntax `term) := #[]
    for typeExpr in nestedTypes do
      let readerId := mkIdent (readerNameExpr typeExpr)
      let body ← mkReaderBody env typeExpr
      let typeStx ← exprToTypeSyntax typeExpr
      let readerType ← `(Ion SymbolId → SymbolTable → Except Std.Format $typeStx)
      let readerBody ← `(fun v tbl => $body)
      bindings := bindings.push (readerId, readerType, readerBody)
    let innerExpr ← `(Strata.Util.IonDeserializer.deserializeWith $rootReaderId)
    let finalExpr ← mkMutualLetRec bindings innerExpr
    elabTerm finalExpr _expectedType?
  | _ => throwUnsupportedSyntax

end
