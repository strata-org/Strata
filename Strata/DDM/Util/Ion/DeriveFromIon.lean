/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
This file provides a command for automatically generating `FromIon` instances
for structures and inductive types.

## Encoding Conventions

- **Structures**: Encoded as Ion structs with field names as keys
- **Inductives with single constructor**: Same as structures
- **Inductives with multiple constructors**: Ion s-expression with constructor name as first element

## Usage

```lean
import Strata.DDM.Util.Ion.DeriveFromIon

structure Point where
  x : Nat
  y : Nat

derive_FromIon Point
```
-/

module

public import Strata.DDM.Ion
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term.TermElabM

-- Non-meta section for instances
public section

namespace Strata.FromIon.Deriving

-- Basic instances for primitive types

instance : Strata.FromIon Nat where
  fromIon v := Strata.FromIonM.asNat "Nat" v

instance : Strata.FromIon Int where
  fromIon v := Strata.FromIonM.asInt v

instance : Strata.FromIon String where
  fromIon v := Strata.FromIonM.asString "String" v

instance : Strata.FromIon Bool where
  fromIon v := Strata.FromIonM.asBool "Bool" v

instance {α} [Strata.FromIon α] : Strata.FromIon (Array α) where
  fromIon v := Strata.FromIonM.asListOf "Array" v Strata.fromIon

instance {α} [Strata.FromIon α] : Strata.FromIon (List α) where
  fromIon v := Array.toList <$> Strata.FromIonM.asListOf "List" v Strata.fromIon

instance {α} [Strata.FromIon α] : Strata.FromIon (Option α) where
  fromIon v := do
    match v.app with
    | .null _ => pure none
    | _ => some <$> Strata.fromIon v

end Strata.FromIon.Deriving

end -- public section

-- Meta section for metaprogramming functions and command
public meta section

open Lean
open Lean.Meta
open Lean.Elab
open Lean.Elab.Command
open Lean.Elab.Term
open Lean.Elab.Deriving

namespace Strata.FromIon.Deriving

/-- Helper to get the last component of a name as a string -/
def getNameStr (n : Name) : String :=
  match n with
  | .str _ s => s
  | .num _ n => toString n
  | .anonymous => "anonymous"


/-- Generate the body for parsing a structure from an Ion struct -/
def mkFromIonBodyForStruct (typeName : Name) (ctorName : Name) (fieldNames : Array Name) : TermElabM (TSyntax `term) := do
  let ctorId := mkIdent ctorName
  let typeId := mkIdent typeName

  if fieldNames.isEmpty then
    `(pure $ctorId)
  else
    -- Build field assignments for the struct literal
    let fieldAssigns ← fieldNames.mapM fun fieldName => do
      let fieldId := mkIdent fieldName
      `(Lean.Parser.Term.structInstField| $fieldId:ident := $fieldId)

    -- Build the final struct construction
    let structLit ← `(({ $[$fieldAssigns:structInstField],* } : $typeId))

    -- Build the do-block with field parsing
    let mut doElems : Array (TSyntax `Lean.Parser.Term.doSeqItem) := #[]

    -- First element: parse the struct
    doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem| let fields ← Strata.FromIonM.asStruct0 v))

    -- Parse each field
    for fieldName in fieldNames do
      let fieldId := mkIdent fieldName
      let fieldNameStr := getNameStr fieldName
      doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem|
        let fieldVal ← Strata.FromIonM.getField fields $(quote fieldNameStr)))
      doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem|
        let $fieldId ← Strata.fromIon fieldVal))

    -- Final return
    doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem| pure $structLit))

    `(do $[$doElems]*)

/-- Generate the body for parsing an inductive with multiple constructors -/
def mkFromIonBodyForInduct (typeName : Name) (ctors : List Name) : TermElabM (TSyntax `term) := do
  let typeNameStr := getNameStr typeName

  -- Generate match alternatives for each constructor
  let mut alts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]

  for ctorName in ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let ctorNameStr := getNameStr ctorName
    let ctorId := mkIdent ctorName

    -- Get the number of fields (excluding type parameters)
    let numFields := ctorInfo.numFields

    if numFields == 0 then
      -- No fields: just return constructor
      let alt ← `(Lean.Parser.Term.matchAltExpr| | $(quote ctorNameStr) => pure $ctorId)
      alts := alts.push alt
    else
      -- Has fields: parse from sexp arguments
      let mut argIds : Array Ident := #[]
      for i in List.range numFields do
        argIds := argIds.push (mkIdent (Name.mkSimple s!"arg{i}"))

      -- Build constructor application
      let ctorApp ← argIds.foldlM (init := (ctorId : TSyntax `term)) fun acc arg =>
        `($acc $arg)

      -- Build the do-block for parsing
      let mut doElems : Array (TSyntax `Lean.Parser.Term.doSeqItem) := #[]

      -- Check argument count
      doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem|
        let ⟨_⟩ ← Strata.FromIonM.checkArgCount $(quote ctorNameStr) args $(quote (numFields + 1))))

      -- Parse each field
      for i in List.range numFields do
        let argId := argIds[i]!
        doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem|
          let $argId ← Strata.fromIon args[$(quote (i + 1))]!))

      -- Return the constructor
      doElems := doElems.push (← `(Lean.Parser.Term.doSeqItem| pure $ctorApp))

      let parseBody ← `(do $[$doElems]*)
      let alt ← `(Lean.Parser.Term.matchAltExpr| | $(quote ctorNameStr) => $parseBody)
      alts := alts.push alt

  -- Add catch-all for unknown constructors
  let catchAll ← `(Lean.Parser.Term.matchAltExpr| | other => throw s!"Unknown constructor for {$(quote typeNameStr)}: {other}")
  alts := alts.push catchAll

  -- Generate the full body
  `(do
    let ⟨args, _⟩ ← Strata.FromIonM.asSexpOrList $(quote typeNameStr) v
    if h : args.size > 0 then
      let tag ← Strata.FromIonM.asSymbolString "constructor tag" args[0]
      match tag with
        $[$alts:matchAlt]*
    else
      throw s!"Expected non-empty sexp for {$(quote typeNameStr)}")


/-- Generate the full FromIon instance declaration -/
def mkFromIonInstance (declName : Name) : TermElabM (Array Command) := do
  let env ← getEnv

  -- Check if it's a structure
  let isStruct := isStructure env declName

  let body ← if isStruct then
    let fieldNames := getStructureFields env declName
    let ctorVal := getStructureCtor env declName
    mkFromIonBodyForStruct declName ctorVal.name fieldNames
  else
    let indVal ← getConstInfoInduct declName
    if indVal.ctors.length == 1 then
      -- Single constructor: treat like struct
      let ctorName := indVal.ctors[0]!
      let ctorInfo ← getConstInfoCtor ctorName

      -- Get field names from constructor
      let ctorType := ctorInfo.type
      let (fieldNames, _) ← forallTelescopeReducing ctorType fun args _ => do
        let names ← args.toList.drop indVal.numParams |>.mapM fun arg => do
          let localDecl ← arg.fvarId!.getDecl
          pure localDecl.userName
        pure (names.toArray, args.size - indVal.numParams)

      mkFromIonBodyForStruct declName ctorName fieldNames
    else
      -- Multiple constructors
      mkFromIonBodyForInduct declName indVal.ctors

  let declId := mkIdent declName

  let cmd ← `(
    instance : Strata.FromIon $declId where
      fromIon v := $body
  )

  return #[cmd]

end Strata.FromIon.Deriving

/-- Derive a FromIon instance for the given type. Use as: `derive_FromIon TypeName` -/
elab "derive_FromIon " t:ident : command => do
  let name ← liftTermElabM <| resolveGlobalConstNoOverload t
  let cmds ← liftTermElabM <| Strata.FromIon.Deriving.mkFromIonInstance name
  for cmd in cmds do
    elabCommand cmd

end -- public meta section
