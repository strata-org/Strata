/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Backends.CBMC.GOTO.InstToJson
public import Strata.Backends.CBMC.GOTO.LambdaToCProverGOTO
import Strata.DL.Lambda.TypeConstructor
import Strata.DL.Lambda.TypeFactory
public import Strata.Languages.Core.Program

namespace Strata

public section

private def datatypeToSymbolEntry (dt : Lambda.LDatatype Unit)
    (mutualNames : List String := [dt.name]) :
    Except Std.Format (String × CProverGOTO.CBMCSymbol) := do
  let mut components : Array (String × Lean.Json) :=
    #[("$tag", CProverGOTO.tyToJson .Integer)]
  for constr in dt.constrs do
    for (fieldId, fieldTy) in constr.args do
      let gty ← Lambda.LMonoTy.toGotoType fieldTy
      let tyJson := CProverGOTO.tyToJson gty
      -- Recursive fields (type refers to any datatype in the mutual block) must be pointers
      let tyJson := match fieldTy with
        | .tcons name _ =>
          if mutualNames.contains name then
            Lean.Json.mkObj [
              ("id", "pointer"),
              ("sub", Lean.Json.arr #[tyJson]),
              ("namedSub", Lean.Json.mkObj [("width", Lean.Json.mkObj [("id", "64")])])
            ]
          else tyJson
        | _ => tyJson
      components := components.push (fieldId.name, tyJson)
  let componentsSub := components.map fun (name, tyJson) =>
    Lean.Json.mkObj [
      ("id", ""),
      ("namedSub", Lean.Json.mkObj [
        ("#pretty_name", Lean.Json.mkObj [("id", name)]),
        ("name", Lean.Json.mkObj [("id", name)]),
        ("type", tyJson)
      ])
    ]
  let structTy := Lean.Json.mkObj [
    ("id", "struct"),
    ("namedSub", Lean.Json.mkObj [
      ("tag", Lean.Json.mkObj [("id", dt.name)]),
      ("components", Lean.Json.mkObj [
        ("id", ""),
        ("sub", Lean.Json.arr componentsSub)
      ])
    ])
  ]
  return (s!"tag-{dt.name}", {
    baseName := dt.name
    isType := true
    mode := "C"
    module := ""
    name := s!"tag-{dt.name}"
    prettyName := s!"struct {dt.name}"
    type := structTy
    value := Lean.Json.mkObj [("id", "nil")]
  })

private def typeConstructorToSymbolEntry (tc : TypeConstructor) :
    String × CProverGOTO.CBMCSymbol :=
  -- CBMC requires structs to have at least one component.
  -- Abstract type constructors have no fields, so add a dummy padding field.
  let dummyComponent := Lean.Json.mkObj [
    ("id", ""),
    ("namedSub", Lean.Json.mkObj [
      ("#pretty_name", Lean.Json.mkObj [("id", "__padding")]),
      ("name", Lean.Json.mkObj [("id", "__padding")]),
      ("type", Lean.Json.mkObj [("id", "bool")])
    ])
  ]
  let structTy := Lean.Json.mkObj [
    ("id", "struct"),
    ("namedSub", Lean.Json.mkObj [
      ("tag", Lean.Json.mkObj [("id", tc.name)]),
      ("components", Lean.Json.mkObj [
        ("id", ""),
        ("sub", Lean.Json.arr #[dummyComponent])
      ])
    ])
  ]
  (s!"tag-{tc.name}", {
    baseName := tc.name
    isType := true
    mode := "C"
    module := ""
    name := s!"tag-{tc.name}"
    prettyName := s!"struct {tc.name}"
    type := structTy
    value := Lean.Json.mkObj [("id", "nil")]
  })


private def collectDatatypeSymbols (pgm : Core.Program) :
    Except Std.Format (Map String CProverGOTO.CBMCSymbol) := do
  let mut syms : List (String × CProverGOTO.CBMCSymbol) := []
  for decl in pgm.decls do
    match decl with
    | .type (.data dts) _ =>
      let mutualNames := dts.map (·.name)
      for dt in dts do
        if dt.typeArgs.isEmpty then
          let entry ← datatypeToSymbolEntry dt mutualNames
          syms := syms ++ [entry]
    | .type (.con tc) _ =>
      if tc.numargs == 0 then
        syms := syms ++ [typeConstructorToSymbolEntry tc]
    | _ => pure ()
  return syms

/-- Collect all extra symbol table entries (datatypes, type constructors). -/
def collectExtraSymbols (pgm : Core.Program) :
    Except Std.Format (Map String CProverGOTO.CBMCSymbol) := do
  collectDatatypeSymbols pgm

end -- public section

end Strata
