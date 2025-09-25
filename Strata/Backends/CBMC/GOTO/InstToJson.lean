/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Program
import Strata.Backends.CBMC.Common

namespace CProverGOTO
open Lean
open Strata.CBMC

-------------------------------------------------------------------------------

/--
Convert SourceLocation to JSON.

NOTE: CBMC's `--show-goto-functions` renders source location using the named
field `sourceLocation`, which is different from `#source_location` rendered by
`--show-symbol-table`.
-/
def sourceLocationToJson (loc : SourceLocation) : String × Json :=
  ("sourceLocation",
  if loc == .nil then Json.mkObj [] else
  Json.mkObj [
    ("file", Json.str loc.file),
    ("function", Json.str loc.function),
    ("line", Json.str (toString loc.line)),
    ("workingDirectory", Json.str loc.workingDir),
    ("comment", Json.str loc.comment),
  ])

def mkSymbolWithSourceLocation (identifier : String) (symbolType : Json) (loc : SourceLocation) : Json :=
  let loc_obj := sourceLocationToJson loc
  Json.mkObj [
    ("id", "symbol"),
    ("namedSub", Json.mkObj [
      ("identifier", Json.mkObj [("id", identifier)]),
      ("type", symbolType)
    ]),
    loc_obj
  ]

/-- Convert `Ty` to JSON format -/
def tyToJson (ty : Ty) : Json :=
  match ty with
  | .Boolean => boolType
  | .Integer => integerType
  | .String => stringType
  | .Empty => emptyType
  | .SignedBV width => mkSignedBVType width
  | .UnsignedBV width => mkUnsignedBVType width
  | _ => Json.mkObj [("id", "unknown")]

/-- Convert `Expr` to JSON format -/
partial def exprToJson (expr : Expr) : Json :=
  let srcField := sourceLocationToJson expr.sourceLoc
  let exprObj := match expr.id with
    | .nullary (.symbol name) => mkSymbolWithSourceLocation name (tyToJson expr.type) expr.sourceLoc
    | .nullary (.constant value) =>
      let value := match expr.type with
        -- (FIXME) Looks like CBMC's JSON form expects Hex values?
        | .SignedBV 32 => i32ToHex value
        | .UnsignedBV 32 => i32ToHex value
        | _ => value
      Json.mkObj [
        ("id", "constant"),
        ("namedSub", Json.mkObj [
          ("type", tyToJson expr.type),
          ("value", Json.mkObj [("id", value)])
        ]),
        srcField
      ]
    | .nullary (.nondet name) =>
      Json.mkObj [
        ("id", "nondet"),
        ("namedSub", Json.mkObj [
          ("identifier", Json.mkObj [("id", name)]),
          ("type", tyToJson expr.type)
        ]),
        srcField
      ]
    | .unary op =>
      let op_str := toString f!"{op}"
      Json.mkObj [
        ("id", op_str),
        ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray),
        srcField
      ]
    | .binary op =>
      let op_str := toString f!"{op}"
      Json.mkObj [
        ("id", op_str),
        ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray),
        srcField
      ]
    | .multiary op =>
      let op_str := toString f!"{op}"
      Json.mkObj [
        ("id", op_str),
        ("namedSub", Json.mkObj [("type", tyToJson expr.type)]),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray),
        srcField
      ]
    | .side_effect effect =>
      let effect_str := toString f!"{effect}"
      Json.mkObj [
        ("id", "side_effect"),
        ("namedSub", Json.mkObj [
          ("statement", Json.mkObj [("id", effect_str)]),
          ("type", tyToJson expr.type)
        ]),
        ("sub", Json.arr (expr.operands.map exprToJson).toArray),
        srcField
      ]
    | _ => panic s!"[exprToJson] Unsupported expr: {format expr}"
  exprObj

/-- Convert `Code` to Json -/
def codeToJson (code : Code) : Json :=
  let namedSub := ("namedSub",
        (Json.mkObj [
              ("statement", Json.mkObj [("id", s!"{format code.id}")]),
              ("type", Json.mkObj [("id", "empty")])]))
  let sourceField := sourceLocationToJson code.sourceLoc
  let sub := ("sub", Json.arr (code.operands.map exprToJson).toArray)
  let obj := Json.mkObj ([("id", Json.str "code"), namedSub, sub, sourceField])
  obj

/--
Generate instruction string for display-/
def instructionToString (inst : Instruction) : String :=
  let comment := s!"        // {inst.locationNum} file {inst.sourceLoc.file} line {inst.sourceLoc.line} function {inst.sourceLoc.function}\n"
  let instrStr := match inst.type with
    | .ASSUME => s!"        {inst.type} {format inst.guard}\n"
    | .ASSERT => s!"        {inst.type} {format inst.guard}\n"
    | _ => s!"        {inst.type} {format inst.code}\n"
  comment ++ instrStr

/-- Main function to convert `Instruction` to JSON -/
def instructionToJson (inst : Instruction) : Json :=
  let baseFields := [
    ("instruction", Json.str (instructionToString inst)),
    ("instructionId", Json.str (toString inst.type)),
    ("locationNumber", Json.num inst.locationNum.toNat)
  ]
  let guardField := if Expr.beq inst.guard Expr.true then [] else [("guard", exprToJson inst.guard)]
  let codeField := if inst.code == Code.skip then [] else [("code", codeToJson inst.code)]
  let sourceField :=  [sourceLocationToJson inst.sourceLoc]
  Json.mkObj (baseFields ++ guardField ++ codeField ++ sourceField)

def programToJson (name : String) (program : Program) : Json :=
  let body :=
      Json.mkObj [
        ("instructions", Json.arr (program.instructions.map instructionToJson)),
        ("parameterIdentifiers", Json.arr (program.parameterIdentifiers.map toJson)),
        ("isBodyAvailable", program.isBodyAvailable),
        ("isInternal", program.isInternal),
        ("name", name)
      ]
  body

/-- Write a program to JSON file -/
def writeProgramToFile (fileName : String) (programName : String) (program : Program) : IO Unit := do
  let json := programToJson programName program
  IO.FS.writeFile fileName json.pretty

/-- Convert `Program`s to JSON containing GOTO functions -/
def programsToJson (programs : List (String × Program)) : Json :=
  let instructions := Json.arr (programs.map (fun (n, p) => programToJson n p)).toArray
  let functions := Json.mkObj [("functions", instructions)]
  functions

/-- Write programs to JSON file -/
def writeProgramsToFile (fileName : String) (programs : List (String × Program)) : IO Unit := do
  let json := programsToJson programs
  IO.FS.writeFile fileName json.pretty

-------------------------------------------------------------------------------
